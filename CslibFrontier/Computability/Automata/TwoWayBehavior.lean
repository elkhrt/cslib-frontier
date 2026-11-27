module

public import CslibFrontier.Computability.Automata.PebbleAutomaton

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Ring

/-!
# Finite-Monoid Two-Way Substring Behavior for Pebble Automata

This module formalizes finite crossing-behavior maps for deterministic two-way
`k`-pebble automata on nonempty substrings visited without placing pebbles. Equal crossing
behaviors are preserved under list concatenation, yielding eventual periodicity of repeated blocks
`List.replicate n a` and invariance of acceptance under pebble-free substring substitution. All
results are proved under standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Main definitions

* `CslibFrontier.Computability.Automata.CrossingOutcome`: Terminal or looping outcome of a
  pebble-free two-way crossing of a nonempty substring.
* `CslibFrontier.Computability.Automata.PebbleAutomaton.twoWayBehavior`: Finite crossing-behavior
  map of a nonempty substring under a `k`-pebble automaton.

## Main results

* `CslibFrontier.Computability.Automata.PebbleAutomaton.twoWayBehavior_append_congr`: Crossing
  behavior is a congruence with respect to list concatenation.
* `CslibFrontier.Computability.Automata.PebbleAutomaton.exists_period_twoWayBehavior_replicate`:
  Eventual periodicity of `twoWayBehavior` on `List.replicate n a`.
* `PebbleAutomaton.accepts_iff_of_twoWayBehavior_eq_of_no_pebble`:
  Replacing a pebble-free substring by one with the same crossing behavior preserves acceptance.
-/

public section

namespace CslibFrontier.Computability.Automata

/-! ### Part 2: Finite-monoid pebble-free two-way substring behavior -/

/-- Outcome of running a `k`-pebble automaton locally across a nonempty substring without
placing pebbles. -/
inductive CrossingOutcome (Q : Type*) where
  | exitLeft (q : Q)
  | exitRight (q : Q)
  | halted (q : Q)
  | placed
  | loop
  deriving DecidableEq

instance instFintypeCrossingOutcome {Q : Type*} [Fintype Q] :
    Fintype (CrossingOutcome Q) := by
  let e : CrossingOutcome Q ≃ (Q ⊕ Q ⊕ Q) ⊕ (Unit ⊕ Unit) :=
    { toFun := fun
        | .exitLeft q => Sum.inl (Sum.inl q)
        | .exitRight q => Sum.inl (Sum.inr (Sum.inl q))
        | .halted q => Sum.inl (Sum.inr (Sum.inr q))
        | .placed => Sum.inr (Sum.inl ())
        | .loop => Sum.inr (Sum.inr ())
      invFun := fun
        | Sum.inl (Sum.inl q) => .exitLeft q
        | Sum.inl (Sum.inr (Sum.inl q)) => .exitRight q
        | Sum.inl (Sum.inr (Sum.inr q)) => .halted q
        | Sum.inr (Sum.inl ()) => .placed
        | Sum.inr (Sum.inr ()) => .loop
      left_inv := fun x ↦ by cases x <;> rfl
      right_inv := fun x ↦ by
        rcases x with (q | q | q) | (⟨⟩ | ⟨⟩) <;> rfl }
  exact Fintype.ofEquiv _ e.symm

namespace PebbleAutomaton

section TwoWayBehavior

private inductive LocalCfg (Q : Type*) (m : ℕ) where
  | inside (q : Q) (pos : Fin m)
  | exitLeft (q : Q)
  | exitRight (q : Q)
  | halted (q : Q)
  | placed
  deriving DecidableEq

private def outcomeToLocal {Q : Type*} {m : ℕ} : CrossingOutcome Q → Option (LocalCfg Q m)
  | .exitLeft q => some (.exitLeft q)
  | .exitRight q => some (.exitRight q)
  | .halted q => some (.halted q)
  | .placed => some .placed
  | .loop => none

private noncomputable def isHaltingDec {k : ℕ} {α Q : Type*} (M : PebbleAutomaton k α Q) (q : Q) :
    Bool :=
  let := Classical.propDecidable
  decide (q ∈ M.halting)

private theorem isHaltingDec_of_mem {k : ℕ} {α Q : Type*} {M : PebbleAutomaton k α Q} {q : Q}
    (h : q ∈ M.halting) : isHaltingDec M q = true := by
  simp [isHaltingDec, h]

private theorem isHaltingDec_of_not_mem {k : ℕ} {α Q : Type*} {M : PebbleAutomaton k α Q} {q : Q}
    (h : q ∉ M.halting) : isHaltingDec M q = false := by
  simp [isHaltingDec, h]

private noncomputable def localStep {k : ℕ} {α Q : Type*} (M : PebbleAutomaton k α Q)
    (B : Finset (Fin k)) (s : List α) : LocalCfg Q s.length → LocalCfg Q s.length
  | .inside q pos =>
    if isHaltingDec M q then
      .halted q
    else
      let res := M.δ q (.sym (s.get pos)) ∅ B
      if res.2.1 ≠ ∅ then
        .placed
      else
        match res.2.2.2 with
        | .stay => .inside res.1 pos
        | .left =>
          if 0 < pos.val then .inside res.1 ⟨pos.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) pos.isLt⟩
          else .exitLeft res.1
        | .right =>
          if h : pos.val + 1 < s.length then .inside res.1 ⟨pos.val + 1, h⟩
          else .exitRight res.1
  | .exitLeft q => .exitLeft q
  | .exitRight q => .exitRight q
  | .halted q => .halted q
  | .placed => .placed

private noncomputable def localRun {k : ℕ} {α Q : Type*} (M : PebbleAutomaton k α Q)
    (B : Finset (Fin k)) (s : List α) (q : Q) (pos : Fin s.length) (t : ℕ) :
    LocalCfg Q s.length :=
  (localStep M B s)^[t] (.inside q pos)

private theorem localStep_terminal {k : ℕ} {α Q : Type*} (M : PebbleAutomaton k α Q)
    (B : Finset (Fin k)) (s : List α) {c : LocalCfg Q s.length}
    (h : ∀ q pos, c ≠ .inside q pos) : localStep M B s c = c := by
  cases c with
  | inside q pos => exact absurd rfl (h q pos)
  | exitLeft _ => rfl
  | exitRight _ => rfl
  | halted _ => rfl
  | placed => rfl

private theorem localRun_eq_of_terminal {k : ℕ} {α Q : Type*} (M : PebbleAutomaton k α Q)
    (B : Finset (Fin k)) (s : List α) (q : Q) (pos : Fin s.length) {t : ℕ}
    (h : ∀ q' pos', localRun M B s q pos t ≠ .inside q' pos') :
    ∀ u ≥ t, localRun M B s q pos u = localRun M B s q pos t := by
  intro u hu
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hu
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [localRun] at ih ⊢
    rw [show t + (d + 1) = (t + d) + 1 by omega, Function.iterate_succ_apply', ih (by omega)]
    exact localStep_terminal M B s h

private theorem localRun_loop_of_inside_at_card {k : ℕ} {α Q : Type*} [Fintype Q]
    (M : PebbleAutomaton k α Q) (B : Finset (Fin k)) (s : List α) (q : Q) (pos : Fin s.length)
    {q₀ : Q} {pos₀ : Fin s.length}
    (h : localRun M B s q pos (Fintype.card Q * s.length) = .inside q₀ pos₀) :
    ∀ t : ℕ, ∃ q' pos', localRun M B s q pos t = .inside q' pos' := by
  let N := Fintype.card Q * s.length
  have hinside : ∀ t ≤ N, ∃ q' pos', localRun M B s q pos t = .inside q' pos' := by
    intro t ht
    by_contra hnot
    push Not at hnot
    have hEq := localRun_eq_of_terminal M B s q pos hnot N ht
    rw [h] at hEq
    exact hnot q₀ pos₀ hEq.symm
  let g : Fin (N + 1) → Q × Fin s.length := fun i ↦
    let hi := hinside i.val (by omega)
    (hi.choose, hi.choose_spec.choose)
  have hg_spec : ∀ i : Fin (N + 1),
      localRun M B s q pos i.val = .inside (g i).1 (g i).2 := by
    intro i
    exact (hinside i.val (by omega)).choose_spec.choose_spec
  have hnot_inj : ¬ Function.Injective g := by
    intro hinj
    have hcard := Fintype.card_le_of_injective g hinj
    simp only [Fintype.card_fin, Fintype.card_prod, N] at hcard
    omega
  rw [Function.Injective] at hnot_inj
  push Not at hnot_inj
  rcases hnot_inj with ⟨i, j, hij, hne⟩
  have hlt_or : i.val < j.val ∨ j.val < i.val := by
    have : i.val ≠ j.val := fun heq ↦ hne (Fin.ext heq)
    omega
  obtain ⟨a, b, hab, hb, hEq_ab⟩ :
      ∃ a b : ℕ, a < b ∧ b ≤ N ∧ localRun M B s q pos a = localRun M B s q pos b := by
    rcases hlt_or with hlt | hlt
    · exact ⟨i.val, j.val, hlt, by omega, by rw [hg_spec i, hg_spec j, hij]⟩
    · exact ⟨j.val, i.val, hlt, by omega, by rw [hg_spec j, hg_spec i, hij]⟩
  have hper : ∀ d : ℕ, localRun M B s q pos (a + d) =
      localRun M B s q pos (a + d % (b - a)) := by
    have hstep_per : ∀ m : ℕ, localRun M B s q pos (a + m + (b - a)) =
        localRun M B s q pos (a + m) := by
      intro m
      have : a + m + (b - a) = m + b := by omega
      rw [this, show a + m = m + a by omega]
      simp only [localRun, Function.iterate_add_apply]
      have hEq_ab' : (localStep M B s)^[b] (.inside q pos) =
          (localStep M B s)^[a] (.inside q pos) := hEq_ab.symm
      rw [hEq_ab']
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
      by_cases hd : d < b - a
      · rw [Nat.mod_eq_of_lt hd]
      · have hsub : d - (b - a) < d := by omega
        have h1 : a + d = a + (d - (b - a)) + (b - a) := by omega
        have hmod : d % (b - a) = (d - (b - a)) % (b - a) := by
          rw [Nat.mod_eq_sub_mod (by omega)]
        rw [h1, hstep_per, ih _ hsub, ← hmod]
  intro t
  by_cases ht : t ≤ N
  · exact hinside t ht
  · have hge : a ≤ t := by omega
    have hlt_b : a + (t - a) % (b - a) ≤ N := by
      have hm : (t - a) % (b - a) < b - a := Nat.mod_lt _ (by omega)
      omega
    have hEq := hper (t - a)
    rw [Nat.add_sub_cancel' hge] at hEq
    rw [hEq]
    exact hinside _ hlt_b

private def entryPos {m : ℕ} (hm : 0 < m) (side : Bool) : Fin m :=
  if side then ⟨m - 1, by omega⟩ else ⟨0, hm⟩

/-- The finite crossing-behavior map of a nonempty substring `s` under a `k`-pebble automaton `M`.
For each available pebble set `B`, entry state `q`, and entry side (`false` = left, `true` =
right), `twoWayBehavior M s B q side` records whether `M` exits left, exits right, halts inside
`s`, tries to place a pebble inside `s`, or loops forever inside `s`. -/
noncomputable def twoWayBehavior {k : ℕ} {α Q : Type*} [Fintype Q]
    (M : PebbleAutomaton k α Q) (s : List α) :
    Finset (Fin k) → Q → Bool → CrossingOutcome Q :=
  fun B q side ↦
    if hs : 0 < s.length then
      match localRun M B s q (entryPos hs side) (Fintype.card Q * s.length + 1) with
      | .inside _ _ => .loop
      | .exitLeft q' => .exitLeft q'
      | .exitRight q' => .exitRight q'
      | .halted q' => .halted q'
      | .placed => .placed
    else
      .loop

private theorem twoWayBehavior_eq_terminal_iff {k : ℕ} {α Q : Type*} [Fintype Q]
    (M : PebbleAutomaton k α Q) {s : List α} (hs : 0 < s.length) (B : Finset (Fin k))
    (q : Q) (side : Bool) {τ : CrossingOutcome Q} {cτ : LocalCfg Q s.length}
    (hτ : outcomeToLocal τ = some cτ) :
    M.twoWayBehavior s B q side = τ ↔ ∃ t : ℕ, localRun M B s q (entryPos hs side) t = cτ := by
  have hcτ_term : ∀ q' pos', cτ ≠ .inside q' pos' := by
    cases τ <;> simp only [outcomeToLocal, Option.some.injEq, reduceCtorEq] at hτ
    all_goals subst hτ; intro _ _ h; cases h
  constructor
  · intro hbeh
    refine ⟨Fintype.card Q * s.length + 1, ?_⟩
    simp only [twoWayBehavior, hs, ↓reduceDIte] at hbeh
    cases hrun : localRun M B s q (entryPos hs side) (Fintype.card Q * s.length + 1) <;>
      rw [hrun] at hbeh <;> subst hbeh <;>
      simp only [outcomeToLocal, Option.some.injEq, reduceCtorEq] at hτ <;> exact hτ
  · rintro ⟨t, ht⟩
    have hAt : localRun M B s q (entryPos hs side) (Fintype.card Q * s.length + 1) = cτ := by
      by_cases hle : t ≤ Fintype.card Q * s.length + 1
      · rw [localRun_eq_of_terminal M B s q (entryPos hs side)
            (fun q' pos' ↦ ht ▸ hcτ_term q' pos') _ hle, ht]
      · have hnot : ∀ q₀ pos₀,
            localRun M B s q (entryPos hs side) (Fintype.card Q * s.length) ≠
              .inside q₀ pos₀ := by
          intro q₀ pos₀ h0
          rcases localRun_loop_of_inside_at_card M B s q (entryPos hs side) h0 t with
            ⟨q', pos', hEq⟩
          exact hcτ_term q' pos' (ht.symm.trans hEq)
        have hstep : localRun M B s q (entryPos hs side) (Fintype.card Q * s.length) =
            localRun M B s q (entryPos hs side) t :=
          (localRun_eq_of_terminal M B s q (entryPos hs side) hnot t (by omega)).symm
        rw [localRun_eq_of_terminal M B s q (entryPos hs side) hnot _ (by omega), hstep, ht]
    simp only [twoWayBehavior, hs, ↓reduceDIte, hAt]
    cases τ <;> simp only [outcomeToLocal, Option.some.injEq, reduceCtorEq] at hτ
    all_goals subst hτ; rfl

private theorem twoWayBehavior_eq_loop_iff {k : ℕ} {α Q : Type*} [Fintype Q]
    (M : PebbleAutomaton k α Q) {s : List α} (hs : 0 < s.length) (B : Finset (Fin k))
    (q : Q) (side : Bool) :
    M.twoWayBehavior s B q side = .loop ↔
      ∀ t : ℕ, ∃ q' pos', localRun M B s q (entryPos hs side) t = .inside q' pos' := by
  constructor
  · intro hbeh t
    simp only [twoWayBehavior, hs, ↓reduceDIte] at hbeh
    cases hrun : localRun M B s q (entryPos hs side) (Fintype.card Q * s.length + 1) with
    | inside q₀ pos₀ =>
      have h0 : ∃ q₁ pos₁, localRun M B s q (entryPos hs side) (Fintype.card Q * s.length) =
          .inside q₁ pos₁ := by
        by_contra hnot
        push Not at hnot
        have hEq := localRun_eq_of_terminal M B s q (entryPos hs side) hnot
          (Fintype.card Q * s.length + 1) (by omega)
        rw [hrun] at hEq
        exact hnot q₀ pos₀ hEq.symm
      rcases h0 with ⟨q₁, pos₁, h1⟩
      exact localRun_loop_of_inside_at_card M B s q (entryPos hs side) h1 t
    | exitLeft _ => rw [hrun] at hbeh; cases hbeh
    | exitRight _ => rw [hrun] at hbeh; cases hbeh
    | halted _ => rw [hrun] at hbeh; cases hbeh
    | placed => rw [hrun] at hbeh; cases hbeh
  · intro hall
    rcases hall (Fintype.card Q * s.length + 1) with ⟨q', pos', hEq⟩
    simp [twoWayBehavior, hs, hEq]

private theorem localRun_append_left {k : ℕ} {α Q : Type*} (M : PebbleAutomaton k α Q)
    (B : Finset (Fin k)) (s t : List α) (q : Q) (pos : Fin s.length) (n : ℕ)
    (hstay : ∀ u < n, ∃ q' pos', localRun M B s q pos u = .inside q' pos') :
    localRun M B (s ++ t) q ⟨pos.val, by simp; omega⟩ n =
      match localRun M B s q pos n with
      | .inside q' pos' => .inside q' ⟨pos'.val, by simp; omega⟩
      | .exitLeft q' => .exitLeft q'
      | .exitRight q' =>
        if ht : 0 < t.length then .inside q' ⟨s.length, by simp; omega⟩
        else .exitRight q'
      | .halted q' => .halted q'
      | .placed => .placed := by
  induction n with
  | zero =>
    simp [localRun]
  | succ n ih =>
    rcases hstay n (Nat.lt_succ_self n) with ⟨qn, posn, hqn⟩
    have hih := ih (fun u hu ↦ hstay u (Nat.lt_trans hu (Nat.lt_succ_self n)))
    simp only [hqn] at hih
    have hstep_l : localRun M B (s ++ t) q ⟨pos.val, by simp; omega⟩ (n + 1) =
        localStep M B (s ++ t) (.inside qn ⟨posn.val, by simp; omega⟩) := by
      simp only [localRun, Function.iterate_succ_apply']
      exact congrArg (localStep M B (s ++ t)) hih
    have hnext : localRun M B s q pos (n + 1) = localStep M B s (.inside qn posn) := by
      simp only [localRun, Function.iterate_succ_apply']
      exact congrArg (localStep M B s) hqn
    rw [hstep_l, hnext]
    have hget : (s ++ t).get ⟨posn.val, by simp; omega⟩ = s.get posn := by
      simp [List.getElem_append_left posn.isLt]
    unfold localStep
    dsimp only
    rw [hget]
    by_cases hH : qn ∈ M.halting
    · simp only [isHaltingDec_of_mem hH, ↓reduceIte]
    · simp only [isHaltingDec_of_not_mem hH, Bool.false_eq_true, ↓reduceIte]
      by_cases hP : (M.δ qn (.sym (s.get posn)) ∅ B).2.1 = ∅
      · simp only [hP, ne_eq, not_true_eq_false, ↓reduceIte]
        cases (M.δ qn (.sym (s.get posn)) ∅ B).2.2.2 with
        | stay => rfl
        | left =>
          by_cases hpos : 0 < posn.val <;> simp only [hpos, ↓reduceIte]
        | right =>
          by_cases hpos : posn.val + 1 < s.length
          · have hpos' : posn.val + 1 < (s ++ t).length := by simp; omega
            simp only [hpos, hpos', ↓reduceDIte]
          · by_cases ht : 0 < t.length
            · have hpos' : posn.val + 1 < (s ++ t).length := by simp; omega
              have hEq : posn.val + 1 = s.length := by omega
              simp only [hpos, hpos', ht, ↓reduceDIte]
              congr 1; exact Fin.ext hEq
            · have hpos' : ¬ (posn.val + 1 < (s ++ t).length) := by simp; omega
              simp only [hpos, hpos', ht, ↓reduceDIte]
      · simp only [hP, ne_eq, not_false_eq_true, ↓reduceIte]

private theorem localRun_append_right {k : ℕ} {α Q : Type*} (M : PebbleAutomaton k α Q)
    (B : Finset (Fin k)) (s t : List α) (q : Q) (pos : Fin t.length) (n : ℕ)
    (hstay : ∀ u < n, ∃ q' pos', localRun M B t q pos u = .inside q' pos') :
    localRun M B (s ++ t) q ⟨s.length + pos.val, by simp⟩ n =
      match localRun M B t q pos n with
      | .inside q' pos' => .inside q' ⟨s.length + pos'.val, by simp⟩
      | .exitLeft q' =>
        if hs : 0 < s.length then .inside q' ⟨s.length - 1, by simp; omega⟩
        else .exitLeft q'
      | .exitRight q' => .exitRight q'
      | .halted q' => .halted q'
      | .placed => .placed := by
  induction n with
  | zero =>
    simp [localRun]
  | succ n ih =>
    rcases hstay n (Nat.lt_succ_self n) with ⟨qn, posn, hqn⟩
    have hih := ih (fun u hu ↦ hstay u (Nat.lt_trans hu (Nat.lt_succ_self n)))
    simp only [hqn] at hih
    have hstep_r : localRun M B (s ++ t) q ⟨s.length + pos.val, by simp⟩ (n + 1) =
        localStep M B (s ++ t) (.inside qn ⟨s.length + posn.val, by simp⟩) := by
      simp only [localRun, Function.iterate_succ_apply']
      exact congrArg (localStep M B (s ++ t)) hih
    have hnext : localRun M B t q pos (n + 1) = localStep M B t (.inside qn posn) := by
      simp only [localRun, Function.iterate_succ_apply']
      exact congrArg (localStep M B t) hqn
    rw [hstep_r, hnext]
    have hget : (s ++ t).get ⟨s.length + posn.val, by simp⟩ = t.get posn := by
      simp only [List.get_eq_getElem]
      rw [List.getElem_append_right (Nat.le_add_right s.length posn.val)]
      simp
    unfold localStep
    dsimp only
    rw [hget]
    by_cases hH : qn ∈ M.halting
    · simp only [isHaltingDec_of_mem hH, ↓reduceIte]
    · simp only [isHaltingDec_of_not_mem hH, Bool.false_eq_true, ↓reduceIte]
      by_cases hP : (M.δ qn (.sym (t.get posn)) ∅ B).2.1 = ∅
      · simp only [hP, ne_eq, not_true_eq_false, ↓reduceIte]
        cases (M.δ qn (.sym (t.get posn)) ∅ B).2.2.2 with
        | stay => rfl
        | right =>
          by_cases hpos : posn.val + 1 < t.length
          · have hpos' : s.length + posn.val + 1 < (s ++ t).length := by simp; omega
            simp only [hpos, hpos', ↓reduceDIte]
            congr 1
          · have hpos' : ¬ (s.length + posn.val + 1 < (s ++ t).length) := by simp; omega
            simp only [hpos, hpos', ↓reduceDIte]
        | left =>
          by_cases hpos : 0 < posn.val
          · have hpos' : 0 < s.length + posn.val := by omega
            have hsub : s.length + posn.val - 1 = s.length + (posn.val - 1) := by omega
            simp only [hpos, hpos', ↓reduceIte]
            congr 1; exact Fin.ext hsub
          · by_cases hs : 0 < s.length
            · have hpos' : 0 < s.length + posn.val := by omega
              have hsub : s.length + posn.val - 1 = s.length - 1 := by omega
              simp only [hpos, hpos', hs, ↓reduceIte, ↓reduceDIte]
              congr 1; exact Fin.ext hsub
            · have hpos' : ¬ (0 < s.length + posn.val) := by omega
              simp only [hpos, hpos', hs, ↓reduceIte, ↓reduceDIte]
      · simp only [hP, ne_eq, not_false_eq_true, ↓reduceIte]

private theorem first_terminal_of_reaches {k : ℕ} {α Q : Type*}
    (M : PebbleAutomaton k α Q) (B : Finset (Fin k)) (s : List α)
    (q : Q) (pos : Fin s.length) {cτ : LocalCfg Q s.length} {d₀ : ℕ}
    (hcτ : ∀ q' pos', cτ ≠ .inside q' pos')
    (hd₀ : localRun M B s q pos d₀ = cτ) :
    ∃ d ≤ d₀,
      (∀ u < d, ∃ q' pos', localRun M B s q pos u = .inside q' pos') ∧
      localRun M B s q pos d = cτ := by
  classical
  have hleast : ∃ d, ∀ q' pos', localRun M B s q pos d ≠ .inside q' pos' :=
    ⟨d₀, fun q' pos' h ↦ hcτ q' pos' (hd₀.symm.trans h)⟩
  let d := Nat.find hleast
  have hd_term : ∀ q' pos', localRun M B s q pos d ≠ .inside q' pos' := Nat.find_spec hleast
  have hd_le : d ≤ d₀ := Nat.find_min' hleast (fun q' pos' h ↦ hcτ q' pos' (hd₀.symm.trans h))
  refine ⟨d, hd_le, fun u hu ↦ ?_, ?_⟩
  · by_contra hnot
    push Not at hnot
    exact Nat.find_min hleast hu hnot
  · rw [← localRun_eq_of_terminal M B s q pos hd_term d₀ hd_le, hd₀]

private theorem localRun_append_reaches_iff {k : ℕ} {α Q : Type*} [Fintype Q]
    (M : PebbleAutomaton k α Q) {s₁ s₂ t₁ t₂ : List α}
    (hs₁ : 0 < s₁.length) (hs₂ : 0 < s₂.length) (ht₁ : 0 < t₁.length) (ht₂ : 0 < t₂.length)
    (hs : M.twoWayBehavior s₁ = M.twoWayBehavior s₂)
    (ht : M.twoWayBehavior t₁ = M.twoWayBehavior t₂)
    (B : Finset (Fin k)) {τ : CrossingOutcome Q}
    (hτ_ne : τ ≠ .loop) :
    ∀ (n : ℕ) (seg entry : Bool) (q : Q),
      (localRun M B (s₁ ++ t₁) q
        (if seg then ⟨s₁.length + (entryPos ht₁ entry).val, by simp⟩
         else ⟨(entryPos hs₁ entry).val, by simp; omega⟩) n =
        (outcomeToLocal τ).get (by cases τ <;> simp_all [outcomeToLocal])) →
      ∃ n' : ℕ,
        localRun M B (s₂ ++ t₂) q
          (if seg then ⟨s₂.length + (entryPos ht₂ entry).val, by simp⟩
           else ⟨(entryPos hs₂ entry).val, by simp; omega⟩) n' =
          (outcomeToLocal τ).get (by cases τ <;> simp_all [outcomeToLocal]) := by
  classical
  have hsome : ∀ (m : ℕ), (outcomeToLocal (m := m) τ).isSome := by
    intro m; cases τ with
    | loop => exact absurd rfl hτ_ne
    | exitLeft _ => rfl
    | exitRight _ => rfl
    | halted _ => rfl
    | placed => rfl
  let cτ₁ : LocalCfg Q (s₁ ++ t₁).length := (outcomeToLocal τ).get (hsome _)
  let cτ₂ : LocalCfg Q (s₂ ++ t₂).length := (outcomeToLocal τ).get (hsome _)
  have hcτ₁_term : ∀ q' pos', cτ₁ ≠ .inside q' pos' := by
    intro _ _ h
    cases τ with
    | loop => exact absurd rfl hτ_ne
    | exitLeft _ => simp [cτ₁, outcomeToLocal] at h
    | exitRight _ => simp [cτ₁, outcomeToLocal] at h
    | halted _ => simp [cτ₁, outcomeToLocal] at h
    | placed => simp [cτ₁, outcomeToLocal] at h
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro seg entry q hreach
    cases seg with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hreach ⊢
      have hex_term : ∃ d ≤ n,
          (∀ u < d, ∃ q' pos', localRun M B s₁ q (entryPos hs₁ entry) u = .inside q' pos') ∧
          (∀ q' pos', localRun M B s₁ q (entryPos hs₁ entry) d ≠ .inside q' pos') := by
        by_contra hnot
        have hall : ∀ u ≤ n, ∃ q' pos',
            localRun M B s₁ q (entryPos hs₁ entry) u = .inside q' pos' := by
          intro u hu
          induction u using Nat.strongRecOn with
          | ind u ihu =>
            by_contra hu_term
            push Not at hu_term
            exact hnot ⟨u, hu, fun v hv ↦ ihu v hv (by omega), hu_term⟩
        have hEq := localRun_append_left M B s₁ t₁ q (entryPos hs₁ entry) n
          (fun u hu ↦ hall u (le_of_lt hu))
        rcases hall n le_rfl with ⟨qn, posn, hqn⟩
        rw [hqn] at hEq
        exact hcτ₁_term qn ⟨posn.val, by simp; omega⟩ (hreach.symm.trans hEq)
      rcases hex_term with ⟨d, hd_le, hd_stay, hd_term⟩
      have hd_pos : 1 ≤ d := by
        cases d with
        | zero => exact absurd rfl (hd_term q (entryPos hs₁ entry))
        | succ _ => omega
      have hEq_d := localRun_append_left M B s₁ t₁ q (entryPos hs₁ entry) d hd_stay
      cases hσ : localRun M B s₁ q (entryPos hs₁ entry) d with
      | inside q' pos' => exact absurd hσ (hd_term q' pos')
      | exitRight q' =>
        have hbeh₁ : M.twoWayBehavior s₁ B q entry = .exitRight q' :=
          (twoWayBehavior_eq_terminal_iff M hs₁ B q entry
            (show outcomeToLocal (.exitRight q') = some (.exitRight q') from rfl)).mpr ⟨d, hσ⟩
        have hbeh₂ : M.twoWayBehavior s₂ B q entry = .exitRight q' := by rw [← hs, hbeh₁]
        rcases (twoWayBehavior_eq_terminal_iff M hs₂ B q entry
            (show outcomeToLocal (.exitRight q') = some (.exitRight q') from rfl)).mp hbeh₂ with
          ⟨d₂, hd₂⟩
        rcases first_terminal_of_reaches M B s₂ q (entryPos hs₂ entry)
            (fun _ _ h ↦ by cases h) hd₂ with ⟨d', _, hd'_stay, hd'_eq⟩
        simp only [hσ, ht₁] at hEq_d
        have hEq_d1 : localRun M B (s₁ ++ t₁) q
            ⟨(entryPos hs₁ entry).val, by simp; omega⟩ d =
            .inside q' ⟨s₁.length + (entryPos ht₁ false).val, by simp [entryPos, ht₁]⟩ := by
          simpa [entryPos] using hEq_d
        have hrem : localRun M B (s₁ ++ t₁) q'
            ⟨s₁.length + (entryPos ht₁ false).val, by simp [entryPos, ht₁]⟩ (n - d) = cτ₁ := by
          have hadd : n = (n - d) + d := by omega
          rw [hadd, localRun, Function.iterate_add_apply] at hreach
          change (localStep M B (s₁ ++ t₁))^[n - d]
              (localRun M B (s₁ ++ t₁) q ⟨(entryPos hs₁ entry).val, by simp; omega⟩ d) =
              cτ₁ at hreach
          rw [hEq_d1] at hreach
          exact hreach
        rcases ih (n - d) (by omega) true false q' hrem with ⟨n'', hn''⟩
        have h2 := localRun_append_left M B s₂ t₂ q (entryPos hs₂ entry) d' hd'_stay
        simp only [hd'_eq, ht₂, ↓reduceDIte] at h2
        have hEq_d2 : localRun M B (s₂ ++ t₂) q
            ⟨(entryPos hs₂ entry).val, by simp; omega⟩ d' =
            .inside q' ⟨s₂.length + (entryPos ht₂ false).val, by simp [entryPos, ht₂]⟩ := by
          simpa [entryPos] using h2
        refine ⟨n'' + d', ?_⟩
        rw [localRun, Function.iterate_add_apply]
        change (localStep M B (s₂ ++ t₂))^[n'']
            (localRun M B (s₂ ++ t₂) q ⟨(entryPos hs₂ entry).val, by simp; omega⟩ d') = cτ₂
        rw [hEq_d2]
        exact hn''
      | exitLeft q' =>
        rw [hσ] at hEq_d
        have hAtN : localRun M B (s₁ ++ t₁) q ⟨(entryPos hs₁ entry).val, by simp; omega⟩ n =
            .exitLeft q' := by
          rw [localRun_eq_of_terminal M B (s₁ ++ t₁) q _
            (fun _ _ h ↦ by rw [hEq_d] at h; cases h) n hd_le, hEq_d]
        have hEq_τ : cτ₁ = .exitLeft q' := hreach.symm.trans hAtN
        have hτ_eq : τ = .exitLeft q' := by
          cases τ with
          | loop => exact absurd rfl hτ_ne
          | exitLeft _ => simpa [cτ₁, outcomeToLocal] using hEq_τ
          | exitRight _ => simp [cτ₁, outcomeToLocal] at hEq_τ
          | halted _ => simp [cτ₁, outcomeToLocal] at hEq_τ
          | placed => simp [cτ₁, outcomeToLocal] at hEq_τ
        have hbeh₁ : M.twoWayBehavior s₁ B q entry = .exitLeft q' :=
          (twoWayBehavior_eq_terminal_iff M hs₁ B q entry
            (show outcomeToLocal (.exitLeft q') = some (.exitLeft q') from rfl)).mpr ⟨d, hσ⟩
        have hbeh₂ : M.twoWayBehavior s₂ B q entry = .exitLeft q' := by rw [← hs, hbeh₁]
        rcases (twoWayBehavior_eq_terminal_iff M hs₂ B q entry
            (show outcomeToLocal (.exitLeft q') = some (.exitLeft q') from rfl)).mp hbeh₂ with
          ⟨d₂, hd₂⟩
        rcases first_terminal_of_reaches M B s₂ q (entryPos hs₂ entry)
            (fun _ _ h ↦ by cases h) hd₂ with ⟨d', _, hd'_stay, hd'_eq⟩
        have h2 := localRun_append_left M B s₂ t₂ q (entryPos hs₂ entry) d' hd'_stay
        rw [hd'_eq] at h2
        exact ⟨d', by subst hτ_eq; exact h2⟩
      | halted q' =>
        rw [hσ] at hEq_d
        have hAtN : localRun M B (s₁ ++ t₁) q ⟨(entryPos hs₁ entry).val, by simp; omega⟩ n =
            .halted q' := by
          rw [localRun_eq_of_terminal M B (s₁ ++ t₁) q _
            (fun _ _ h ↦ by rw [hEq_d] at h; cases h) n hd_le, hEq_d]
        have hEq_τ : cτ₁ = .halted q' := hreach.symm.trans hAtN
        have hτ_eq : τ = .halted q' := by
          cases τ with
          | loop => exact absurd rfl hτ_ne
          | exitLeft _ => simp [cτ₁, outcomeToLocal] at hEq_τ
          | exitRight _ => simp [cτ₁, outcomeToLocal] at hEq_τ
          | halted _ => simpa [cτ₁, outcomeToLocal] using hEq_τ
          | placed => simp [cτ₁, outcomeToLocal] at hEq_τ
        have hbeh₁ : M.twoWayBehavior s₁ B q entry = .halted q' :=
          (twoWayBehavior_eq_terminal_iff M hs₁ B q entry
            (show outcomeToLocal (.halted q') = some (.halted q') from rfl)).mpr ⟨d, hσ⟩
        have hbeh₂ : M.twoWayBehavior s₂ B q entry = .halted q' := by rw [← hs, hbeh₁]
        rcases (twoWayBehavior_eq_terminal_iff M hs₂ B q entry
            (show outcomeToLocal (.halted q') = some (.halted q') from rfl)).mp hbeh₂ with
          ⟨d₂, hd₂⟩
        rcases first_terminal_of_reaches M B s₂ q (entryPos hs₂ entry)
            (fun _ _ h ↦ by cases h) hd₂ with ⟨d', _, hd'_stay, hd'_eq⟩
        have h2 := localRun_append_left M B s₂ t₂ q (entryPos hs₂ entry) d' hd'_stay
        rw [hd'_eq] at h2
        exact ⟨d', by subst hτ_eq; exact h2⟩
      | placed =>
        rw [hσ] at hEq_d
        have hAtN : localRun M B (s₁ ++ t₁) q ⟨(entryPos hs₁ entry).val, by simp; omega⟩ n =
            .placed := by
          rw [localRun_eq_of_terminal M B (s₁ ++ t₁) q _
            (fun _ _ h ↦ by rw [hEq_d] at h; cases h) n hd_le, hEq_d]
        have hEq_τ : cτ₁ = .placed := hreach.symm.trans hAtN
        have hτ_eq : τ = .placed := by
          cases τ with
          | loop => exact absurd rfl hτ_ne
          | exitLeft _ => simp [cτ₁, outcomeToLocal] at hEq_τ
          | exitRight _ => simp [cτ₁, outcomeToLocal] at hEq_τ
          | halted _ => simp [cτ₁, outcomeToLocal] at hEq_τ
          | placed => rfl
        have hbeh₁ : M.twoWayBehavior s₁ B q entry = .placed :=
          (twoWayBehavior_eq_terminal_iff M hs₁ B q entry
            (show outcomeToLocal .placed = some .placed from rfl)).mpr ⟨d, hσ⟩
        have hbeh₂ : M.twoWayBehavior s₂ B q entry = .placed := by rw [← hs, hbeh₁]
        rcases (twoWayBehavior_eq_terminal_iff M hs₂ B q entry
            (show outcomeToLocal .placed = some .placed from rfl)).mp hbeh₂ with
          ⟨d₂, hd₂⟩
        rcases first_terminal_of_reaches M B s₂ q (entryPos hs₂ entry)
            (fun _ _ h ↦ by cases h) hd₂ with ⟨d', _, hd'_stay, hd'_eq⟩
        have h2 := localRun_append_left M B s₂ t₂ q (entryPos hs₂ entry) d' hd'_stay
        rw [hd'_eq] at h2
        exact ⟨d', by subst hτ_eq; exact h2⟩
    | true =>
      simp only [↓reduceIte] at hreach ⊢
      have hex_term : ∃ d ≤ n,
          (∀ u < d, ∃ q' pos', localRun M B t₁ q (entryPos ht₁ entry) u = .inside q' pos') ∧
          (∀ q' pos', localRun M B t₁ q (entryPos ht₁ entry) d ≠ .inside q' pos') := by
        by_contra hnot
        have hall : ∀ u ≤ n, ∃ q' pos',
            localRun M B t₁ q (entryPos ht₁ entry) u = .inside q' pos' := by
          intro u hu
          induction u using Nat.strongRecOn with
          | ind u ihu =>
            by_contra hu_term
            push Not at hu_term
            exact hnot ⟨u, hu, fun v hv ↦ ihu v hv (by omega), hu_term⟩
        have hEq := localRun_append_right M B s₁ t₁ q (entryPos ht₁ entry) n
          (fun u hu ↦ hall u (le_of_lt hu))
        rcases hall n le_rfl with ⟨qn, posn, hqn⟩
        rw [hqn] at hEq
        exact hcτ₁_term qn ⟨s₁.length + posn.val, by simp⟩ (hreach.symm.trans hEq)
      rcases hex_term with ⟨d, hd_le, hd_stay, hd_term⟩
      have hd_pos : 1 ≤ d := by
        cases d with
        | zero => exact absurd rfl (hd_term q (entryPos ht₁ entry))
        | succ _ => omega
      have hEq_d := localRun_append_right M B s₁ t₁ q (entryPos ht₁ entry) d hd_stay
      cases hσ : localRun M B t₁ q (entryPos ht₁ entry) d with
      | inside q' pos' => exact absurd hσ (hd_term q' pos')
      | exitLeft q' =>
        have hbeh₁ : M.twoWayBehavior t₁ B q entry = .exitLeft q' :=
          (twoWayBehavior_eq_terminal_iff M ht₁ B q entry
            (show outcomeToLocal (.exitLeft q') = some (.exitLeft q') from rfl)).mpr ⟨d, hσ⟩
        have hbeh₂ : M.twoWayBehavior t₂ B q entry = .exitLeft q' := by rw [← ht, hbeh₁]
        rcases (twoWayBehavior_eq_terminal_iff M ht₂ B q entry
            (show outcomeToLocal (.exitLeft q') = some (.exitLeft q') from rfl)).mp hbeh₂ with
          ⟨d₂, hd₂⟩
        rcases first_terminal_of_reaches M B t₂ q (entryPos ht₂ entry)
            (fun _ _ h ↦ by cases h) hd₂ with ⟨d', _, hd'_stay, hd'_eq⟩
        simp only [hσ, hs₁, ↓reduceDIte] at hEq_d
        have hEq_d1 : localRun M B (s₁ ++ t₁) q
            ⟨s₁.length + (entryPos ht₁ entry).val, by simp⟩ d =
            .inside q' ⟨(entryPos hs₁ true).val, by simp [entryPos]; omega⟩ := by
          simpa [entryPos] using hEq_d
        have hrem : localRun M B (s₁ ++ t₁) q'
            ⟨(entryPos hs₁ true).val, by simp [entryPos]; omega⟩ (n - d) = cτ₁ := by
          have hadd : n = (n - d) + d := by omega
          rw [hadd, localRun, Function.iterate_add_apply] at hreach
          change (localStep M B (s₁ ++ t₁))^[n - d]
              (localRun M B (s₁ ++ t₁) q
                ⟨s₁.length + (entryPos ht₁ entry).val, by simp⟩ d) = cτ₁ at hreach
          rw [hEq_d1] at hreach
          exact hreach
        rcases ih (n - d) (by omega) false true q' hrem with ⟨n'', hn''⟩
        have h2 := localRun_append_right M B s₂ t₂ q (entryPos ht₂ entry) d' hd'_stay
        simp only [hd'_eq, hs₂, ↓reduceDIte] at h2
        have hEq_d2 : localRun M B (s₂ ++ t₂) q
            ⟨s₂.length + (entryPos ht₂ entry).val, by simp⟩ d' =
            .inside q' ⟨(entryPos hs₂ true).val, by simp [entryPos]; omega⟩ := by
          simpa [entryPos] using h2
        refine ⟨n'' + d', ?_⟩
        rw [localRun, Function.iterate_add_apply]
        change (localStep M B (s₂ ++ t₂))^[n'']
            (localRun M B (s₂ ++ t₂) q
              ⟨s₂.length + (entryPos ht₂ entry).val, by simp⟩ d') = cτ₂
        rw [hEq_d2]
        exact hn''
      | exitRight q' =>
        rw [hσ] at hEq_d
        have hAtN : localRun M B (s₁ ++ t₁) q
            ⟨s₁.length + (entryPos ht₁ entry).val, by simp⟩ n = .exitRight q' := by
          rw [localRun_eq_of_terminal M B (s₁ ++ t₁) q _
            (fun _ _ h ↦ by rw [hEq_d] at h; cases h) n hd_le, hEq_d]
        have hEq_τ : cτ₁ = .exitRight q' := hreach.symm.trans hAtN
        have hτ_eq : τ = .exitRight q' := by
          cases τ with
          | loop => exact absurd rfl hτ_ne
          | exitLeft _ => simp [cτ₁, outcomeToLocal] at hEq_τ
          | exitRight _ => simpa [cτ₁, outcomeToLocal] using hEq_τ
          | halted _ => simp [cτ₁, outcomeToLocal] at hEq_τ
          | placed => simp [cτ₁, outcomeToLocal] at hEq_τ
        have hbeh₁ : M.twoWayBehavior t₁ B q entry = .exitRight q' :=
          (twoWayBehavior_eq_terminal_iff M ht₁ B q entry
            (show outcomeToLocal (.exitRight q') = some (.exitRight q') from rfl)).mpr ⟨d, hσ⟩
        have hbeh₂ : M.twoWayBehavior t₂ B q entry = .exitRight q' := by rw [← ht, hbeh₁]
        rcases (twoWayBehavior_eq_terminal_iff M ht₂ B q entry
            (show outcomeToLocal (.exitRight q') = some (.exitRight q') from rfl)).mp hbeh₂ with
          ⟨d₂, hd₂⟩
        rcases first_terminal_of_reaches M B t₂ q (entryPos ht₂ entry)
            (fun _ _ h ↦ by cases h) hd₂ with ⟨d', _, hd'_stay, hd'_eq⟩
        have h2 := localRun_append_right M B s₂ t₂ q (entryPos ht₂ entry) d' hd'_stay
        rw [hd'_eq] at h2
        exact ⟨d', by subst hτ_eq; exact h2⟩
      | halted q' =>
        rw [hσ] at hEq_d
        have hAtN : localRun M B (s₁ ++ t₁) q
            ⟨s₁.length + (entryPos ht₁ entry).val, by simp⟩ n = .halted q' := by
          rw [localRun_eq_of_terminal M B (s₁ ++ t₁) q _
            (fun _ _ h ↦ by rw [hEq_d] at h; cases h) n hd_le, hEq_d]
        have hEq_τ : cτ₁ = .halted q' := hreach.symm.trans hAtN
        have hτ_eq : τ = .halted q' := by
          cases τ with
          | loop => exact absurd rfl hτ_ne
          | exitLeft _ => simp [cτ₁, outcomeToLocal] at hEq_τ
          | exitRight _ => simp [cτ₁, outcomeToLocal] at hEq_τ
          | halted _ => simpa [cτ₁, outcomeToLocal] using hEq_τ
          | placed => simp [cτ₁, outcomeToLocal] at hEq_τ
        have hbeh₁ : M.twoWayBehavior t₁ B q entry = .halted q' :=
          (twoWayBehavior_eq_terminal_iff M ht₁ B q entry
            (show outcomeToLocal (.halted q') = some (.halted q') from rfl)).mpr ⟨d, hσ⟩
        have hbeh₂ : M.twoWayBehavior t₂ B q entry = .halted q' := by rw [← ht, hbeh₁]
        rcases (twoWayBehavior_eq_terminal_iff M ht₂ B q entry
            (show outcomeToLocal (.halted q') = some (.halted q') from rfl)).mp hbeh₂ with
          ⟨d₂, hd₂⟩
        rcases first_terminal_of_reaches M B t₂ q (entryPos ht₂ entry)
            (fun _ _ h ↦ by cases h) hd₂ with ⟨d', _, hd'_stay, hd'_eq⟩
        have h2 := localRun_append_right M B s₂ t₂ q (entryPos ht₂ entry) d' hd'_stay
        rw [hd'_eq] at h2
        exact ⟨d', by subst hτ_eq; exact h2⟩
      | placed =>
        rw [hσ] at hEq_d
        have hAtN : localRun M B (s₁ ++ t₁) q
            ⟨s₁.length + (entryPos ht₁ entry).val, by simp⟩ n = .placed := by
          rw [localRun_eq_of_terminal M B (s₁ ++ t₁) q _
            (fun _ _ h ↦ by rw [hEq_d] at h; cases h) n hd_le, hEq_d]
        have hEq_τ : cτ₁ = .placed := hreach.symm.trans hAtN
        have hτ_eq : τ = .placed := by
          cases τ with
          | loop => exact absurd rfl hτ_ne
          | exitLeft _ => simp [cτ₁, outcomeToLocal] at hEq_τ
          | exitRight _ => simp [cτ₁, outcomeToLocal] at hEq_τ
          | halted _ => simp [cτ₁, outcomeToLocal] at hEq_τ
          | placed => rfl
        have hbeh₁ : M.twoWayBehavior t₁ B q entry = .placed :=
          (twoWayBehavior_eq_terminal_iff M ht₁ B q entry
            (show outcomeToLocal .placed = some .placed from rfl)).mpr ⟨d, hσ⟩
        have hbeh₂ : M.twoWayBehavior t₂ B q entry = .placed := by rw [← ht, hbeh₁]
        rcases (twoWayBehavior_eq_terminal_iff M ht₂ B q entry
            (show outcomeToLocal .placed = some .placed from rfl)).mp hbeh₂ with
          ⟨d₂, hd₂⟩
        rcases first_terminal_of_reaches M B t₂ q (entryPos ht₂ entry)
            (fun _ _ h ↦ by cases h) hd₂ with ⟨d', _, hd'_stay, hd'_eq⟩
        have h2 := localRun_append_right M B s₂ t₂ q (entryPos ht₂ entry) d' hd'_stay
        rw [hd'_eq] at h2
        exact ⟨d', by subst hτ_eq; exact h2⟩

/-- Crossing behavior is a congruence with respect to concatenation of nonempty lists. -/
theorem twoWayBehavior_append_congr {k : ℕ} {α Q : Type*} [Fintype Q]
    (M : PebbleAutomaton k α Q) {s₁ s₂ t₁ t₂ : List α}
    (hs₁ : 0 < s₁.length) (hs₂ : 0 < s₂.length) (ht₁ : 0 < t₁.length) (ht₂ : 0 < t₂.length)
    (hs : M.twoWayBehavior s₁ = M.twoWayBehavior s₂)
    (ht : M.twoWayBehavior t₁ = M.twoWayBehavior t₂) :
    M.twoWayBehavior (s₁ ++ t₁) = M.twoWayBehavior (s₂ ++ t₂) := by
  classical
  have hst₁ : 0 < (s₁ ++ t₁).length := by simp; omega
  have hst₂ : 0 < (s₂ ++ t₂).length := by simp; omega
  funext B q side
  have h_imp : ∀ {τ : CrossingOutcome Q}, τ ≠ .loop →
      M.twoWayBehavior (s₁ ++ t₁) B q side = τ → M.twoWayBehavior (s₂ ++ t₂) B q side = τ := by
    intro τ hτ hEq
    cases hopt : outcomeToLocal (m := (s₁ ++ t₁).length) τ with
    | none =>
      cases τ with
      | loop => exact absurd rfl hτ
      | exitLeft _ => simp [outcomeToLocal] at hopt
      | exitRight _ => simp [outcomeToLocal] at hopt
      | halted _ => simp [outcomeToLocal] at hopt
      | placed => simp [outcomeToLocal] at hopt
    | some cτ₁ =>
      cases hopt₂ : outcomeToLocal (m := (s₂ ++ t₂).length) τ with
      | none =>
        cases τ with
        | loop => exact absurd rfl hτ
        | exitLeft _ => simp [outcomeToLocal] at hopt₂
        | exitRight _ => simp [outcomeToLocal] at hopt₂
        | halted _ => simp [outcomeToLocal] at hopt₂
        | placed => simp [outcomeToLocal] at hopt₂
      | some cτ₂ =>
        rcases (twoWayBehavior_eq_terminal_iff M hst₁ B q side hopt).mp hEq with ⟨n, hn⟩
        have hpos_eq : (if side then ⟨s₁.length + (entryPos ht₁ side).val, by simp⟩
            else ⟨(entryPos hs₁ side).val, by simp; omega⟩ : Fin (s₁ ++ t₁).length) =
            entryPos hst₁ side := by
          cases side <;> simp [entryPos]
          omega
        have hpos_eq₂ : (if side then ⟨s₂.length + (entryPos ht₂ side).val, by simp⟩
            else ⟨(entryPos hs₂ side).val, by simp; omega⟩ : Fin (s₂ ++ t₂).length) =
            entryPos hst₂ side := by
          cases side <;> simp [entryPos]
          omega
        have hget1 : (outcomeToLocal τ).get (by cases τ with
            | loop => exact absurd rfl hτ
            | _ => rfl) = cτ₁ := by
          simp [hopt]
        have hget2 : (outcomeToLocal τ).get (by cases τ with
            | loop => exact absurd rfl hτ
            | _ => rfl) = cτ₂ := by
          simp [hopt₂]
        have hn' := localRun_append_reaches_iff M hs₁ hs₂ ht₁ ht₂ hs ht B hτ n side side q
        rw [hpos_eq, hpos_eq₂, hget1, hget2] at hn'
        exact (twoWayBehavior_eq_terminal_iff M hst₂ B q side hopt₂).mpr (hn' hn)
  cases h1 : M.twoWayBehavior (s₁ ++ t₁) B q side with
  | loop =>
    by_contra hne
    have h2_imp : ∀ {τ : CrossingOutcome Q}, τ ≠ .loop →
        M.twoWayBehavior (s₂ ++ t₂) B q side = τ → M.twoWayBehavior (s₁ ++ t₁) B q side = τ := by
      intro τ hτ hEq
      cases hopt : outcomeToLocal (m := (s₂ ++ t₂).length) τ with
      | none =>
        cases τ with
        | loop => exact absurd rfl hτ
        | exitLeft _ => simp [outcomeToLocal] at hopt
        | exitRight _ => simp [outcomeToLocal] at hopt
        | halted _ => simp [outcomeToLocal] at hopt
        | placed => simp [outcomeToLocal] at hopt
      | some cτ₂ =>
        cases hopt₁ : outcomeToLocal (m := (s₁ ++ t₁).length) τ with
        | none =>
          cases τ with
          | loop => exact absurd rfl hτ
          | exitLeft _ => simp [outcomeToLocal] at hopt₁
          | exitRight _ => simp [outcomeToLocal] at hopt₁
          | halted _ => simp [outcomeToLocal] at hopt₁
          | placed => simp [outcomeToLocal] at hopt₁
        | some cτ₁ =>
          rcases (twoWayBehavior_eq_terminal_iff M hst₂ B q side hopt).mp hEq with ⟨n, hn⟩
          have hpos_eq : (if side then ⟨s₂.length + (entryPos ht₂ side).val, by simp⟩
              else ⟨(entryPos hs₂ side).val, by simp; omega⟩ : Fin (s₂ ++ t₂).length) =
              entryPos hst₂ side := by
            cases side <;> simp [entryPos]; omega
          have hpos_eq₁ : (if side then ⟨s₁.length + (entryPos ht₁ side).val, by simp⟩
              else ⟨(entryPos hs₁ side).val, by simp; omega⟩ : Fin (s₁ ++ t₁).length) =
              entryPos hst₁ side := by
            cases side <;> simp [entryPos]; omega
          have hn' := localRun_append_reaches_iff M hs₂ hs₁ ht₂ ht₁ hs.symm ht.symm
            B hτ n side side q
          rw [hpos_eq, hpos_eq₁, show (outcomeToLocal τ).get _ = cτ₂ by simp [hopt],
            show (outcomeToLocal τ).get _ = cτ₁ by simp [hopt₁]] at hn'
          exact (twoWayBehavior_eq_terminal_iff M hst₁ B q side hopt₁).mpr (hn' hn)
    have := h2_imp (Ne.symm hne) rfl
    rw [h1] at this
    exact hne this
  | exitLeft q' => exact (h_imp (by simp) h1).symm
  | exitRight q' => exact (h_imp (by simp) h1).symm
  | halted q' => exact (h_imp (by simp) h1).symm
  | placed => exact (h_imp (by simp) h1).symm

/-- Eventual periodicity of `twoWayBehavior` on repeated single-letter blocks `List.replicate n a`.
There exist a preperiod `p ≥ 1` and period `d ≥ 1` bounded by the finite cardinality of the
behavior codomain plus `1`. -/
theorem exists_period_twoWayBehavior_replicate {k : ℕ} {α Q : Type*} [Fintype Q] [DecidableEq Q]
    (M : PebbleAutomaton k α Q) (a : α) :
    ∃ p d : ℕ, 1 ≤ p ∧ 1 ≤ d ∧
      p + d ≤ Fintype.card (Finset (Fin k) → Q → Bool → CrossingOutcome Q) + 1 ∧
      ∀ n q : ℕ, p ≤ n →
        M.twoWayBehavior (List.replicate (n + q * d) a) =
          M.twoWayBehavior (List.replicate n a) := by
  let K := Fintype.card (Finset (Fin k) → Q → Bool → CrossingOutcome Q)
  let g : Fin (K + 1) → (Finset (Fin k) → Q → Bool → CrossingOutcome Q) :=
    fun i ↦ M.twoWayBehavior (List.replicate (i.val + 1) a)
  have hnot_inj : ¬ Function.Injective g := by
    intro hinj
    have hcard := Fintype.card_le_of_injective g hinj
    simp only [Fintype.card_fin] at hcard
    omega
  rw [Function.Injective] at hnot_inj
  push Not at hnot_inj
  rcases hnot_inj with ⟨i, j, hij, hne⟩
  have hlt_or : i.val < j.val ∨ j.val < i.val := by
    have : i.val ≠ j.val := fun heq ↦ hne (Fin.ext heq)
    omega
  obtain ⟨p, d, hp, hd, hpd, hEq⟩ :
      ∃ p d : ℕ, 1 ≤ p ∧ 1 ≤ d ∧ p + d ≤ K + 1 ∧
        M.twoWayBehavior (List.replicate (p + d) a) = M.twoWayBehavior (List.replicate p a) := by
    rcases hlt_or with hlt | hlt
    · refine ⟨i.val + 1, j.val - i.val, by omega, by omega, by omega, ?_⟩
      have : i.val + 1 + (j.val - i.val) = j.val + 1 := by omega
      rw [this]
      exact hij.symm
    · refine ⟨j.val + 1, i.val - j.val, by omega, by omega, by omega, ?_⟩
      have : j.val + 1 + (i.val - j.val) = i.val + 1 := by omega
      rw [this]
      exact hij
  have hshift : ∀ r : ℕ,
      M.twoWayBehavior (List.replicate (p + r + d) a) =
        M.twoWayBehavior (List.replicate (p + r) a) := by
    intro r
    cases r with
    | zero => simpa using hEq
    | succ r =>
      have h1 : List.replicate (p + (r + 1) + d) a =
          List.replicate (p + d) a ++ List.replicate (r + 1) a := by
        rw [← List.replicate_add]; congr 1; omega
      have h2 : List.replicate (p + (r + 1)) a =
          List.replicate p a ++ List.replicate (r + 1) a := by
        rw [← List.replicate_add]
      rw [h1, h2]
      exact twoWayBehavior_append_congr M (by simp; omega) (by simp; omega)
        (by simp) (by simp) hEq rfl
  refine ⟨p, d, hp, hd, hpd, fun n q hn ↦ ?_⟩
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction q with
  | zero => simp
  | succ q ih =>
    have h1 : p + r + (q + 1) * d = p + (r + q * d) + d := by ring
    rw [h1, hshift (r + q * d)]
    have h2 : p + (r + q * d) = p + r + q * d := by ring
    rw [h2, ih]

private theorem localRun_matches_tape {k : ℕ} {α Q : Type*} (M : PebbleAutomaton k α Q)
    (u s v : List α) (c₀ : Cfg k (u ++ s ++ v).length Q)
    (hpeb_out : ∀ r, (c₀.pebbles r).val ≤ u.length ∨ u.length + s.length < (c₀.pebbles r).val)
    (q : Q) (pos : Fin s.length)
    (hstate : c₀.state = q) (hhead : c₀.head.val = u.length + 1 + pos.val) :
    ∀ n : ℕ,
      (∀ d < n, ∃ q' pos', localRun M (pebblesAvail c₀) s q pos d = .inside q' pos') →
      (let c := (M.step (u ++ s ++ v))^[n] c₀
       match localRun M (pebblesAvail c₀) s q pos n with
       | .inside q' pos' =>
         c.pebbles = c₀.pebbles ∧ c.state = q' ∧ c.head.val = u.length + 1 + pos'.val
       | .exitLeft q' => c.pebbles = c₀.pebbles ∧ c.state = q' ∧ c.head.val = u.length
       | .exitRight q' =>
         c.pebbles = c₀.pebbles ∧ c.state = q' ∧ c.head.val = u.length + s.length + 1
       | .halted q' => c.pebbles = c₀.pebbles ∧ c.state = q' ∧ c.state ∈ M.halting
       | .placed =>
         ∃ r, u.length < (c.pebbles r).val ∧ (c.pebbles r).val ≤ u.length + s.length) := by
  let w := u ++ s ++ v
  intro n
  induction n with
  | zero =>
    intro _
    simp [localRun, hstate, hhead]
  | succ n ih =>
    intro hstay
    rcases hstay n (Nat.lt_succ_self n) with ⟨qn, posn, hqn⟩
    have hih := ih (fun d hd ↦ hstay d (Nat.lt_trans hd (Nat.lt_succ_self n)))
    rw [hqn] at hih
    rcases hih with ⟨hpeb_n, hstate_n, hhead_n⟩
    set cn := (M.step w)^[n] c₀
    have hw : w.length = u.length + s.length + v.length := by
      simp only [w, List.length_append]
    have hAt : pebblesAtHead cn = ∅ := by
      ext r
      simp only [mem_pebblesAtHead_iff, Finset.notMem_empty, iff_false, not_and]
      intro hEq _
      have := hpeb_out r
      rw [hpeb_n, hhead_n] at hEq
      omega
    have hAv : pebblesAvail cn = pebblesAvail c₀ := by
      ext r; simp [mem_pebblesAvail_iff, hpeb_n]
    have hinner1 : 0 < cn.head.val := by omega
    have hinner2 : cn.head.val ≤ w.length := by simp only [w, List.length_append]; omega
    have htape : tapeAt w cn.head = .sym (s.get posn) := by
      rw [tapeAt_inner w cn.head hinner1 hinner2]
      congr 1
      have hidx : cn.head.val - 1 = u.length + posn.val := by omega
      simp only [List.get_eq_getElem, hidx, w, List.append_assoc]
      rw [List.getElem_append_right (by omega)]
      simp only [Nat.add_sub_cancel_left]
      rw [List.getElem_append_left posn.isLt]
    have hnext_local : localRun M (pebblesAvail c₀) s q pos (n + 1) =
        localStep M (pebblesAvail c₀) s (.inside qn posn) := by
      simp only [localRun, Function.iterate_succ_apply']
      exact congrArg (localStep M (pebblesAvail c₀) s) hqn
    rw [hnext_local]
    have hstep_n : (M.step w)^[n + 1] c₀ = M.step w cn := by
      rw [Function.iterate_succ_apply']
    rw [hstep_n]
    unfold localStep
    dsimp only
    by_cases hH : qn ∈ M.halting
    · have hH' : cn.state ∈ M.halting := hstate_n ▸ hH
      simp only [isHaltingDec_of_mem hH, ↓reduceIte]
      rw [step_of_mem_halting M w hH']
      exact ⟨hpeb_n, hstate_n, hH'⟩
    · have hH' : cn.state ∉ M.halting := hstate_n ▸ hH
      let res := M.δ qn (.sym (s.get posn)) ∅ (pebblesAvail c₀)
      have hstep_eq : M.step w cn =
          ⟨res.1, moveHead cn.head res.2.2.2,
            fun r ↦ if r ∈ res.2.1 then ⟨cn.head.val, Nat.lt_succ_of_le hinner2⟩
              else if r ∈ res.2.2.1 then ⟨0, Nat.zero_lt_succ _⟩ else cn.pebbles r⟩ := by
        rw [step_of_not_mem_halting M w hH']
        simp only [htape, hAt, hAv, hstate_n, hinner2, ↓reduceDIte]
        rfl
      simp only [isHaltingDec_of_not_mem hH, Bool.false_eq_true, ↓reduceIte]
      by_cases hP : res.2.1 = ∅
      · have hD : res.2.2.1 = pebblesAvail c₀ := by
          have hcons := M.pebble_conserved qn (.sym (s.get posn)) ∅ (pebblesAvail c₀)
            (Finset.disjoint_empty_left _)
          simp only [Finset.empty_union] at hcons
          change res.2.1 ∪ res.2.2.1 = pebblesAvail c₀ at hcons
          rw [hP, Finset.empty_union] at hcons
          exact hcons
        have hpeb_eq : (M.step w cn).pebbles = c₀.pebbles := by
          rw [hstep_eq]
          funext r
          dsimp only
          simp only [hP, Finset.notMem_empty, ↓reduceIte, hD, hpeb_n]
          by_cases hB : r ∈ pebblesAvail c₀
          · have h0 : (c₀.pebbles r).val = 0 := (mem_pebblesAvail_iff _ _).mp hB
            simp only [hB, ↓reduceIte]
            exact Fin.ext h0.symm
          · simp [hB]
        have hP' : (M.δ qn (.sym (s.get posn)) ∅ (pebblesAvail c₀)).2.1 = ∅ := hP
        simp only [hP', ne_eq, not_true_eq_false, ↓reduceIte]
        cases hdir : res.2.2.2 with
        | stay =>
          simp only
          exact ⟨hpeb_eq, by rw [hstep_eq], by rw [hstep_eq, hdir]; simp [hhead_n]⟩
        | left =>
          by_cases hpos : 0 < posn.val
          · simp only [hpos, ↓reduceIte]
            refine ⟨hpeb_eq, by rw [hstep_eq], ?_⟩
            rw [hstep_eq, hdir]; simp [hhead_n]; omega
          · simp only [hpos, ↓reduceIte]
            refine ⟨hpeb_eq, by rw [hstep_eq], ?_⟩
            rw [hstep_eq, hdir]; simp [hhead_n]; omega
        | right =>
          by_cases hpos : posn.val + 1 < s.length
          · simp only [hpos, ↓reduceDIte]
            refine ⟨hpeb_eq, by rw [hstep_eq], ?_⟩
            rw [hstep_eq, hdir]
            dsimp only
            rw [moveHead_right_val _ (by omega)]
            omega
          · simp only [hpos, ↓reduceDIte]
            refine ⟨hpeb_eq, by rw [hstep_eq], ?_⟩
            rw [hstep_eq, hdir]
            dsimp only
            rw [moveHead_right_val _ (by omega)]
            omega
      · have hP' : (M.δ qn (.sym (s.get posn)) ∅ (pebblesAvail c₀)).2.1 ≠ ∅ := hP
        simp only [ite_eq_left_of_eq_true _ _ (eq_true hP')]
        rw [hstep_eq]
        rcases Finset.nonempty_iff_ne_empty.mpr hP with ⟨r, hr⟩
        refine ⟨r, ?_, ?_⟩
        · simp [hr, hhead_n]; omega
        · simp [hr, hhead_n]; omega

private def OutsidePosRel (uLen s₁Len s₂Len : ℕ) (p₁ p₂ : ℕ) : Prop :=
  (p₁ ≤ uLen ∧ p₂ = p₁) ∨ (uLen + s₁Len < p₁ ∧ p₂ + s₁Len = p₁ + s₂Len)

/-- Replacing a pebble-free nonempty substring `s₁` by a nonempty substring `s₂` with the same
crossing behavior preserves halting and acceptance. -/
theorem accepts_iff_of_twoWayBehavior_eq_of_no_pebble {k : ℕ} {α Q : Type*} [Fintype Q]
    (M : PebbleAutomaton k α Q) {u s₁ s₂ v : List α}
    (hs₁ : 0 < s₁.length) (hs₂ : 0 < s₂.length)
    (hbeh : M.twoWayBehavior s₁ = M.twoWayBehavior s₂)
    (hHalt : M.Halts (u ++ s₁ ++ v))
    (hnoPeb : ∀ t r, ¬ (u.length < (M.run (u ++ s₁ ++ v) t).pebbles r ∧
        (M.run (u ++ s₁ ++ v) t).pebbles r ≤ u.length + s₁.length)) :
    M.Accepts (u ++ s₁ ++ v) ↔ M.Accepts (u ++ s₂ ++ v) := by
  classical
  let w₁ := u ++ s₁ ++ v
  let w₂ := u ++ s₂ ++ v
  have hw₁ : w₁.length = u.length + s₁.length + v.length := by simp only [w₁, List.length_append]
  have hw₂ : w₂.length = u.length + s₂.length + v.length := by simp only [w₂, List.length_append]
  rcases hHalt with ⟨tH, htH⟩
  have hsim : ∀ (rem : ℕ) (t₁ : ℕ) (c₂ : Cfg k w₂.length Q),
      tH - t₁ = rem → t₁ ≤ tH →
      (let c₁ := M.run w₁ t₁
       c₁.state = c₂.state ∧
       OutsidePosRel u.length s₁.length s₂.length c₁.head.val c₂.head.val ∧
       (∀ r, OutsidePosRel u.length s₁.length s₂.length (c₁.pebbles r).val (c₂.pebbles r).val)) →
      ∃ d : ℕ, ((M.step w₂)^[d] c₂).state = (M.run w₁ tH).state := by
    intro rem
    induction rem using Nat.strongRecOn with
    | ind rem ih =>
      intro t₁ c₂ hrem ht₁le hrel
      rcases hrel with ⟨hstate, hhead, hpeb⟩
      set c₁ := M.run w₁ t₁
      by_cases hH₁ : c₁.state ∈ M.halting
      · have hEq := M.run_eq_of_mem_halting w₁ hH₁ tH ht₁le
        exact ⟨0, by change c₂.state = (M.run w₁ tH).state; rw [← hstate, hEq]⟩
      · have ht₁_lt : t₁ < tH := by
          by_contra hge
          have heq : t₁ = tH := by omega
          exact hH₁ (by change (M.run w₁ t₁).state ∈ M.halting; rw [heq]; exact htH)
        have hH₂ : c₂.state ∉ M.halting := hstate ▸ hH₁
        have hAt : pebblesAtHead c₁ = pebblesAtHead c₂ := by
          ext r
          simp only [mem_pebblesAtHead_iff]
          rcases hhead with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
            rcases hpeb r with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩ <;> omega
        have hAv : pebblesAvail c₁ = pebblesAvail c₂ := by
          ext r
          simp only [mem_pebblesAvail_iff]
          rcases hpeb r with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩ <;> omega
        have htape : tapeAt w₁ c₁.head = tapeAt w₂ c₂.head := by
          rcases hhead with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · by_cases h0 : c₁.head.val = 0
            · have h0' : c₂.head.val = 0 := by omega
              rw [show c₁.head = ⟨0, by omega⟩ from Fin.ext h0,
                show c₂.head = ⟨0, by omega⟩ from Fin.ext h0', tapeAt_zero, tapeAt_zero]
            · rw [tapeAt_inner w₁ c₁.head (by omega) (by simp only [w₁, List.length_append]; omega),
                tapeAt_inner w₂ c₂.head (by omega) (by simp only [w₂, List.length_append]; omega)]
              congr 1
              simp only [List.get_eq_getElem, w₁, w₂, List.append_assoc]
              rw [List.getElem_append_left (by omega), List.getElem_append_left (by omega)]
              simp [h2]
          · by_cases hEnd : c₁.head.val = w₁.length + 1
            · have hEnd' : c₂.head.val = w₂.length + 1 := by
                simp only [w₁, w₂, List.length_append] at hEnd ⊢; omega
              rw [show c₁.head = ⟨w₁.length + 1, by omega⟩ from Fin.ext hEnd,
                show c₂.head = ⟨w₂.length + 1, by omega⟩ from Fin.ext hEnd',
                tapeAt_last, tapeAt_last]
            · have hle2 : c₂.head.val ≤ w₂.length := by
                simp only [w₂, List.length_append]
                simp only [w₁, List.length_append] at hEnd; omega
              rw [tapeAt_inner w₁ c₁.head (by omega) (by omega),
                tapeAt_inner w₂ c₂.head (by omega) hle2]
              congr 1
              simp only [List.get_eq_getElem, w₁, w₂, List.append_assoc]
              rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega),
                List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
              congr 1; omega
        let res := M.δ c₁.state (tapeAt w₁ c₁.head) (pebblesAtHead c₁) (pebblesAvail c₁)
        have hstep₁ : M.run w₁ (t₁ + 1) =
            ⟨res.1, moveHead c₁.head res.2.2.2,
              fun r ↦ if r ∈ res.2.1 then
                  if hle : c₁.head.val ≤ w₁.length then ⟨c₁.head.val, Nat.lt_succ_of_le hle⟩
                  else ⟨0, Nat.zero_lt_succ _⟩
                else if r ∈ res.2.2.1 then ⟨0, Nat.zero_lt_succ _⟩ else c₁.pebbles r⟩ := by
          rw [run_succ, step_of_not_mem_halting M w₁ hH₁]
        have hstep₂ : M.step w₂ c₂ =
            ⟨res.1, moveHead c₂.head res.2.2.2,
              fun r ↦ if r ∈ res.2.1 then
                  if hle : c₂.head.val ≤ w₂.length then ⟨c₂.head.val, Nat.lt_succ_of_le hle⟩
                  else ⟨0, Nat.zero_lt_succ _⟩
                else if r ∈ res.2.2.1 then ⟨0, Nat.zero_lt_succ _⟩ else c₂.pebbles r⟩ := by
          rw [step_of_not_mem_halting M w₂ hH₂]
          simp only [← hstate, ← htape, ← hAt, ← hAv]
          rfl
        have hpeb_next : ∀ r, OutsidePosRel u.length s₁.length s₂.length
            ((M.run w₁ (t₁ + 1)).pebbles r).val ((M.step w₂ c₂).pebbles r).val := by
          intro r
          rw [hstep₁, hstep₂]
          dsimp only
          by_cases hC : r ∈ res.2.1
          · simp only [hC, ↓reduceIte]
            by_cases hle1 : c₁.head.val ≤ w₁.length
            · have hle2 : c₂.head.val ≤ w₂.length := by
                simp only [w₁, w₂, List.length_append] at hle1 ⊢
                rcases hhead with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
              simp only [hle1, hle2, ↓reduceDIte]
              exact hhead
            · have hle2 : ¬ (c₂.head.val ≤ w₂.length) := by
                simp only [w₁, w₂, List.length_append] at hle1 ⊢
                rcases hhead with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
              simp only [hle1, hle2, ↓reduceDIte]
              exact Or.inl ⟨Nat.zero_le _, rfl⟩
          · by_cases hD : r ∈ res.2.2.1
            · simp only [hC, hD, ↓reduceIte]
              exact Or.inl ⟨Nat.zero_le _, rfl⟩
            · simp only [hC, hD, ↓reduceIte]
              exact hpeb r
        have hstate_next : (M.run w₁ (t₁ + 1)).state = (M.step w₂ c₂).state := by
          rw [hstep₁, hstep₂]
        by_cases hIn : u.length < (M.run w₁ (t₁ + 1)).head.val ∧
            (M.run w₁ (t₁ + 1)).head.val ≤ u.length + s₁.length
        · -- Entered `s₁`!
          let side : Bool := decide (res.2.2.2 = .left)
          have hhead1_entry : (M.run w₁ (t₁ + 1)).head.val =
              u.length + 1 + (entryPos hs₁ side).val := by
            rw [hstep₁] at hIn ⊢; dsimp only at hIn ⊢
            cases hdir : res.2.2.2 with
            | stay =>
              rw [hdir] at hIn; simp only [moveHead_stay] at hIn
              rcases hhead with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
            | left =>
              rw [hdir] at hIn; simp only [moveHead_left_val] at hIn
              have : side = true := by simp [side, hdir]
              simp only [this, entryPos, ↓reduceIte, moveHead_left_val]
              rcases hhead with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
            | right =>
              rw [hdir] at hIn
              have : side = false := by simp [side, hdir]
              simp only [this, entryPos, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
              rcases hhead with ⟨h1, _⟩ | ⟨h1, _⟩
              · rw [moveHead_right_val _ (by simp only [w₁, List.length_append]; omega)] at hIn ⊢
                omega
              · by_cases he : c₁.head.val = w₁.length + 1
                · rw [show c₁.head = ⟨w₁.length + 1, by omega⟩ from Fin.ext he,
                    moveHead_right_last] at hIn
                  simp only [w₁, List.length_append] at hIn; omega
                · rw [moveHead_right_val _ (by omega)] at hIn; omega
          have hhead2_entry : (M.step w₂ c₂).head.val =
              u.length + 1 + (entryPos hs₂ side).val := by
            rw [hstep₁] at hIn; rw [hstep₂]; dsimp only at hIn ⊢
            cases hdir : res.2.2.2 with
            | stay =>
              rw [hdir] at hIn; simp only [moveHead_stay] at hIn
              rcases hhead with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
            | left =>
              rw [hdir] at hIn; simp only [moveHead_left_val] at hIn
              have : side = true := by simp [side, hdir]
              simp only [this, entryPos, ↓reduceIte, moveHead_left_val]
              rcases hhead with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
            | right =>
              rw [hdir] at hIn
              have : side = false := by simp [side, hdir]
              simp only [this, entryPos, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
              rcases hhead with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · rw [moveHead_right_val _ (by simp only [w₁, List.length_append]; omega)] at hIn
                rw [moveHead_right_val _ (by simp only [w₂, List.length_append]; omega)]
                omega
              · by_cases he : c₁.head.val = w₁.length + 1
                · rw [show c₁.head = ⟨w₁.length + 1, by omega⟩ from Fin.ext he,
                    moveHead_right_last] at hIn
                  simp only [w₁, List.length_append] at hIn; omega
                · rw [moveHead_right_val _ (by omega)] at hIn; omega
          let B := pebblesAvail (M.run w₁ (t₁ + 1))
          have hAv_next : pebblesAvail (M.step w₂ c₂) = B := by
            ext r; simp only [B, mem_pebblesAvail_iff]
            rcases hpeb_next r with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩ <;> omega
          have hpeb_out₁ : ∀ r, ((M.run w₁ (t₁ + 1)).pebbles r).val ≤ u.length ∨
              u.length + s₁.length < ((M.run w₁ (t₁ + 1)).pebbles r).val := by
            intro r; rcases hpeb_next r with ⟨hp1, _⟩ | ⟨hp1, _⟩
            · exact Or.inl hp1
            · exact Or.inr hp1
          have hpeb_out₂ : ∀ r, ((M.step w₂ c₂).pebbles r).val ≤ u.length ∨
              u.length + s₂.length < ((M.step w₂ c₂).pebbles r).val := by
            intro r; rcases hpeb_next r with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩
            · exact Or.inl (by omega)
            · exact Or.inr (by omega)
          -- Local run in `s₁` cannot loop (since `M` halts at `tH`) and cannot place a pebble
          have hnotLoop : M.twoWayBehavior s₁ B res.1 side ≠ .loop := by
            intro hloop
            have hall := (twoWayBehavior_eq_loop_iff M hs₁ B res.1 side).mp hloop
            have hm := localRun_matches_tape M u s₁ v (M.run w₁ (t₁ + 1)) hpeb_out₁ res.1
              (entryPos hs₁ side) (by rw [hstep₁]) hhead1_entry (tH - (t₁ + 1)) (fun d _ ↦ hall d)
            rcases hall (tH - (t₁ + 1)) with ⟨qn, posn, hqn⟩
            rw [hqn] at hm
            have hrun_eq : (M.step w₁)^[tH - (t₁ + 1)] (M.run w₁ (t₁ + 1)) = M.run w₁ tH := by
              rw [← run_add, Nat.sub_add_cancel (show t₁ + 1 ≤ tH by omega)]
            -- Check at `tH - (t₁ + 1) + 1`: `localRun` stays inside, contradicting `htH`
            have hqn_next : localRun M B s₁ res.1 (entryPos hs₁ side) (tH - (t₁ + 1) + 1) =
                localStep M B s₁ (.inside qn posn) := by
              simp only [localRun, Function.iterate_succ_apply']
              exact congrArg (localStep M B s₁) hqn
            have hH_qn : qn ∈ M.halting := by
              rw [← hm.2.1, hrun_eq]; exact htH
            rcases hall (tH - (t₁ + 1) + 1) with ⟨q2, p2, hq2⟩
            rw [hqn_next] at hq2
            unfold localStep at hq2
            simp only [isHaltingDec_of_mem hH_qn, ↓reduceIte] at hq2
            cases hq2
          -- Find first terminal step `d₁` of `localRun` in `s₁`
          have hex_d₁ : ∃ d₁ : ℕ,
              (∀ u' < d₁, ∃ q' pos',
                localRun M B s₁ res.1 (entryPos hs₁ side) u' = .inside q' pos') ∧
              (∀ q' pos', localRun M B s₁ res.1 (entryPos hs₁ side) d₁ ≠ .inside q' pos') := by
            have hnotall : ∃ d₁, ∀ q' pos',
                localRun M B s₁ res.1 (entryPos hs₁ side) d₁ ≠ .inside q' pos' := by
              by_contra hall
              push Not at hall
              exact hnotLoop ((twoWayBehavior_eq_loop_iff M hs₁ B res.1 side).mpr hall)
            refine ⟨Nat.find hnotall, fun u' hu' ↦ ?_, Nat.find_spec hnotall⟩
            by_contra hnot
            push Not at hnot
            exact Nat.find_min hnotall hu' hnot
          rcases hex_d₁ with ⟨d₁, hd₁_stay, hd₁_term⟩
          have hm₁ := localRun_matches_tape M u s₁ v (M.run w₁ (t₁ + 1)) hpeb_out₁ res.1
            (entryPos hs₁ side) (by rw [hstep₁]) hhead1_entry d₁ hd₁_stay
          have hrun_d₁ : (M.step w₁)^[d₁] (M.run w₁ (t₁ + 1)) = M.run w₁ (d₁ + (t₁ + 1)) := by
            rw [← run_add]
          have hle_tH_of_exit :
              (∀ q', localRun M B s₁ res.1 (entryPos hs₁ side) d₁ ≠ .halted q') →
              d₁ + (t₁ + 1) ≤ tH := by
            intro hne_halt
            by_contra hgt
            have hprev : tH - (t₁ + 1) < d₁ := by omega
            rcases hd₁_stay (tH - (t₁ + 1)) hprev with ⟨qn, posn, hqn⟩
            have hm_tH := localRun_matches_tape M u s₁ v (M.run w₁ (t₁ + 1)) hpeb_out₁ res.1
              (entryPos hs₁ side) (by rw [hstep₁]) hhead1_entry (tH - (t₁ + 1))
              (fun d hd ↦ hd₁_stay d (lt_trans hd hprev))
            rw [hqn] at hm_tH
            have hrun_eq : (M.step w₁)^[tH - (t₁ + 1)] (M.run w₁ (t₁ + 1)) = M.run w₁ tH := by
              rw [← run_add, Nat.sub_add_cancel (show t₁ + 1 ≤ tH by omega)]
            have hH_qn : qn ∈ M.halting := by
              have hst_tH : ((M.step w₁)^[tH - (t₁ + 1)] (M.run w₁ (t₁ + 1))).state = qn :=
                hm_tH.2.1
              rw [← hst_tH, hrun_eq]; exact htH
            have hqn_next : localRun M B s₁ res.1 (entryPos hs₁ side) (tH - (t₁ + 1) + 1) =
                localStep M B s₁ (.inside qn posn) := by
              simp only [localRun, Function.iterate_succ_apply']
              exact congrArg (localStep M B s₁) hqn
            have hlt_or : tH - (t₁ + 1) + 1 = d₁ ∨ tH - (t₁ + 1) + 1 < d₁ := by omega
            rcases hlt_or with hEq | hlt
            · rw [hEq] at hqn_next
              unfold localStep at hqn_next
              simp only [isHaltingDec_of_mem hH_qn, ↓reduceIte] at hqn_next
              exact hne_halt qn hqn_next
            · rcases hd₁_stay (tH - (t₁ + 1) + 1) hlt with ⟨q2, p2, hq2⟩
              rw [hqn_next] at hq2; unfold localStep at hq2
              simp only [isHaltingDec_of_mem hH_qn, ↓reduceIte] at hq2; cases hq2
          have hex_d₂ : ∀ (τ : CrossingOutcome Q) (cτ : LocalCfg Q s₂.length),
              outcomeToLocal τ = some cτ →
              M.twoWayBehavior s₁ B res.1 side = τ →
              ∃ d₂ : ℕ,
                (∀ u' < d₂, ∃ q'' pos'',
                  localRun M B s₂ res.1 (entryPos hs₂ side) u' = .inside q'' pos'') ∧
                localRun M B s₂ res.1 (entryPos hs₂ side) d₂ = cτ := by
            intro τ cτ hτ hbeh₁
            have hbeh₂ : M.twoWayBehavior s₂ B res.1 side = τ := by rw [← hbeh, hbeh₁]
            rcases (twoWayBehavior_eq_terminal_iff M hs₂ B res.1 side hτ).mp hbeh₂ with
              ⟨d₂', hd₂'⟩
            have hnot_in : ∀ q'' pos'', cτ ≠ .inside q'' pos'' := by
              cases τ <;> simp only [outcomeToLocal, Option.some.injEq, reduceCtorEq] at hτ
              all_goals subst hτ; intro _ _ h; cases h
            rcases first_terminal_of_reaches M B s₂ res.1 (entryPos hs₂ side) hnot_in hd₂' with
              ⟨d₂, _, hd₂_stay, hd₂_eq⟩
            exact ⟨d₂, hd₂_stay, hd₂_eq⟩
          have hd₁_pos : 1 ≤ d₁ := by
            cases d₁ with
            | zero => exact absurd rfl (hd₁_term res.1 (entryPos hs₁ side))
            | succ _ => omega
          cases hσ : localRun M B s₁ res.1 (entryPos hs₁ side) d₁ with
          | inside q' pos' => exact absurd hσ (hd₁_term q' pos')
          | placed =>
            rw [hσ, hrun_d₁] at hm₁
            rcases hm₁ with ⟨r, hr1, hr2⟩
            exact absurd ⟨hr1, hr2⟩ (hnoPeb (d₁ + (t₁ + 1)) r)
          | halted q' =>
            rw [hσ, hrun_d₁] at hm₁
            rcases hm₁ with ⟨_, hst_q', hH_q'⟩
            have hbeh₁ : M.twoWayBehavior s₁ B res.1 side = .halted q' :=
              (twoWayBehavior_eq_terminal_iff M hs₁ B res.1 side rfl).mpr ⟨d₁, hσ⟩
            rcases hex_d₂ (.halted q') (.halted q') rfl hbeh₁ with ⟨d₂, hd₂_stay, hd₂_eq⟩
            have hm₂ := localRun_matches_tape M u s₂ v (M.step w₂ c₂) hpeb_out₂ res.1
              (entryPos hs₂ side) (by rw [hstep₂]) hhead2_entry d₂
              (by simpa [hAv_next] using hd₂_stay)
            rw [hAv_next, hd₂_eq] at hm₂
            have hEq_tH : (M.run w₁ tH).state = q' := by
              have h1 := M.run_eq_of_mem_halting w₁ hH_q' (max (d₁ + (t₁ + 1)) tH)
                (le_max_left _ _)
              have h2 := M.run_eq_of_mem_halting w₁ htH (max (d₁ + (t₁ + 1)) tH)
                (le_max_right _ _)
              rw [← hst_q', ← congrArg Cfg.state (h1.symm.trans h2)]
            refine ⟨d₂ + 1, ?_⟩
            rw [Function.iterate_succ_apply, hm₂.2.1, hEq_tH]
          | exitLeft q' =>
            rw [hσ, hrun_d₁] at hm₁
            rcases hm₁ with ⟨hpeb_d₁, hst_q', hhead_d₁⟩
            have hd₁_le_tH := hle_tH_of_exit (fun _ h ↦ by rw [hσ] at h; cases h)
            have hbeh₁ : M.twoWayBehavior s₁ B res.1 side = .exitLeft q' :=
              (twoWayBehavior_eq_terminal_iff M hs₁ B res.1 side rfl).mpr ⟨d₁, hσ⟩
            rcases hex_d₂ (.exitLeft q') (.exitLeft q') rfl hbeh₁ with ⟨d₂, hd₂_stay, hd₂_eq⟩
            have hm₂ := localRun_matches_tape M u s₂ v (M.step w₂ c₂) hpeb_out₂ res.1
              (entryPos hs₂ side) (by rw [hstep₂]) hhead2_entry d₂
              (by simpa [hAv_next] using hd₂_stay)
            rw [hAv_next, hd₂_eq] at hm₂
            rcases hm₂ with ⟨hpeb_d₂, hst_d₂, hhead_d₂⟩
            change ((M.step w₂)^[d₂] (M.step w₂ c₂)).head.val = u.length at hhead_d₂
            rcases ih (tH - (d₁ + (t₁ + 1))) (by omega) (d₁ + (t₁ + 1))
                ((M.step w₂)^[d₂] (M.step w₂ c₂)) rfl hd₁_le_tH
                ⟨hst_q'.trans hst_d₂.symm, Or.inl ⟨by omega, by omega⟩,
                  fun r ↦ by rw [hpeb_d₁, hpeb_d₂]; exact hpeb_next r⟩ with ⟨d₃, hd₃⟩
            refine ⟨d₃ + d₂ + 1, ?_⟩
            simpa [Function.iterate_add_apply, Function.iterate_succ_apply] using hd₃
          | exitRight q' =>
            rw [hσ, hrun_d₁] at hm₁
            rcases hm₁ with ⟨hpeb_d₁, hst_q', hhead_d₁⟩
            have hd₁_le_tH := hle_tH_of_exit (fun _ h ↦ by rw [hσ] at h; cases h)
            have hbeh₁ : M.twoWayBehavior s₁ B res.1 side = .exitRight q' :=
              (twoWayBehavior_eq_terminal_iff M hs₁ B res.1 side rfl).mpr ⟨d₁, hσ⟩
            rcases hex_d₂ (.exitRight q') (.exitRight q') rfl hbeh₁ with ⟨d₂, hd₂_stay, hd₂_eq⟩
            have hm₂ := localRun_matches_tape M u s₂ v (M.step w₂ c₂) hpeb_out₂ res.1
              (entryPos hs₂ side) (by rw [hstep₂]) hhead2_entry d₂
              (by simpa [hAv_next] using hd₂_stay)
            rw [hAv_next, hd₂_eq] at hm₂
            rcases hm₂ with ⟨hpeb_d₂, hst_d₂, hhead_d₂⟩
            change ((M.step w₂)^[d₂] (M.step w₂ c₂)).head.val =
              u.length + s₂.length + 1 at hhead_d₂
            rcases ih (tH - (d₁ + (t₁ + 1))) (by omega) (d₁ + (t₁ + 1))
                ((M.step w₂)^[d₂] (M.step w₂ c₂)) rfl hd₁_le_tH
                ⟨hst_q'.trans hst_d₂.symm, Or.inr ⟨by omega, by omega⟩,
                  fun r ↦ by rw [hpeb_d₁, hpeb_d₂]; exact hpeb_next r⟩ with ⟨d₃, hd₃⟩
            refine ⟨d₃ + d₂ + 1, ?_⟩
            simpa [Function.iterate_add_apply, Function.iterate_succ_apply] using hd₃
        · -- Stayed outside `s₁`!
          have hhead_next : OutsidePosRel u.length s₁.length s₂.length
              (M.run w₁ (t₁ + 1)).head.val (M.step w₂ c₂).head.val := by
            rw [hstep₁, hstep₂]
            dsimp only
            cases hdir : res.2.2.2 with
            | stay => simpa only [moveHead_stay] using hhead
            | left =>
              simp only [moveHead_left_val]
              rcases hhead with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · exact Or.inl ⟨by omega, by omega⟩
              · by_cases hbound : c₁.head.val = u.length + s₁.length + 1
                · rw [hstep₁, hdir] at hIn
                  simp only [moveHead_left_val] at hIn
                  omega
                · exact Or.inr ⟨by omega, by omega⟩
            | right =>
              rcases hhead with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · by_cases hbound : c₁.head.val = u.length
                · rw [hstep₁, hdir] at hIn
                  rw [moveHead_right_val _ (by simp only [w₁, List.length_append]; omega)] at hIn
                  omega
                · rw [moveHead_right_val _ (by simp only [w₁, List.length_append]; omega),
                    moveHead_right_val _ (by simp only [w₂, List.length_append]; omega)]
                  exact Or.inl ⟨by omega, by omega⟩
              · by_cases hEnd : c₁.head.val = w₁.length + 1
                · have hEnd2 : c₂.head.val = w₂.length + 1 := by
                    simp only [w₁, w₂, List.length_append] at hEnd ⊢; omega
                  rw [show c₁.head = ⟨w₁.length + 1, by omega⟩ from Fin.ext hEnd,
                    show c₂.head = ⟨w₂.length + 1, by omega⟩ from Fin.ext hEnd2,
                    moveHead_right_last, moveHead_right_last]
                  exact Or.inr ⟨by dsimp only; omega, by dsimp only; omega⟩
                · have hlt2 : c₂.head.val + 1 < w₂.length + 2 := by
                    simp only [w₂, List.length_append]
                    simp only [w₁, List.length_append] at hEnd; omega
                  rw [moveHead_right_val _ (by omega), moveHead_right_val _ hlt2]
                  exact Or.inr ⟨by omega, by omega⟩
          rcases ih (tH - (t₁ + 1)) (by omega) (t₁ + 1) (M.step w₂ c₂) rfl (by omega)
              ⟨hstate_next, hhead_next, hpeb_next⟩ with ⟨d, hd⟩
          exact ⟨d + 1, by simpa [Function.iterate_succ_apply] using hd⟩
  rcases hsim tH 0 (M.initCfg w₂.length) (Nat.sub_zero tH) (Nat.zero_le tH)
      ⟨by simp, Or.inl ⟨by simp, by simp⟩,
        fun _ ↦ Or.inl ⟨by simp, by simp⟩⟩ with ⟨d, hd⟩
  have hrun_d : M.run w₂ d = (M.step w₂)^[d] (M.initCfg w₂.length) := by
    rw [← run_zero, ← run_add, Nat.add_zero]
  have hd_halt : (M.run w₂ d).state ∈ M.halting := by rw [hrun_d, hd]; exact htH
  constructor
  · rintro ⟨t₁, ht₁⟩
    have h1 := M.run_eq_of_mem_halting w₁ htH (max t₁ tH) (le_max_right _ _)
    have h2 := M.run_eq_of_mem_halting w₁ (M.accepting_subset_halting ht₁) (max t₁ tH)
      (le_max_left _ _)
    have hacc : (M.run w₁ tH).state ∈ M.accepting := (h1.symm.trans h2).symm ▸ ht₁
    exact ⟨d, by rw [hrun_d, hd]; exact hacc⟩
  · rintro ⟨t₂, ht₂⟩
    have h1 := M.run_eq_of_mem_halting w₂ hd_halt (max t₂ d) (le_max_right _ _)
    have h2 := M.run_eq_of_mem_halting w₂ (M.accepting_subset_halting ht₂) (max t₂ d)
      (le_max_left _ _)
    have hacc : (M.run w₂ d).state ∈ M.accepting := (h1.symm.trans h2).symm ▸ ht₂
    exact ⟨tH, by rw [← hd, ← hrun_d]; exact hacc⟩

end TwoWayBehavior

end PebbleAutomaton

end CslibFrontier.Computability.Automata
