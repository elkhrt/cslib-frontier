module

public import CslibFrontier.Init
public import Cslib.Computability.Machines.Turing.SingleTape.Deterministic
import Mathlib.Tactic

/-!
# Totalized Stepping and Output Extraction for Single-Tape Turing Machines

This module provides a totalized single-step transition function `totalStep` for deterministic
single-tape Turing machines (`Cslib.Turing.SingleTapeTM`) that leaves halted configurations
(`state = none`) stationary, together with iterated space-usage bounds, reachability identities
connecting `Relation.RelatesInSteps` and `Relation.RelatesWithinSteps` to iterated `totalStep`,
non-blank right-tape extraction `biTapeRightList` for `Cslib.Turing.BiTape`, and instance
reindexing for `Cslib.Turing.SingleTapeTM.PolyTimeComputable`.

## Main definitions

* `CslibFrontier.Turing.SingleTapeTM.totalStep`: totalized transition function fixing halted states.
* `CslibFrontier.Turing.SingleTapeTM.biTapeRightList`: extracts `StackTape.cons t.head t.right`
  as a `List (Option Symbol)`.
* `CslibFrontier.Turing.SingleTapeTM.reindexPolyTimeComputable`: transports `PolyTimeComputable`
  between arbitrary `Inhabited` and `Fintype` instances on the alphabet.

## Main results

* `CslibFrontier.Turing.SingleTapeTM.iterate_totalStep_spaceUsed_le`: after `i` totalized steps,
  `spaceUsed` grows by at most `i`.
* `CslibFrontier.Turing.SingleTapeTM.iterate_totalStep_eq_of_relatesWithinSteps`: if a machine
  reaches a halted configuration within `B ≤ T` steps, then `T` iterations of `totalStep` reach
  that exact halted configuration.
* `CslibFrontier.Turing.SingleTapeTM.biTapeRightList_mk₁`: `biTapeRightList (BiTape.mk₁ ys)`
  equals `ys.map some`.
-/

public section

namespace CslibFrontier.Turing.SingleTapeTM

/-- Totalized transition step on `tm.Cfg`: once in `state = none`, remains stationary. -/
@[expose] def totalStep {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
    (tm : Cslib.Turing.SingleTapeTM Symbol) (cfg : tm.Cfg) : tm.Cfg :=
  (tm.step cfg).getD cfg

@[simp]
theorem totalStep_halt {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
    (tm : Cslib.Turing.SingleTapeTM Symbol) (t : Cslib.Turing.BiTape Symbol) :
    totalStep tm ⟨none, t⟩ = ⟨none, t⟩ := rfl

/-- Whenever `tm.TransitionRelation c₁ c₂` holds, `totalStep tm c₁ = c₂`. -/
theorem totalStep_of_transition {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
    {tm : Cslib.Turing.SingleTapeTM Symbol} {c₁ c₂ : tm.Cfg}
    (h : tm.TransitionRelation c₁ c₂) : totalStep tm c₁ = c₂ := by
  change tm.step c₁ = some c₂ at h
  simp only [totalStep, h, Option.getD_some]

/-- Each totalized step increases `spaceUsed` by at most `1`. -/
theorem totalStep_spaceUsed_le {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
    (tm : Cslib.Turing.SingleTapeTM Symbol) (cfg : tm.Cfg) :
    (totalStep tm cfg).spaceUsed ≤ cfg.spaceUsed + 1 := by
  unfold totalStep
  cases h : tm.step cfg with
  | none => simp
  | some cfg' => exact Cslib.Turing.SingleTapeTM.Cfg.spaceUsed_step cfg cfg' h

/-- Iterating `totalStep` `i` times increases `spaceUsed` by at most `i`. -/
theorem iterate_totalStep_spaceUsed_le {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
    (tm : Cslib.Turing.SingleTapeTM Symbol) (cfg : tm.Cfg) (i : ℕ) :
    ((totalStep tm)^[i] cfg).spaceUsed ≤ cfg.spaceUsed + i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    have hstep := totalStep_spaceUsed_le tm ((totalStep tm)^[i] cfg)
    omega

/-- Any halted configuration is a fixed point of iterated `totalStep`. -/
theorem iterate_totalStep_halt {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
    (tm : Cslib.Turing.SingleTapeTM Symbol) (t : Cslib.Turing.BiTape Symbol) (i : ℕ) :
    (totalStep tm)^[i] ⟨none, t⟩ = ⟨none, t⟩ := by
  induction i with
  | zero => rfl
  | succ i ih => simp [Function.iterate_succ_apply', ih]

/-- `m`-step transition reachability implies `(totalStep tm)^[m] c₁ = c₂`. -/
theorem iterate_totalStep_of_relatesInSteps {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
    {tm : Cslib.Turing.SingleTapeTM Symbol} {c₁ c₂ : tm.Cfg} {m : ℕ}
    (h : Relation.RelatesInSteps tm.TransitionRelation c₁ c₂ m) :
    (totalStep tm)^[m] c₁ = c₂ := by
  induction h with
  | refl => rfl
  | tail c' c'' k _ hstep ih =>
    rw [Function.iterate_succ_apply', ih, totalStep_of_transition hstep]

/-- Reaching a halted configuration `⟨none, tHalt⟩` within `B ≤ T` steps implies
`(totalStep tm)^[T] c₀ = ⟨none, tHalt⟩`. -/
theorem iterate_totalStep_eq_of_relatesWithinSteps {Symbol : Type} [Inhabited Symbol]
    [Fintype Symbol] {tm : Cslib.Turing.SingleTapeTM Symbol} {c₀ : tm.Cfg}
    {tHalt : Cslib.Turing.BiTape Symbol} {B T : ℕ}
    (hRel : Relation.RelatesWithinSteps tm.TransitionRelation c₀ ⟨none, tHalt⟩ B)
    (hBT : B ≤ T) :
    (totalStep tm)^[T] c₀ = ⟨none, tHalt⟩ := by
  obtain ⟨m, hmB, hmSteps⟩ := hRel
  have hSplit : T = (T - m) + m := by omega
  rw [hSplit, Function.iterate_add_apply, iterate_totalStep_of_relatesInSteps hmSteps,
    iterate_totalStep_halt]

/-- Right half of a `BiTape` starting at the head cell, normalized via `StackTape.cons`. -/
@[expose] def biTapeRightList {Symbol : Type*} (t : Cslib.Turing.BiTape Symbol) :
    List (Option Symbol) :=
  (Cslib.Turing.StackTape.cons t.head t.right).toList

@[simp]
theorem biTapeRightList_mk₁ {Symbol : Type*} (ys : List Symbol) :
    biTapeRightList (Cslib.Turing.BiTape.mk₁ ys) = ys.map some := by
  cases ys with
  | nil => simp [biTapeRightList, Cslib.Turing.BiTape.mk₁, Cslib.Turing.BiTape.nil]
  | cons y yt =>
    simp [biTapeRightList, Cslib.Turing.BiTape.mk₁, Cslib.Turing.StackTape.mapSome]

/-- Transports `Cslib.Turing.SingleTapeTM.PolyTimeComputable f` across arbitrary `Inhabited` and
`Fintype` instances on `Symbol`. -/
@[expose] def reindexPolyTimeComputable {Symbol : Type} (i₁ i₂ : Inhabited Symbol)
    (f₁ f₂ : Fintype Symbol) {f : List Symbol → List Symbol}
    (hf : @Cslib.Turing.SingleTapeTM.PolyTimeComputable Symbol i₁ f₁ f) :
    @Cslib.Turing.SingleTapeTM.PolyTimeComputable Symbol i₂ f₂ f :=
  let tc₁ := @Cslib.Turing.SingleTapeTM.PolyTimeComputable.toTimeComputable Symbol i₁ f₁ f hf
  let tm₁ := @Cslib.Turing.SingleTapeTM.TimeComputable.tm Symbol i₁ f₁ f tc₁
  let tm₂ : @Cslib.Turing.SingleTapeTM Symbol i₂ f₂ :=
    @Cslib.Turing.SingleTapeTM.mk Symbol i₂ f₂
      (@Cslib.Turing.SingleTapeTM.State Symbol i₁ f₁ tm₁)
      (@Cslib.Turing.SingleTapeTM.stateFintype Symbol i₁ f₁ tm₁)
      (@Cslib.Turing.SingleTapeTM.q₀ Symbol i₁ f₁ tm₁)
      (@Cslib.Turing.SingleTapeTM.tr Symbol i₁ f₁ tm₁)
  let mapCfg : @Cslib.Turing.SingleTapeTM.Cfg Symbol i₁ f₁ tm₁ →
      @Cslib.Turing.SingleTapeTM.Cfg Symbol i₂ f₂ tm₂ := fun c =>
    @Cslib.Turing.SingleTapeTM.Cfg.mk Symbol i₂ f₂ tm₂
      (@Cslib.Turing.SingleTapeTM.Cfg.state Symbol i₁ f₁ tm₁ c)
      (@Cslib.Turing.SingleTapeTM.Cfg.BiTape Symbol i₁ f₁ tm₁ c)
  let tc₂ : @Cslib.Turing.SingleTapeTM.TimeComputable Symbol i₂ f₂ f :=
    @Cslib.Turing.SingleTapeTM.TimeComputable.mk Symbol i₂ f₂ f
      tm₂
      (@Cslib.Turing.SingleTapeTM.TimeComputable.timeBound Symbol i₁ f₁ f tc₁)
      (fun a =>
        @Relation.RelatesWithinSteps.map _ _
          (@Cslib.Turing.SingleTapeTM.TransitionRelation Symbol i₁ f₁ tm₁)
          (@Cslib.Turing.SingleTapeTM.TransitionRelation Symbol i₂ f₂ tm₂)
          mapCfg
          (fun c₁ c₂ hstep => by
            cases c₁ with
            | mk st bt =>
              cases st with
              | none => cases hstep
              | some q =>
                let r := @Cslib.Turing.SingleTapeTM.tr Symbol i₁ f₁ tm₁ q bt.head
                change some (@Cslib.Turing.SingleTapeTM.Cfg.mk Symbol i₁ f₁ tm₁ r.2
                  ((bt.write r.1.symbol).optionMove r.1.movement)) = some c₂ at hstep
                cases hstep
                rfl)
          _ _ _
          (@Cslib.Turing.SingleTapeTM.TimeComputable.outputsFunInTime Symbol i₁ f₁ f tc₁ a))
  @Cslib.Turing.SingleTapeTM.PolyTimeComputable.mk Symbol i₂ f₂ f tc₂
    (@Cslib.Turing.SingleTapeTM.PolyTimeComputable.poly Symbol i₁ f₁ f hf)
    (@Cslib.Turing.SingleTapeTM.PolyTimeComputable.bounds Symbol i₁ f₁ f hf)

end CslibFrontier.Turing.SingleTapeTM
