module

public import CslibFrontier.Computability.Complexity.Classes.Time
public import CslibFrontier.Computability.Complexity.Reduction
public import Mathlib.Computability.Ackermann
public import Mathlib.Computability.Primrec.Basic
import Mathlib.Tactic.Linarith

/-!
# The Complexity Class `ACKERMANN` (`F_ω`)

This module defines the non-elementary complexity class `ACKERMANN` (`F_ω` in Schmitz's
fast-growing complexity hierarchy) using `Cslib.Complexity.DTIME`, Mathlib's Ackermann
function `ack`, and primitive recursive bounds `Primrec`, together with its closure under
polynomial-time many-one reductions and the inclusion `P ⊆ ACKERMANN`.

## Main definitions

* `PaperLib.ACKERMANN`: decision problems decidable in time `O(ack (p n) (p n))` for some
  primitive recursive function `p : ℕ → ℕ`.
* `PaperLib.AckermannHard`: polynomial-time hardness for `ACKERMANN`.
* `PaperLib.AckermannComplete`: membership in and polynomial-time hardness for `ACKERMANN`.

## Main results

* `PaperLib.P_subset_ACKERMANN`: every polynomial-time decidable problem lies in `ACKERMANN`.
* `PaperLib.mem_ACKERMANN_of_polyTimeReducible`: `ACKERMANN` is closed under polynomial-time
  many-one reductions.
* `PaperLib.AckermannHard.trans`: `ACKERMANN`-hardness transfers along polynomial-time
  reductions.
-/

public section

namespace CslibFrontier

open Cslib.Complexity

/-- The complexity class `ACKERMANN` (`F_ω`): problems decidable deterministically within
time `O(ack (p n) (p n))` for some primitive recursive function `p : ℕ → ℕ`. -/
def ACKERMANN {α : Type*} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ p : ℕ → ℕ, Primrec p ∧ A ∈ DTIME enc (fun n => ack (p n) (p n))}

/-- A decision problem `B` is `ACKERMANN`-hard under polynomial-time many-one reductions. -/
abbrev AckermannHard {β : Type*} (encB : β ↪ List Bool) (B : Set β) : Prop :=
  PolyTimeHard @ACKERMANN encB B

/-- A decision problem `B` is `ACKERMANN`-complete under polynomial-time many-one
reductions. -/
abbrev AckermannComplete {β : Type} (encB : β ↪ List Bool) (B : Set β) : Prop :=
  PolyTimeComplete @ACKERMANN encB B

/-- Every problem in `P` lies in `ACKERMANN`. -/
theorem P_subset_ACKERMANN {α : Type*} {enc : α ↪ List Bool} :
    P enc ⊆ ACKERMANN enc := by
  intro A hA
  obtain ⟨k, hDT⟩ := mem_P_iff_exists_mem_DTIME.mp hA
  let p : ℕ → ℕ := fun n => n ^ k + k + 1
  have hpow : ∀ m : ℕ, Primrec (fun n : ℕ => n ^ m) := by
    intro m; induction m with
    | zero => simpa using Primrec.const 1
    | succ m ihm => simpa [pow_succ] using Primrec.nat_mul.comp ihm Primrec.id
  have hp : Primrec p :=
    Primrec.nat_add.comp (Primrec.nat_add.comp (hpow k) (Primrec.const k)) (Primrec.const 1)
  refine ⟨p, hp, DTIME_mono (fun n => ?_) hDT⟩
  have hlt : p n < ack (p n) (p n) := by
    calc p n < ack 0 (p n) := by simp
      _ ≤ ack (p n) (p n) := ack_mono_left (p n) (Nat.zero_le _)
  have hle : n ^ k ≤ p n := by dsimp [p]; omega
  exact hle.trans (le_of_lt hlt)

/-- `ACKERMANN` is closed under polynomial-time many-one reductions. -/
theorem mem_ACKERMANN_of_polyTimeReducible {α β : Type}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {A : Set α} {B : Set β}
    (hred : PolyTimeReducible encA encB A B) (hB : B ∈ ACKERMANN encB) :
    A ∈ ACKERMANN encA := by
  obtain ⟨g, hg, hmem⟩ := hred
  obtain ⟨p, hp, hDT⟩ := hB
  obtain ⟨t, s, ht, hs, hcomp⟩ := hg
  obtain ⟨ct, dt, htd⟩ := Cslib.polynomiallyBounded_iff_le.mp ht
  obtain ⟨cs, ds, hsd⟩ := Cslib.polynomiallyBounded_iff_le.mp hs
  -- Bound both the time `t n` and output length `|encB (g a)| ≤ t |encA a|` by a polynomial `q n`:
  let q : ℕ → ℕ := fun n => (ct + cs + 1) * (n + 1) ^ (max dt ds) + 1
  have hpow_succ : ∀ m : ℕ, Primrec (fun n : ℕ => (n + 1) ^ m) := by
    intro m; induction m with
    | zero => simpa using Primrec.const 1
    | succ m ihm => simpa [pow_succ] using Primrec.nat_mul.comp ihm Primrec.succ
  have hq_prim : Primrec q :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const (ct + cs + 1)) (hpow_succ (max dt ds)))
      (Primrec.const 1)
  have hq_ge : ∀ a : α,
      t (encA a).length ≤ q (encA a).length ∧
      s (encA a).length ≤ q (encA a).length ∧
      (encB (g a)).length ≤ q (encA a).length := by
    intro a
    have h1 := htd (encA a).length
    have h2 := hsd (encA a).length
    have hlen := hcomp.length_le a
    have hm1 : ct * ((encA a).length + 1) ^ dt ≤
        (ct + cs + 1) * ((encA a).length + 1) ^ max dt ds :=
      Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_left _ _))
    have hm2 : cs * ((encA a).length + 1) ^ ds ≤
        (ct + cs + 1) * ((encA a).length + 1) ^ max dt ds :=
      Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_right _ _))
    dsimp [q]
    omega
  have hcomp_O : Turing.MultiTapeTM.ComputableInO g encA encB
      (fun a => q (encA a).length) (fun a => q (encA a).length) := by
    refine Turing.MultiTapeTM.ComputableInO.of_bounds hcomp 1
      (fun a => by have := (hq_ge a).1; omega)
      (fun a => by have := (hq_ge a).2.1; omega)
      (fun a => by have := (hq_ge a).2.2; omega)
  -- Replace `p` by its running maximum `pMax` so it is monotone and still primitive recursive!
  let pMax : ℕ → ℕ := Nat.rec (p 0) (fun m prev => max prev (p (m + 1)))
  have hpMax_prim : Primrec pMax :=
    Primrec.nat_rec₁ (p 0)
      (Primrec.nat_max.comp Primrec.snd (hp.comp (Primrec.succ.comp Primrec.fst)))
  have hpMax_mono : Monotone pMax := by
    refine monotone_nat_of_le_succ (fun m => ?_)
    exact le_max_left _ _
  have hp_le_pMax : ∀ m : ℕ, p m ≤ pMax m := by
    intro m
    cases m with
    | zero => exact le_rfl
    | succ m => exact le_max_right _ _
  let r : ℕ → ℕ := fun n => q n + pMax (q n)
  have hr_prim : Primrec r := Primrec.nat_add.comp hq_prim (hpMax_prim.comp hq_prim)
  have hset : A = g ⁻¹' B := Set.ext hmem
  rw [hset]
  refine ⟨r, hr_prim, preimage_mem_DTIME (C := 2) hDT hcomp_O (fun a => ?_)⟩
  have hlen_le : (encB (g a)).length ≤ q (encA a).length := (hq_ge a).2.2
  have h1 : q (encA a).length ≤ ack (r (encA a).length) (r (encA a).length) := by
    have hlt : q (encA a).length < ack 0 (q (encA a).length) := by simp
    have hle : q (encA a).length ≤ r (encA a).length := Nat.le_add_right _ _
    exact (le_of_lt hlt).trans (ack_le_ack (Nat.zero_le _) hle)
  have h2 : ack (p (encB (g a)).length) (p (encB (g a)).length) ≤
      ack (r (encA a).length) (r (encA a).length) := by
    have hp1 : p (encB (g a)).length ≤ pMax (q (encA a).length) :=
      (hp_le_pMax _).trans (hpMax_mono hlen_le)
    have hp2 : pMax (q (encA a).length) ≤ r (encA a).length := Nat.le_add_left _ _
    exact ack_le_ack (hp1.trans hp2) (hp1.trans hp2)
  omega

/-- `ACKERMANN`-hardness transfers along polynomial-time many-one reductions. -/
theorem AckermannHard.trans {α β : Type*} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {A : Set α} {B : Set β} (hA : AckermannHard encA A)
    (hAB : PolyTimeReducible encA encB A B) : AckermannHard encB B :=
  PolyTimeHard.trans hA hAB

/-- The empty problem is in `ACKERMANN`. -/
@[simp] theorem empty_mem_ACKERMANN {α : Type*} {enc : α ↪ List Bool} :
    (∅ : Set α) ∈ ACKERMANN enc :=
  P_subset_ACKERMANN empty_mem_P

/-- The universal problem is in `ACKERMANN`. -/
@[simp] theorem univ_mem_ACKERMANN {α : Type*} {enc : α ↪ List Bool} :
    (Set.univ : Set α) ∈ ACKERMANN enc :=
  P_subset_ACKERMANN univ_mem_P

end CslibFrontier
