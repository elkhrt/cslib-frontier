/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.Modular
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.Bounds
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.HaltingTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Counting.Deterministic
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.BranchingProgramDeterminant
public import CslibFrontier.Computability.Complexity.Classes.LogSpace.DeterminantInclusion

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Layered Algebraic Branching Programs and $\mathrm{Mod}_k\mathrm{L} \subseteq \mathrm{DET}_k$

This module formalizes the layered algebraic branching program to determinant reduction over
commutative rings (via `Matrix.eq_det_submatrix_sub_one_of_eq_single_add_vecMul`), the inclusions
$\mathrm{L} \subseteq \mathrm{UL} \subseteq \mathrm{Mod}_k\mathrm{L}$, and the modular counting
logspace inclusion $\mathrm{Mod}_k\mathrm{L} \subseteq \mathrm{DET}_k \subseteq \mathrm{DET}$ for
every $k \ge 2$ under standard Lean axioms.

## Main definitions

* `Cslib.Complexity.walkVec`: multi-step row-vector walk weights across a sequence of
  `T` transition matrices `Fin T → Matrix (Fin M) (Fin M) R`.
* `Cslib.Complexity.layeredDAGSpec`: compiler turning `T` single-literal `M × M`
  transition matrix specifications over `ZMod k`, a start vertex, and an accepting weight vector
  into a single `((T + 1) * M + 1) × ((T + 1) * M + 1)` `SingleVarMatrixSpec`.
* `Cslib.Complexity.ctmStepMult`, `Cslib.Complexity.ctmStepSpec`:
  transition-occurrence multiplicity matrix of a `MultiTapeCTM` on the compact logspace
  configuration box.

## Main results

* `Cslib.Complexity.L_subset_UL`, `Cslib.Complexity.L_subset_ModL`:
  $\mathrm{L} \subseteq \mathrm{UL}$ and (for $k \ge 2$) $\mathrm{L} \subseteq
  \mathrm{Mod}_k\mathrm{L}$.
* `Cslib.Complexity.det_layeredDAGSpec_eval`: the determinant of
  `layeredDAGSpec` equals the total `T`-step walk weight from `start` to `acceptVec`.
* `ModL_subset_DETkOn`,
  `ModL_encBits_subset_DETk`,
  `ModL_subset_DETOn`: for every $k \ge 2$,
  $\mathrm{Mod}_k\mathrm{L} \subseteq \mathrm{DET}_k \subseteq \mathrm{DET}$.
-/

public section

namespace Cslib.Complexity

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open scoped Matrix
open _root_.Turing _root_.Turing.MultiTapeNTM _root_.Turing.MultiTapeNTM.ConfigurationGraph

/-! ### Arithmetic helpers on `ZMod k` -/

theorem zmod_one_ne_zero {k : ℕ} (hk : 2 ≤ k) : (1 : ZMod k) ≠ 0 := by
  intro h
  have hv : ((1 : ℕ) : ZMod k).val = (0 : ZMod k).val := by simpa using congrArg ZMod.val h
  rw [ZMod.val_natCast, ZMod.val_zero, Nat.mod_eq_of_lt (by omega)] at hv
  omega

theorem zmod_natCast_ne_zero_iff {k : ℕ} [NeZero k] (c : ℕ) :
    (c : ZMod k) ≠ 0 ↔ c % k ≠ 0 := by
  refine not_congr ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hv := congrArg ZMod.val h
    rwa [ZMod.val_natCast, ZMod.val_zero] at hv
  · apply ZMod.val_injective k
    rw [ZMod.val_natCast, ZMod.val_zero, h]

/-! ### Deterministic logspace embeds into `UL` and `ModL k` -/

private theorem toNTM_ofDeterministic_ctm {k_tapes : ℕ} {State : Type}
    (tm : MultiTapeTM k_tapes Bool State) :
    (MultiTapeCTM.ofDeterministic tm).toNTM = tm.toMultiTapeNTM := by
  cases tm with
  | mk ntm det =>
    simp only [MultiTapeCTM.toNTM, MultiTapeCTM.ofDeterministic, List.mem_singleton]
    congr with q s w a : 4
    apply propext
    rw [Equiv.symm_apply_eq]
    exact eq_comm.trans (MultiTapeTM.tr_iff (tm := ⟨ntm, det⟩)).symm

/-- **$\mathrm{L} \subseteq \mathrm{UL}$**: every deterministic logspace decision problem is
unambiguously countable in logarithmic space via `Turing.MultiTapeCTM.ofDeterministic`. -/
theorem L_subset_UL {α : Type} {enc : α ↪ List Bool} :
    L enc ⊆ UL enc := by
  rintro A ⟨f, ⟨t, c, k_tapes, State, hfinite, tm, htm⟩, hA⟩
  let g : α → ℕ := fun a ↦ if f a then 1 else 0
  refine ⟨g, ⟨k_tapes, State, hfinite, MultiTapeCTM.ofDeterministic tm, c, fun a ↦ ?_⟩,
    fun a ↦ by dsimp only [g]; split_ifs <;> omega,
    fun a ↦ by rw [hA a]; dsimp only [g]; cases f a <;> simp⟩
  obtain ⟨⟨u, hhalt, hout⟩, -, hspace⟩ := htm a
  refine ⟨by rwa [toNTM_ofDeterministic_ctm], u, ?_, ?_⟩
  · exact (MultiTapeCTM.haltsWithin_ofDeterministic_iff tm u _).mpr hhalt
  · unfold MultiTapeCTM.acceptCount
    change g a =
      (MultiTapeCTM.ofDeterministic tm).branchCount (· == [true]) u (tm.initCfg (enc a))
    rw [MultiTapeCTM.branchCount_ofDeterministic tm _ u _ hhalt]
    change (if f a = true then 1 else 0) =
      if ((tm.runFrom (tm.initCfg (enc a)) u).output == [true]) = true then 1 else 0
    rw [hout]
    cases f a <;> rfl

/-- **$\mathrm{L} \subseteq \mathrm{Mod}_k\mathrm{L}$** for every modulus `k ≥ 2`. -/
theorem L_subset_ModL {α : Type} {enc : α ↪ List Bool} {k : ℕ} (hk : 2 ≤ k) :
    L enc ⊆ ModL k enc :=
  L_subset_UL.trans (UL_subset_ModL hk)

/-! ### Layered single-literal algebraic branching program to determinant compiler -/

/-- Row-vector walk weights across `s ≤ T` steps of a `T`-step layered transition sequence
`P : Fin T → Matrix (Fin M) (Fin M) R` starting at `start : Fin M`. -/
@[expose]
def walkVec {R : Type*} [CommRing R] {T M : ℕ}
    (start : Fin M) (P : Fin T → Matrix (Fin M) (Fin M) R) : ∀ s ≤ T, Fin M → R
  | 0, _ => Pi.single start 1
  | s + 1, hs => walkVec start P s (Nat.le_of_succ_le hs) ᵥ* P ⟨s, hs⟩

@[simp]
theorem walkVec_zero {R : Type*} [CommRing R] {T M : ℕ}
    (start : Fin M) (P : Fin T → Matrix (Fin M) (Fin M) R) (h0 : 0 ≤ T) :
    walkVec start P 0 h0 = Pi.single start 1 :=
  rfl

@[simp]
theorem walkVec_succ {R : Type*} [CommRing R] {T M : ℕ}
    (start : Fin M) (P : Fin T → Matrix (Fin M) (Fin M) R) (s : ℕ) (hs : s + 1 ≤ T) :
    walkVec start P (s + 1) hs =
      walkVec start P s (Nat.le_of_succ_le hs) ᵥ* P ⟨s, hs⟩ :=
  rfl

private theorem walkVec_congr {R : Type*} [CommRing R] {T M : ℕ}
    (start : Fin M) (P : Fin T → Matrix (Fin M) (Fin M) R)
    {s₁ s₂ : ℕ} (hs₁ : s₁ ≤ T) (hs₂ : s₂ ≤ T) (hs : s₁ = s₂)
    {u₁ u₂ : Fin M} (hu : u₁ = u₂) :
    walkVec start P s₁ hs₁ u₁ = walkVec start P s₂ hs₂ u₂ := by
  subst hs hu
  rfl

theorem walkVec_const_dot_eq_pow_mulVec {R : Type*} [CommRing R] {T M : ℕ}
    (start : Fin M) (A : Matrix (Fin M) (Fin M) R) (s : ℕ) (hs : s ≤ T) (e : Fin M → R) :
    (∑ u : Fin M, walkVec start (fun _ ↦ A) s hs u * e u) = ((A ^ s) *ᵥ e) start := by
  induction s generalizing e with
  | zero =>
    rw [walkVec_zero, pow_zero, Matrix.one_mulVec, Finset.sum_eq_single start]
    · simp
    · intro u _ hne; simp [Pi.single_eq_of_ne hne]
    · simp
  | succ s ih =>
    dsimp only [walkVec, Matrix.vecMul, dotProduct]
    have hswap :
        (∑ v : Fin M, (∑ u : Fin M, walkVec start (fun _ ↦ A) s (Nat.le_of_succ_le hs) u * A u v) *
          e v) =
        ∑ u : Fin M, walkVec start (fun _ ↦ A) s (Nat.le_of_succ_le hs) u *
          (A *ᵥ e) u := by
      simp_rw [Finset.sum_mul, mul_assoc]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun u _ ↦ ?_
      rw [← Finset.mul_sum]
      rfl
    rw [hswap, ih (Nat.le_of_succ_le hs) (A *ᵥ e), Matrix.mulVec_mulVec, ← pow_succ]

/-- Single-literal matrix specification of dimension `(T + 1) * M + 1` whose determinant over
`ZMod k` equals the `T`-step walk weight from `start` to `acceptVec` across `stepSpec`. -/
def layeredDAGSpec {k n T M : ℕ} (hM : 0 < M) (start : Fin M)
    (stepSpec : Fin T → SingleVarMatrixSpec k n M) (acceptVec : Fin M → ZMod k) :
    SingleVarMatrixSpec k n ((T + 1) * M + 1) where
  readIdx row col :=
    if row.val = col.val + 1 then none
    else if row.val = 0 then none
    else if hstep : row.val - 1 < T * M then
      let p := row.val - 1
      let s : Fin T := ⟨p / M, Nat.div_lt_of_lt_mul (by nlinarith)⟩
      let u : Fin M := ⟨p % M, Nat.mod_lt _ hM⟩
      if hcol : (s.val + 1) * M ≤ col.val ∧ col.val < (s.val + 2) * M then
        (stepSpec s).readIdx u ⟨col.val - (s.val + 1) * M, by
          have : (s.val + 2) * M = (s.val + 1) * M + M := by ring
          omega⟩
      else none
    else none
  valFalse row col :=
    if row.val = col.val + 1 then -1
    else if row.val = 0 then
      if col.val = start.val then 1 else 0
    else if hstep : row.val - 1 < T * M then
      let p := row.val - 1
      let s : Fin T := ⟨p / M, Nat.div_lt_of_lt_mul (by nlinarith)⟩
      let u : Fin M := ⟨p % M, Nat.mod_lt _ hM⟩
      if hcol : (s.val + 1) * M ≤ col.val ∧ col.val < (s.val + 2) * M then
        (stepSpec s).valFalse u ⟨col.val - (s.val + 1) * M, by
          have : (s.val + 2) * M = (s.val + 1) * M + M := by ring
          omega⟩
      else 0
    else
      let u : Fin M := ⟨row.val - (1 + T * M), by
        have hr := row.isLt
        have : (T + 1) * M = T * M + M := by ring
        omega⟩
      if col.val = (T + 1) * M then acceptVec u else 0
  valTrue row col :=
    if row.val = col.val + 1 then -1
    else if row.val = 0 then
      if col.val = start.val then 1 else 0
    else if hstep : row.val - 1 < T * M then
      let p := row.val - 1
      let s : Fin T := ⟨p / M, Nat.div_lt_of_lt_mul (by nlinarith)⟩
      let u : Fin M := ⟨p % M, Nat.mod_lt _ hM⟩
      if hcol : (s.val + 1) * M ≤ col.val ∧ col.val < (s.val + 2) * M then
        (stepSpec s).valTrue u ⟨col.val - (s.val + 1) * M, by
          have : (s.val + 2) * M = (s.val + 1) * M + M := by ring
          omega⟩
      else 0
    else
      let u : Fin M := ⟨row.val - (1 + T * M), by
        have hr := row.isLt
        have : (T + 1) * M = T * M + M := by ring
        omega⟩
      if col.val = (T + 1) * M then acceptVec u else 0

/-- **Determinant evaluation of `layeredDAGSpec`**: for every Boolean assignment `x : Fin n → Bool`,
`((layeredDAGSpec hM start stepSpec acceptVec).eval x).det` equals the total `T`-step walk weight
from `start` to `acceptVec`. -/
theorem det_layeredDAGSpec_eval {k n T M : ℕ} (hM : 0 < M) (start : Fin M)
    (stepSpec : Fin T → SingleVarMatrixSpec k n M) (acceptVec : Fin M → ZMod k)
    (x : Fin n → Bool) :
    ((layeredDAGSpec hM start stepSpec acceptVec).eval x).det =
      ∑ u : Fin M, walkVec start (fun t ↦ (stepSpec t).eval x) T le_rfl u * acceptVec u := by
  let m := (T + 1) * M + 1
  let P : Fin T → Matrix (Fin M) (Fin M) (ZMod k) := fun t ↦ (stepSpec t).eval x
  let W : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod k) := fun i j ↦
    if i.val = 0 then
      if j.val = 1 + start.val then 1 else 0
    else if hstep : i.val - 1 < T * M then
      let p := i.val - 1
      let s : Fin T := ⟨p / M, Nat.div_lt_of_lt_mul (by nlinarith)⟩
      let u : Fin M := ⟨p % M, Nat.mod_lt _ hM⟩
      if hj : 1 + (s.val + 1) * M ≤ j.val ∧ j.val < 1 + (s.val + 2) * M then
        P s u ⟨j.val - (1 + (s.val + 1) * M), by
          have : (s.val + 2) * M = (s.val + 1) * M + M := by ring
          omega⟩
      else 0
    else if hT : i.val < 1 + (T + 1) * M then
      let u : Fin M := ⟨i.val - (1 + T * M), by
        have : (T + 1) * M = T * M + M := by ring
        omega⟩
      if j.val = 1 + (T + 1) * M then acceptVec u else 0
    else 0
  have hW_upper : ∀ i j : Fin (m + 1), j ≤ i → W i j = 0 := by
    intro i j hji
    have hle : j.val ≤ i.val := hji
    dsimp only [W]
    by_cases hi0 : i.val = 0
    · simp only [hi0, ↓reduceIte]
      split_ifs with hj
      · omega
      · rfl
    · simp only [hi0, ↓reduceIte]
      by_cases hstep : i.val - 1 < T * M
      · simp only [hstep, ↓reduceDIte]
        let s_val := (i.val - 1) / M
        have hrem := Nat.div_add_mod (i.val - 1) M
        have hmod := Nat.mod_lt (i.val - 1) hM
        have hi_lt : i.val < 1 + (s_val + 1) * M := by
          have : (s_val + 1) * M = M * ((i.val - 1) / M) + M := by dsimp [s_val]; ring
          omega
        split_ifs with hj
        · exfalso; dsimp only [s_val] at hi_lt; omega
        · rfl
      · simp only [hstep, ↓reduceDIte]
        split_ifs with hT hj
        · omega
        · rfl
        · rfl
  have hW_of_zero {i j : Fin (m + 1)} (hi0 : i.val = 0) :
      W i j = if j.val = 1 + start.val then 1 else 0 := by
    dsimp only [W]; rw [ite_eq_left hi0]
  have hW_step {i j : Fin (m + 1)} (hi0 : i.val ≠ 0) (hstep : i.val - 1 < T * M) :
      W i j =
        if hj : 1 + ((i.val - 1) / M + 1) * M ≤ j.val ∧
            j.val < 1 + ((i.val - 1) / M + 2) * M then
          P ⟨(i.val - 1) / M, Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hstep)⟩
            ⟨(i.val - 1) % M, Nat.mod_lt _ hM⟩
            ⟨j.val - (1 + ((i.val - 1) / M + 1) * M), by
              have : ((i.val - 1) / M + 2) * M = ((i.val - 1) / M + 1) * M + M := by ring
              omega⟩
        else 0 := by
    dsimp only [W]; rw [ite_eq_right hi0, dite_eq_left hstep]
  have hW_last {i j : Fin (m + 1)} (hi0 : i.val ≠ 0) (hnot : ¬(i.val - 1 < T * M)) :
      W i j =
        if hT : i.val < 1 + (T + 1) * M then
          if j.val = 1 + (T + 1) * M then
            acceptVec ⟨i.val - (1 + T * M), by
              have : (T + 1) * M = T * M + M := by ring
              omega⟩
          else 0
        else 0 := by
    dsimp only [W]; rw [ite_eq_right hi0, dite_eq_right hnot]
  have hsub : (layeredDAGSpec hM start stepSpec acceptVec).eval x =
      (W - 1).submatrix Fin.castSucc Fin.succ := by
    ext row col
    have hdiag_iff : (row.castSucc = col.succ) ↔ row.val = col.val + 1 := by
      simp [Fin.ext_iff]
    by_cases hdiag : row.val = col.val + 1
    · have hrc : row.castSucc = col.succ := hdiag_iff.mpr hdiag
      have hW0 : W col.succ col.succ = 0 := hW_upper col.succ col.succ le_rfl
      rw [SingleVarMatrixSpec.eval_apply]
      dsimp only [layeredDAGSpec]
      simp only [hdiag, ↓reduceIte, Matrix.submatrix_apply, Matrix.sub_apply,
        hrc, hW0, Matrix.one_apply_eq, zero_sub]
    · have hrc : row.castSucc ≠ col.succ := fun h ↦ hdiag (hdiag_iff.mp h)
      have h1 : (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod k)) row.castSucc col.succ = 0 :=
        Matrix.one_apply_ne hrc
      simp only [Matrix.submatrix_apply, Matrix.sub_apply, h1, sub_zero]
      by_cases hr0 : row.val = 0
      · have hr_read : (layeredDAGSpec hM start stepSpec acceptVec).readIdx row col = none := by
          dsimp only [layeredDAGSpec]
          rw [ite_eq_right hdiag, ite_eq_left hr0]
        have hr_false : (layeredDAGSpec hM start stepSpec acceptVec).valFalse row col =
            if col.val = start.val then 1 else 0 := by
          dsimp only [layeredDAGSpec]
          rw [ite_eq_right hdiag, ite_eq_left hr0]
        rw [SingleVarMatrixSpec.eval_apply, hr_read, hr_false, hW_of_zero (by simp [hr0])]
        simp only [Fin.val_succ]
        by_cases hc : col.val = start.val
        · rw [ite_eq_left hc, ite_eq_left (by omega : col.val + 1 = 1 + start.val)]
        · rw [ite_eq_right hc, ite_eq_right (by omega : col.val + 1 ≠ 1 + start.val)]
      · by_cases hstep : row.val - 1 < T * M
        · let s : Fin T :=
            ⟨(row.val - 1) / M, Nat.div_lt_of_lt_mul (by nlinarith)⟩
          let u : Fin M := ⟨(row.val - 1) % M, Nat.mod_lt _ hM⟩
          by_cases hcol : ((row.val - 1) / M + 1) * M ≤ col.val ∧
              col.val < ((row.val - 1) / M + 2) * M
          · have hsub_lt : col.val - ((row.val - 1) / M + 1) * M < M := by
              have : ((row.val - 1) / M + 2) * M = ((row.val - 1) / M + 1) * M + M := by ring
              omega
            let v : Fin M := ⟨col.val - ((row.val - 1) / M + 1) * M, hsub_lt⟩
            have hr_read : (layeredDAGSpec hM start stepSpec acceptVec).readIdx row col =
                (stepSpec s).readIdx u v := by
              dsimp only [layeredDAGSpec, s, u, v]
              rw [ite_eq_right hdiag, ite_eq_right hr0, dite_eq_left hstep, dite_eq_left hcol]
            have hr_false : (layeredDAGSpec hM start stepSpec acceptVec).valFalse row col =
                (stepSpec s).valFalse u v := by
              dsimp only [layeredDAGSpec, s, u, v]
              rw [ite_eq_right hdiag, ite_eq_right hr0, dite_eq_left hstep, dite_eq_left hcol]
            have hr_true : (layeredDAGSpec hM start stepSpec acceptVec).valTrue row col =
                (stepSpec s).valTrue u v := by
              dsimp only [layeredDAGSpec, s, u, v]
              rw [ite_eq_right hdiag, ite_eq_right hr0, dite_eq_left hstep, dite_eq_left hcol]
            have hW_val : W row.castSucc col.succ = (stepSpec s).eval x u v := by
              rw [hW_step (by simp [hr0]) (by simpa using hstep)]
              simp only [Fin.val_castSucc, Fin.val_succ]
              rw [dite_eq_left ⟨by omega, by omega⟩]
              change (stepSpec s).eval x u _ = (stepSpec s).eval x u v
              congr 1; ext; dsimp only [v]; omega
            rw [SingleVarMatrixSpec.eval_apply, hr_read, hr_false, hr_true, hW_val,
              SingleVarMatrixSpec.eval_apply]
          · have hr_read : (layeredDAGSpec hM start stepSpec acceptVec).readIdx row col = none := by
              dsimp only [layeredDAGSpec]
              rw [ite_eq_right hdiag, ite_eq_right hr0, dite_eq_left hstep, dite_eq_right hcol]
            have hr_false : (layeredDAGSpec hM start stepSpec acceptVec).valFalse row col = 0 := by
              dsimp only [layeredDAGSpec]
              rw [ite_eq_right hdiag, ite_eq_right hr0, dite_eq_left hstep, dite_eq_right hcol]
            have hW_val : W row.castSucc col.succ = 0 := by
              rw [hW_step (by simp [hr0]) (by simpa using hstep)]
              simp only [Fin.val_castSucc, Fin.val_succ]
              rw [dite_eq_right (by omega)]
            rw [SingleVarMatrixSpec.eval_apply, hr_read, hr_false, hW_val]
        · have hrow_lt : row.val < 1 + (T + 1) * M := by
            have : row.val < (T + 1) * M + 1 := row.isLt
            omega
          have hr_read : (layeredDAGSpec hM start stepSpec acceptVec).readIdx row col = none := by
            dsimp only [layeredDAGSpec]
            rw [ite_eq_right hdiag, ite_eq_right hr0, dite_eq_right hstep]
          have hr_false : (layeredDAGSpec hM start stepSpec acceptVec).valFalse row col =
              if col.val = (T + 1) * M then
                acceptVec ⟨row.val - (1 + T * M), by
                  have hr := row.isLt
                  have : (T + 1) * M = T * M + M := by ring
                  omega⟩
              else 0 := by
            dsimp only [layeredDAGSpec]
            rw [ite_eq_right hdiag, ite_eq_right hr0, dite_eq_right hstep]
          rw [SingleVarMatrixSpec.eval_apply, hr_read, hr_false,
            hW_last (by simp [hr0]) (by simpa using hstep)]
          simp only [Fin.val_castSucc, Fin.val_succ]
          rw [dite_eq_left hrow_lt]
          by_cases hc : col.val = (T + 1) * M
          · rw [ite_eq_left hc, ite_eq_left (by omega : col.val + 1 = 1 + (T + 1) * M)]
          · rw [ite_eq_right hc, ite_eq_right (by omega : col.val + 1 ≠ 1 + (T + 1) * M)]
  let q : Fin (m + 1) → ZMod k := fun j ↦
    if hj0 : j.val = 0 then 1
    else if hjL : j.val - 1 < (T + 1) * M then
      let p := j.val - 1
      walkVec start P (p / M)
        (Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by nlinarith)))
        ⟨p % M, Nat.mod_lt _ hM⟩
    else ∑ u : Fin M, walkVec start P T le_rfl u * acceptVec u
  have hq_of_zero {j : Fin (m + 1)} (hj0 : j.val = 0) : q j = 1 := by
    dsimp only [q]; rw [dite_eq_left hj0]
  have hq_layer {j : Fin (m + 1)} (hj0 : j.val ≠ 0) (hjL : j.val - 1 < (T + 1) * M) :
      q j = walkVec start P ((j.val - 1) / M)
        (Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by nlinarith)))
        ⟨(j.val - 1) % M, Nat.mod_lt _ hM⟩ := by
    dsimp only [q]; rw [dite_eq_right hj0, dite_eq_left hjL]
  have hq_sink {j : Fin (m + 1)} (hj0 : j.val ≠ 0) (hjL : ¬(j.val - 1 < (T + 1) * M)) :
      q j = ∑ u : Fin M, walkVec start P T le_rfl u * acceptVec u := by
    dsimp only [q]; rw [dite_eq_right hj0, dite_eq_right hjL]
  have hq : q = Pi.single 0 1 + q ᵥ* W := by
    funext j
    simp only [Pi.add_apply, Matrix.vecMul, dotProduct]
    by_cases hj0 : j.val = 0
    · obtain rfl : j = 0 := Fin.ext hj0
      have hsum0 : (∑ i : Fin (m + 1), q i * W i 0) = 0 :=
        Finset.sum_eq_zero fun i _ ↦ by
          rw [hW_upper i 0 (Nat.zero_le _), mul_zero]
      rw [hsum0, add_zero, Pi.single_eq_same, hq_of_zero rfl]
    · have hj_ne0 : j ≠ 0 := fun h ↦ hj0 (congrArg Fin.val h)
      rw [Pi.single_eq_of_ne hj_ne0, zero_add]
      by_cases hjL : j.val - 1 < (T + 1) * M
      · obtain ⟨s, hs_def⟩ : ∃ s, (j.val - 1) / M = s := ⟨_, rfl⟩
        obtain ⟨v, hv_def⟩ : ∃ v : Fin M,
            (⟨(j.val - 1) % M, Nat.mod_lt _ hM⟩ : Fin M) = v := ⟨_, rfl⟩
        have hv_mod : (j.val - 1) % M = v.val := congrArg Fin.val hv_def
        have hv_lt : v.val < M := v.isLt
        have hs_le : s ≤ T := by
          rw [← hs_def]
          exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by nlinarith))
        have hj_val : j.val = 1 + s * M + v.val := by
          have hdm := Nat.div_add_mod (j.val - 1) M
          rw [hs_def, hv_mod, Nat.mul_comm M s] at hdm
          omega
        rw [hq_layer hj0 hjL, walkVec_congr start P _ hs_le hs_def hv_def]
        rcases Nat.eq_zero_or_pos s with hs0 | hs_pos
        · have hj_val0 : j.val = 1 + v.val := by
            have : s * M = 0 := by rw [hs0, zero_mul]
            omega
          have hwalk0 : walkVec start P s hs_le v =
              (Pi.single start (1 : ZMod k) : Fin M → ZMod k) v := by
            rw [walkVec_congr start P hs_le (Nat.zero_le T) hs0 rfl, walkVec_zero]
          rw [hwalk0, Finset.sum_eq_single (0 : Fin (m + 1))]
          · rw [hq_of_zero rfl, one_mul, hW_of_zero rfl]
            by_cases hv : v = start
            · subst hv
              rw [ite_eq_left hj_val0, Pi.single_eq_same]
            · have hne : j.val ≠ 1 + start.val := fun h ↦ hv (Fin.ext (by omega))
              rw [ite_eq_right hne, Pi.single_eq_of_ne hv]
          · intro i _ hi0
            suffices hW0 : W i j = 0 by rw [hW0, mul_zero]
            have hi_ne : i.val ≠ 0 := fun h ↦ hi0 (Fin.ext h)
            by_cases hstep : i.val - 1 < T * M
            · rw [hW_step hi_ne hstep, dite_eq_right]
              intro hj_in
              have hM_le : M ≤ ((i.val - 1) / M + 1) * M :=
                Nat.le_mul_of_pos_left M (Nat.succ_pos _)
              omega
            · rw [hW_last hi_ne hstep]
              by_cases hT : i.val < 1 + (T + 1) * M
              · rw [dite_eq_left hT, ite_eq_right]
                intro hj_s
                have hM_le : M ≤ (T + 1) * M := Nat.le_mul_of_pos_left M (Nat.succ_pos T)
                omega
              · rw [dite_eq_right hT]
          · simp
        · obtain ⟨s', hs_eq⟩ : ∃ s', s = s' + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
          have hs'_lt : s' < T := by omega
          let embed (u : Fin M) : Fin (m + 1) :=
            ⟨1 + s' * M + u.val, by
              have hu := u.isLt
              dsimp only [m]
              nlinarith⟩
          have hembed_inj : Function.Injective embed := fun u₁ u₂ h ↦
            Fin.ext (by have := congrArg Fin.val h; dsimp only [embed] at this; omega)
          have hsum_eq :
              (∑ i : Fin (m + 1), q i * W i j) =
                ∑ u : Fin M, q (embed u) * W (embed u) j := by
            rw [← Finset.sum_image (f := fun i ↦ q i * W i j) (fun u₁ _ u₂ _ h ↦ hembed_inj h)]
            refine (Finset.sum_subset (Finset.subset_univ _) fun i _ hnot ↦ ?_).symm
            rw [Finset.mem_image] at hnot
            suffices hW0 : W i j = 0 by rw [hW0, mul_zero]
            by_cases hi0 : i.val = 0
            · rw [hW_of_zero hi0, ite_eq_right]
              intro hstart
              have hst_lt : start.val < M := start.isLt
              have hM_le : M ≤ s * M := Nat.le_mul_of_pos_left M hs_pos
              omega
            · by_cases hstep : i.val - 1 < T * M
              · rw [hW_step hi0 hstep]
                by_cases hj_in : 1 + ((i.val - 1) / M + 1) * M ≤ j.val ∧
                    j.val < 1 + ((i.val - 1) / M + 2) * M
                · exfalso
                  obtain ⟨qi, hqi⟩ : ∃ qi, (i.val - 1) / M = qi := ⟨_, rfl⟩
                  rw [hqi] at hj_in
                  have hsi : qi = s' := by
                    have hlow : qi ≤ s' := by
                      by_contra hgt
                      have hmul : (s' + 2) * M ≤ (qi + 1) * M :=
                        Nat.mul_le_mul_right M (by omega)
                      have hexp : (s' + 2) * M = s * M + M := by rw [hs_eq]; ring
                      omega
                    have hhigh : s' ≤ qi := by
                      by_contra hlt'
                      have hmul : (qi + 2) * M ≤ (s' + 1) * M :=
                        Nat.mul_le_mul_right M (by omega)
                      have hexp : (s' + 1) * M = s * M := by rw [hs_eq]
                      omega
                    omega
                  let ui : Fin M := ⟨(i.val - 1) % M, Nat.mod_lt _ hM⟩
                  have hi_eq : embed ui = i := Fin.ext <| by
                    have hdm := Nat.div_add_mod (i.val - 1) M
                    rw [hqi, hsi, Nat.mul_comm M s'] at hdm
                    dsimp only [embed, ui]
                    omega
                  exact hnot ⟨ui, Finset.mem_univ ui, hi_eq⟩
                · rw [dite_eq_right hj_in]
              · rw [hW_last hi0 hstep]
                by_cases hT : i.val < 1 + (T + 1) * M
                · rw [dite_eq_left hT, ite_eq_right]
                  intro hj_s
                  have hmul : (s + 1) * M ≤ (T + 1) * M :=
                    Nat.mul_le_mul_right M (Nat.succ_le_succ hs_le)
                  have hexp : (s + 1) * M = s * M + M := by ring
                  omega
                · rw [dite_eq_right hT]
          rw [hsum_eq]
          have hwalk_succ : walkVec start P s hs_le v =
              (walkVec start P s' (Nat.le_of_lt hs'_lt) ᵥ* P ⟨s', hs'_lt⟩) v := by
            rw [walkVec_congr start P hs_le (Nat.succ_le_of_lt hs'_lt) hs_eq rfl, walkVec_succ]
          rw [hwalk_succ]
          dsimp only [Matrix.vecMul, dotProduct]
          refine Finset.sum_congr rfl fun u _ ↦ ?_
          have hembed_ne0 : (embed u).val ≠ 0 := by dsimp only [embed]; omega
          have hembed_sub : (embed u).val - 1 = s' * M + u.val := by dsimp only [embed]; omega
          have hembed_lt_TM : (embed u).val - 1 < T * M := by
            rw [hembed_sub]
            calc s' * M + u.val < s' * M + M := Nat.add_lt_add_left u.isLt _
              _ = (s' + 1) * M := by ring
              _ ≤ T * M := Nat.mul_le_mul_right M hs'_lt
          have hembed_lt_T1M : (embed u).val - 1 < (T + 1) * M :=
            lt_of_lt_of_le hembed_lt_TM (Nat.mul_le_mul_right M (Nat.le_succ T))
          have hdiv_u : ((embed u).val - 1) / M = s' := by
            rw [hembed_sub, Nat.mul_comm, Nat.mul_add_div hM,
              Nat.div_eq_of_lt u.isLt, add_zero]
          have hmod_u : ((embed u).val - 1) % M = u.val := by
            rw [hembed_sub, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt u.isLt]
          have hq_u : q (embed u) = walkVec start P s' (Nat.le_of_lt hs'_lt) u := by
            rw [hq_layer hembed_ne0 hembed_lt_T1M]
            exact walkVec_congr start P _ _ hdiv_u (Fin.ext hmod_u)
          have hj_in : 1 + (((embed u).val - 1) / M + 1) * M ≤ j.val ∧
              j.val < 1 + (((embed u).val - 1) / M + 2) * M := by
            rw [hdiv_u]
            have h1 : (s' + 1) * M = s * M := by rw [hs_eq]
            have h2 : (s' + 2) * M = s * M + M := by rw [hs_eq]; ring
            exact ⟨by omega, by omega⟩
          have hW_u : W (embed u) j = P ⟨s', hs'_lt⟩ u v := by
            rw [hW_step hembed_ne0 hembed_lt_TM, dite_eq_left hj_in]
            have hs_fin :
                (⟨((embed u).val - 1) / M,
                  Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hembed_lt_TM)⟩ : Fin T) =
                ⟨s', hs'_lt⟩ := Fin.ext hdiv_u
            have hu_fin : (⟨((embed u).val - 1) % M, Nat.mod_lt _ hM⟩ : Fin M) = u :=
              Fin.ext hmod_u
            rw [hs_fin, hu_fin]
            congr 1
            ext
            simp only [hdiv_u]
            have : (s' + 1) * M = s * M := by rw [hs_eq]
            omega
          rw [hq_u, hW_u]
      · have hj_sink : j.val = 1 + (T + 1) * M := by
          have := j.isLt
          dsimp only [m] at this
          omega
        rw [hq_sink hj0 hjL]
        let embedT (u : Fin M) : Fin (m + 1) :=
          ⟨1 + T * M + u.val, by have hu := u.isLt; dsimp [m]; nlinarith⟩
        have hembedT_inj : Function.Injective embedT := fun u₁ u₂ h ↦
          Fin.ext (by have := congrArg Fin.val h; dsimp [embedT] at this; omega)
        have hsum_eq :
            (∑ i : Fin (m + 1), q i * W i j) =
              ∑ u : Fin M, q (embedT u) * W (embedT u) j := by
          rw [← Finset.sum_image (f := fun i ↦ q i * W i j) (fun u₁ _ u₂ _ h ↦ hembedT_inj h)]
          refine (Finset.sum_subset (Finset.subset_univ _) fun i _ hnot ↦ ?_).symm
          rw [Finset.mem_image] at hnot
          suffices hW0 : W i j = 0 by rw [hW0, mul_zero]
          by_cases hi0 : i.val = 0
          · rw [hW_of_zero hi0, ite_eq_right]
            intro hstart
            have hst_lt : start.val < M := start.isLt
            have hM_le : M ≤ (T + 1) * M := Nat.le_mul_of_pos_left M (Nat.succ_pos T)
            omega
          · by_cases hstep : i.val - 1 < T * M
            · rw [hW_step hi0 hstep, dite_eq_right]
              intro hj_in
              have hdiv_lt : (i.val - 1) / M < T :=
                Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hstep)
              have hmul : ((i.val - 1) / M + 2) * M ≤ (T + 1) * M :=
                Nat.mul_le_mul_right M (by omega)
              omega
            · rw [hW_last hi0 hstep]
              by_cases hT : i.val < 1 + (T + 1) * M
              · exfalso
                let ui : Fin M := ⟨i.val - (1 + T * M), by
                  have : (T + 1) * M = T * M + M := by ring
                  omega⟩
                have hi_eq : embedT ui = i := Fin.ext (by dsimp [embedT, ui]; omega)
                exact hnot ⟨ui, Finset.mem_univ ui, hi_eq⟩
              · rw [dite_eq_right hT]
        rw [hsum_eq]
        refine Finset.sum_congr rfl fun u _ ↦ ?_
        have hne0 : (embedT u).val ≠ 0 := by dsimp only [embedT]; omega
        have hembedT_sub : (embedT u).val - 1 = T * M + u.val := by dsimp only [embedT]; omega
        have hnot_TM : ¬((embedT u).val - 1 < T * M) := by rw [hembedT_sub]; omega
        have hlt_T1M : (embedT u).val - 1 < (T + 1) * M := by
          rw [hembedT_sub]
          calc T * M + u.val < T * M + M := Nat.add_lt_add_left u.isLt _
            _ = (T + 1) * M := by ring
        have hlt_1T1M : (embedT u).val < 1 + (T + 1) * M := by
          dsimp only [embedT]
          have := u.isLt
          have : (T + 1) * M = T * M + M := by ring
          omega
        have hdiv_T : ((embedT u).val - 1) / M = T := by
          rw [hembedT_sub, Nat.mul_comm, Nat.mul_add_div hM,
            Nat.div_eq_of_lt u.isLt, add_zero]
        have hmod_T : ((embedT u).val - 1) % M = u.val := by
          rw [hembedT_sub, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt u.isLt]
        have hq_u : q (embedT u) = walkVec start P T le_rfl u := by
          rw [hq_layer hne0 hlt_T1M]
          exact walkVec_congr start P _ _ hdiv_T (Fin.ext hmod_T)
        have hW_u : W (embedT u) j = acceptVec u := by
          rw [hW_last hne0 hnot_TM, dite_eq_left hlt_1T1M, ite_eq_left hj_sink]
          congr 1; ext; dsimp only [embedT]; omega
        rw [hq_u, hW_u]
  rw [hsub, ← Matrix.eq_det_submatrix_sub_one_of_eq_single_add_vecMul W hW_upper hq]
  exact hq_sink (by simp [m]) (by simp [m])

/-! ### Compact transition multiplicity matrix and $\mathrm{Mod}_k\mathrm{L}$ in $\mathrm{DET}_k$ -/

/-- Transition-occurrence multiplicity of `M : MultiTapeCTM k_tapes Bool State` from compact vertex
`u` to `v` on supplied input symbol `sym`. Halted vertices have a single self-loop. -/
noncomputable def ctmStepMult {k_tapes : ℕ} {State : Type} [Fintype State]
    (M : MultiTapeCTM k_tapes Bool State) (B n : ℕ)
    (u v : Fin (vertexBound (k := k_tapes) B)) (sym : Option Bool) : ℕ :=
  let r := readRegisters (k := k_tapes) B u.val
  if valid (k := k_tapes) (State := State) B n u.val &&
     valid (k := k_tapes) (State := State) B n v.val then
    if r .control = stateCode (State := State) none then
      if v = u then 1 else 0
    else
      ∑ qw : State × (Fin k_tapes → Option Bool),
        if r .control = stateCode (some qw.1) ∧
           (∀ i, r (.head i) = symbolCode (qw.2 i)) then
          ((M.tr qw.1 (inputSymbol n (r .inputPos) sym) qw.2 Empty.elim).map
            MultiTapeMachine.Action.emptyOracleEquiv).countP fun act ↦
              fitsB B (nextRegisters n r act) &&
                decide (v.val = Cslib.Radix.pack B (nextRegisters n r act))
        else 0
  else 0

/-- Single-literal matrix specification over `ZMod k` for one transition step of `M` on the compact
configuration box of radix `B` and input length `n`. -/
noncomputable def ctmStepSpec {k k_tapes : ℕ} {State : Type} [Fintype State]
    (M : MultiTapeCTM k_tapes Bool State) (B n : ℕ) :
    SingleVarMatrixSpec k n (vertexBound (k := k_tapes) B) where
  readIdx u _ :=
    let q := queryIndex (k := k_tapes) B u.val
    if hq : q < n then some ⟨q, hq⟩ else none
  valFalse u v :=
    let q := queryIndex (k := k_tapes) B u.val
    if q < n then (ctmStepMult M B n u v (some false) : ZMod k)
    else (ctmStepMult M B n u v none : ZMod k)
  valTrue u v :=
    (ctmStepMult M B n u v (some true) : ZMod k)

private theorem eval_ctmStepSpec_eq {k k_tapes : ℕ} {State : Type} [Fintype State]
    (M : MultiTapeCTM k_tapes Bool State) (B : ℕ) (w : List Bool)
    (u v : Fin (vertexBound (k := k_tapes) B)) :
    ((ctmStepSpec (k := k) M B w.length).eval (fun i : Fin w.length ↦ w[i.val])) u v =
      (ctmStepMult M B w.length u v w[queryIndex (k := k_tapes) B u.val]? : ZMod k) := by
  rw [SingleVarMatrixSpec.eval_apply]
  dsimp only [ctmStepSpec]
  by_cases hq : queryIndex (k := k_tapes) B u.val < w.length
  · simp only [hq, ↓reduceDIte, ↓reduceIte]
    rw [List.getElem?_eq_getElem hq]
    cases w[queryIndex (k := k_tapes) B u.val] <;> rfl
  · simp only [hq, ↓reduceDIte, ↓reduceIte]
    rw [List.getElem?_eq_none (not_lt.mp hq)]

private theorem sum_countP_mul {α R : Type*} [Semiring R] {N : ℕ}
    (l : List α) (pred : α → Fin N → Bool) (g : Fin N → R)
    (huniq : ∀ a ∈ l, ∃ v₀ : Fin N, ∀ v : Fin N, pred a v = decide (v = v₀)) :
    (∑ v : Fin N, (l.countP (fun a ↦ pred a v) : R) * g v) =
      (l.map fun a ↦ ∑ v : Fin N, if pred a v then g v else 0).sum := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    obtain ⟨v₀, hv₀⟩ := huniq a (List.mem_cons_self ..)
    have hrest := ih (fun b hb ↦ huniq b (List.mem_cons_of_mem a hb))
    simp only [List.countP_cons, List.map_cons, List.sum_cons, ← hrest, Nat.cast_add, add_mul,
      Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    simp only [hv₀]
    rw [Finset.sum_eq_single v₀, Finset.sum_eq_single v₀]
    · simp
    · intro v _ hne; simp [hne]
    · simp
    · intro v _ hne; simp [hne]
    · simp

private theorem ctmStepMult_pow_mulVec_eq_branchCount {k k_tapes : ℕ} {State : Type} [Fintype State]
    (M : MultiTapeCTM k_tapes Bool State) (B : ℕ) (w : List Bool)
    (hfit_all : ∀ view, Relation.ReflTransGen M.toNTM.ViewStep (M.toNTM.initView w) view →
      Fits B (registers view)) :
    let N := vertexBound (k := k_tapes) B
    let P : Matrix (Fin N) (Fin N) (ZMod k) := fun u v ↦
      (ctmStepMult M B w.length u v w[queryIndex (k := k_tapes) B u.val]? : ZMod k)
    let e₀ : Fin N → ZMod k := fun v ↦
      if bad (k := k_tapes) (State := State) B w.length v.val then 1 else 0
    ∀ (t : ℕ) (view : FiniteCfg k_tapes Bool State) (cfg : Cfg k_tapes Bool State w)
      (hreach : Relation.ReflTransGen M.toNTM.ViewStep (M.toNTM.initView w) view),
      ViewRep view cfg →
      ((P ^ t) *ᵥ e₀) ⟨vertexID B view, vertexID_lt (hfit_all view hreach)⟩ =
        (M.branchCount (· == [true]) t cfg : ZMod k) := by
  intro N P e₀ t
  induction t with
  | zero =>
    intro view cfg hreach hrep
    have hfit := hfit_all view hreach
    simp only [pow_zero, Matrix.one_mulVec, e₀, ← M.countP_runList, MultiTapeCTM.runList_zero,
      List.countP_cons, List.countP_nil, zero_add]
    have hbad : bad (k := k_tapes) (State := State) B w.length (vertexID B view) =
        (cfg.state.isNone && (cfg.output == [true])) := by
      have hlen_in : w.length = view.input.length := by rw [hrep.input]
      rw [Bool.eq_iff_iff, hlen_in, bad_vertexID hfit, hrep.state, hrep.output,
        outputClass_eq_true_iff, Bool.and_eq_true, Option.isNone_iff_eq_none, beq_iff_eq]
    rw [hbad]
    cases (cfg.state.isNone && (cfg.output == [true])) <;> simp
  | succ t ih =>
    intro view cfg hreach hrep
    have hfit := hfit_all view hreach
    let u₀ : Fin N := ⟨vertexID B view, vertexID_lt hfit⟩
    have hvalid_u₀ : valid (k := k_tapes) (State := State) B w.length u₀.val = true := by
      simpa [u₀, hrep.input] using valid_vertexID hfit
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    let g := (P ^ t) *ᵥ e₀
    change (∑ v : Fin N, P u₀ v * g v) = _
    cases hs : cfg.state with
    | none =>
      have hvs : view.state = none := hrep.state.trans hs
      have hP (v : Fin N) : P u₀ v = if v = u₀ then 1 else 0 := by
        dsimp only [P, ctmStepMult]
        rw [readRegisters_vertexID hfit, hvalid_u₀, Bool.true_and]
        have hctrl : (registers view) .control = stateCode (State := State) none := by
          simp [registers, hvs]
        rw [ite_eq_left hctrl]
        by_cases hv : v = u₀
        · subst hv; simp [hvalid_u₀]
        · simp only [hv, ↓reduceIte]; split_ifs <;> simp
      simp only [hP, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      rw [show g u₀ = ((P ^ t) *ᵥ e₀) u₀ from rfl, ih view cfg hreach hrep,
        ← M.countP_runList, ← M.countP_runList, M.runList_halted hs, M.runList_halted hs]
    | some q₀ =>
      have hvs : view.state = some q₀ := hrep.state.trans hs
      have hctrl_ne : (registers view) .control ≠ stateCode (State := State) none := by
        simp [registers, hvs, stateCode_injective.eq_iff]
      obtain ⟨hin_sym, hwork_sym⟩ := hrep.symbols
      have hin_q : inputSymbol w.length ((registers view) .inputPos)
          w[queryIndex (k := k_tapes) B u₀.val]? = cfg.inputSymbol := by
        have hq := inputSymbol_query hfit
        simpa [registers, u₀, hrep.input, hin_sym] using hq
      have hP (v : Fin N) :
          P u₀ v =
            (((M.actions cfg).countP fun act ↦
              valid (k := k_tapes) (State := State) B w.length v.val &&
                fitsB B (nextRegisters w.length (registers view) act) &&
                decide (v.val = Cslib.Radix.pack B (nextRegisters w.length (registers view) act)) :
              ℕ) : ZMod k) := by
        dsimp only [P, ctmStepMult]
        rw [readRegisters_vertexID hfit, hvalid_u₀, Bool.true_and]
        by_cases hv_val : valid (k := k_tapes) (State := State) B w.length v.val = true
        · simp only [hv_val, ↓reduceIte, hctrl_ne]
          rw [Finset.sum_eq_single (q₀, view.workTapeSymbols)]
          · have hcond : (registers view) .control = stateCode (some q₀) ∧
                ∀ i, (registers view) (.head i) = symbolCode (view.workTapeSymbols i) :=
              ⟨by simp [registers, hvs], fun i ↦ rfl⟩
            rw [ite_eq_left hcond]
            congr 2
            simp [MultiTapeCTM.actions, hs, hin_q, hwork_sym]
          · rintro ⟨q', work'⟩ _ hne
            rw [ite_eq_right]
            rintro ⟨hq', hw'⟩
            apply hne
            have hq_eq : q' = q₀ := by
              have : some q₀ = some q' :=
                stateCode_injective (by simpa [registers, hvs] using hq')
              exact Option.some.inj this.symm
            have hw_eq : work' = view.workTapeSymbols := funext fun i ↦
              (symbolCode_injective (hw' i)).symm
            exact Prod.ext hq_eq hw_eq
          · simp
        · have hfalse : valid (k := k_tapes) (State := State) B w.length v.val = false :=
            Bool.eq_false_iff.mpr hv_val
          simp [hfalse]
      simp_rw [hP]
      have hact_step : ∀ act ∈ M.actions cfg,
          M.toNTM.ViewStep view (view.step act).summarizeOutput := by
        intro act hact
        simp only [MultiTapeCTM.actions, hs, List.mem_map] at hact
        obtain ⟨rawAct, hraw, rfl⟩ := hact
        simp only [ViewStep, hvs]
        refine ⟨_, ?_, rfl⟩
        simp only [MultiTapeCTM.toNTM, Equiv.symm_apply_apply]
        rwa [hin_sym, hwork_sym]
      have huniq : ∀ act ∈ M.actions cfg, ∃ v₀ : Fin N, ∀ v : Fin N,
          (valid (k := k_tapes) (State := State) B w.length v.val &&
            fitsB B (nextRegisters w.length (registers view) act) &&
            decide (v.val = Cslib.Radix.pack B (nextRegisters w.length (registers view) act))) =
          decide (v = v₀) := by
        intro act hact
        have hreach' := hreach.tail (hact_step act hact)
        have hfit' := hfit_all _ hreach'
        have hreg_eq : nextRegisters w.length (registers view) act =
            registers (view.step act).summarizeOutput := by
          simpa [hrep.input] using (registers_step view act).symm
        let v₀ : Fin N := ⟨vertexID B (view.step act).summarizeOutput, vertexID_lt hfit'⟩
        refine ⟨v₀, fun v ↦ ?_⟩
        rw [hreg_eq, fitsB_eq_true.mpr hfit', Bool.and_true]
        change (valid (k := k_tapes) (State := State) B w.length v.val &&
            decide (v.val = v₀.val)) = decide (v = v₀)
        by_cases hv : v = v₀
        · subst hv
          have hv_valid : valid (k := k_tapes) (State := State) B w.length v₀.val = true := by
            have hvin : (view.step act).summarizeOutput.input = w := input_of_reachable hreach'
            simpa [v₀, hvin] using valid_vertexID hfit'
          simp [hv_valid]
        · have hne_val : v.val ≠ v₀.val := fun h ↦ hv (Fin.ext h)
          simp [hv, hne_val]
      rw [sum_countP_mul (M.actions cfg) _ g huniq, M.branchCount_succ (· == [true]) cfg t q₀ hs,
        Nat.cast_sum, ← List.sum_ofFn]
      congr 1
      apply List.ext_getElem
      · simp
      · intro idx h₁ h₂
        simp only [List.getElem_map, List.getElem_ofFn]
        let act := (M.actions cfg)[idx]'(by simpa using h₁)
        have hact_mem : act ∈ M.actions cfg := List.getElem_mem _
        have hreach' := hreach.tail (hact_step act hact_mem)
        have hfit' := hfit_all _ hreach'
        have hreg_eq : nextRegisters w.length (registers view) act =
            registers (view.step act).summarizeOutput := by
          simpa [hrep.input] using (registers_step view act).symm
        let v₀ : Fin N := ⟨vertexID B (view.step act).summarizeOutput, vertexID_lt hfit'⟩
        have hv_valid : valid (k := k_tapes) (State := State) B w.length v₀.val = true := by
          have hvin : (view.step act).summarizeOutput.input = w := input_of_reachable hreach'
          simpa [v₀, hvin] using valid_vertexID hfit'
        rw [Finset.sum_eq_single v₀]
        · simp only [act, hreg_eq, hv_valid, fitsB_eq_true.mpr hfit', Bool.and_self]
          change (if decide (v₀.val = v₀.val) = true then g v₀ else 0) = _
          simp only [decide_true, ↓reduceIte]
          exact ih _ _ hreach' (hrep.step act)
        · intro v _ hne
          have hne_val : v.val ≠ v₀.val := fun h ↦ hne (Fin.ext h)
          simp only [act, hreg_eq]
          change (if (valid (k := k_tapes) (State := State) B w.length v.val &&
              fitsB B (registers (view.step act).summarizeOutput) &&
              decide (v.val = v₀.val)) = true then g v else 0) = 0
          simp [hne_val]
        · simp

/-- **$\mathrm{Mod}_k\mathrm{L} \subseteq \mathrm{DET}_k$** on arbitrary encoded decision problems
for every modulus `k ≥ 2`. -/
theorem ModL_subset_DETkOn {k : ℕ} (hk : 2 ≤ k) {α : Type} {enc : α ↪ List Bool} :
    ModL k enc ⊆ DETkOn k enc := by
  have hk_ne : NeZero k := ⟨by omega⟩
  rintro A ⟨f, ⟨k_tapes, State, hfinite, M, c, hM⟩, hA⟩
  classical
  let _ : Fintype State := Fintype.ofFinite State
  let D : ℕ := radixExponent State c
  let expT : ℕ := logSpaceClockExponent k_tapes State c
  let B (n : ℕ) : ℕ := radix D n
  let N (n : ℕ) : ℕ := vertexBound (k := k_tapes) (B n)
  have hN_pos (n : ℕ) : 0 < N n := by
    dsimp only [N]
    rw [vertexBound_eq_pow]
    exact Nat.pow_pos (by omega)
  let T (n : ℕ) : ℕ := polyClock expT n
  have hstart_lt (n : ℕ) : startID M.toNTM (B n) < N n := by
    let w₀ : List Bool := List.replicate n false
    have hfit₀ : Fits (B n) (registers (M.toNTM.initView w₀)) := by
      have hD : 2 ≤ D := by simp only [D, radixExponent]; omega
      have hbase : w₀.length + 2 ≤ B n := by
        simp only [w₀, List.length_replicate, B, radix]
        calc n + 2 = (n + 2) ^ 1 := (pow_one _).symm
          _ ≤ (n + 2) ^ D := Nat.pow_le_pow_right (by omega) (by omega)
      have hc_lt : Fintype.card (Option State) < B n :=
        Nat.lt_of_succ_lt (card_succ_lt_radix c n)
      have h3_lt : 3 < B n :=
        calc 3 < 2 ^ 2 := by decide
          _ ≤ (n + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
          _ ≤ B n := Nat.pow_le_pow_right (by omega) hD
      intro i
      cases i with
      | inputPos =>
        simpa [registers, MultiTapeNTM.initView, FiniteCfg.init] using
          lt_of_lt_of_le (by omega : 1 < w₀.length + 2) hbase
      | control => exact (Fintype.equivFin (Option State) _).isLt.trans hc_lt
      | output => exact (outputCode_lt _).trans h3_lt
      | head _ => simpa [registers] using (symbolCode_lt _).trans h3_lt
      | left _ | right _ =>
        simpa [registers, MultiTapeNTM.initView, FiniteCfg.init, Cslib.Turing.BiTape.nil] using
          Nat.zero_lt_of_lt h3_lt
    rw [← vertexID_init M.toNTM (B n) w₀]
    exact vertexID_lt hfit₀
  let dagDim (n : ℕ) : ℕ := (T n + 1) * N n + 1
  let dagSpec (n : ℕ) : SingleVarMatrixSpec k n (dagDim n) :=
    layeredDAGSpec (hN_pos n) ⟨startID M.toNTM (B n), hstart_lt n⟩
      (fun _ : Fin (T n) ↦ ctmStepSpec (k := k) M (B n) n)
      (fun v : Fin (N n) ↦
        if bad (k := k_tapes) (State := State) (B n) n v.val then 1 else 0)
  let C (n : ℕ) : Circuit oracleSignature n 1 :=
    singleLiteralDetCircuit (dagSpec n) 0 true
  let L_wit : Language Bool :=
    {w : List Bool |
      (C w.length).eval (oracleInterpretation (detZModLanguage k))
        (fun i : Fin w.length ↦ w[i.val]) 0 = true}
  have hL_mem : L_wit ∈ DETk k := by
    let pCard := D * Fintype.card (Register k_tapes)
    let bound (n : ℕ) : ℕ :=
      n + 4 + DetZModInstance.encodedLen k ((polyClock expT n + 1) * (n + 2) ^ pCard + 1)
    have hpoly : PolynomiallyBounded bound := by
      dsimp only [bound, polyClock]
      simp only [DetZModInstance.encodedLen_eq]
      fun_prop
    obtain ⟨a₀, d₀, hbound_poly⟩ := polynomiallyBounded_iff_le.1 hpoly
    refine ⟨C, 3 * (d₀ + a₀ + 4), bound, hpoly, fun n ↦ ⟨?_, ?_, ?_, ?_⟩⟩
    · exact (size_singleLiteralDetCircuit_le _ _ _).trans (Nat.le_add_right _ _)
    · have hN_eq : N n = (n + 2) ^ pCard := vertexBound_eq_pow D n
      have hdim_eq : dagDim n = (polyClock expT n + 1) * (n + 2) ^ pCard + 1 := by
        simp [dagDim, T, hN_eq]
      refine (fanInAtMost_singleLiteralDetCircuit _ _ _).mono ?_
      rw [hdim_eq]
      exact max_le (by dsimp [bound]; omega) (Nat.le_add_left _ _)
    · have hN_eq : N n = (n + 2) ^ pCard := vertexBound_eq_pow D n
      have hdim_eq : dagDim n = (polyClock expT n + 1) * (n + 2) ^ pCard + 1 := by
        simp [dagDim, T, hN_eq]
      have hlen_le : DetZModInstance.encodedLen k (dagDim n) ≤ a₀ * (n + 1) ^ d₀ := by
        have h1 : DetZModInstance.encodedLen k (dagDim n) ≤ bound n := by
          rw [hdim_eq]; exact Nat.le_add_left _ _
        exact h1.trans (hbound_poly n)
      refine (depthWith_singleLiteralDetCircuit_le _ _ _).trans ?_
      by_cases h0 : DetZModInstance.encodedLen k (dagDim n) = 0
      · simp only [h0, Nat.log_zero_right]
        have : 1 ≤ Nat.log 2 n + 1 := Nat.le_add_left 1 _
        nlinarith
      · have hn2 : n + 1 < 2 ^ (Nat.log 2 n + 2) := by
          have := Nat.lt_pow_succ_log_self Nat.one_lt_two n
          rw [pow_succ]
          omega
        have ha2 : a₀ < 2 ^ (a₀ + 1) := Nat.lt_two_pow_self.trans_le
          (Nat.pow_le_pow_right Nat.two_pos (Nat.le_succ a₀))
        have hpow_lt : DetZModInstance.encodedLen k (dagDim n) <
            2 ^ ((a₀ + 1) + d₀ * (Nat.log 2 n + 2)) :=
          calc DetZModInstance.encodedLen k (dagDim n)
              ≤ a₀ * (n + 1) ^ d₀ := hlen_le
            _ ≤ a₀ * (2 ^ (Nat.log 2 n + 2)) ^ d₀ :=
                Nat.mul_le_mul_left a₀ (Nat.pow_le_pow_left hn2.le d₀)
            _ < 2 ^ (a₀ + 1) * (2 ^ (Nat.log 2 n + 2)) ^ d₀ :=
                Nat.mul_lt_mul_of_pos_right ha2 (Nat.pow_pos (Nat.two_pow_pos (Nat.log 2 n + 2)))
            _ = 2 ^ ((a₀ + 1) + d₀ * (Nat.log 2 n + 2)) := by
                rw [← pow_mul, mul_comm (Nat.log 2 n + 2) d₀, ← pow_add]
        have hlog_lt := (Nat.log_lt_iff_lt_pow (by decide) h0).mpr hpow_lt
        have h1 : 1 ≤ Nat.log 2 n + 1 := Nat.le_add_left 1 _
        nlinarith
    · intro x
      funext j
      obtain rfl : j = 0 := Subsingleton.elim j 0
      dsimp only [single]
      rw [Bool.eq_iff_iff, Language.slice_eq_true_iff]
      change _ ↔ (C (List.ofFn x).length).eval (oracleInterpretation (detZModLanguage k))
        (fun i ↦ (List.ofFn x)[i.val]) 0 = true
      have hfn : ∀ (m : ℕ) (hm : m = n) (y : Fin m → Bool),
          (∀ i : Fin m, y i = x (Fin.cast hm i)) →
          (C m).eval (oracleInterpretation (detZModLanguage k)) y 0 =
            (C n).eval (oracleInterpretation (detZModLanguage k)) x 0 := by
        rintro m rfl y hy
        congr 2
        funext i
        exact hy i
      rw [hfn (List.ofFn x).length List.length_ofFn
        (fun i ↦ (List.ofFn x)[i.val]) (fun i ↦ by simp only [List.getElem_ofFn]; rfl)]
  refine ⟨L_wit, hL_mem, fun a ↦ ?_⟩
  rw [hA a]
  let w := enc a
  let n := w.length
  change f a % k ≠ 0 ↔
    (C n).eval (oracleInterpretation (detZModLanguage k)) (fun i : Fin n ↦ w[i.val]) 0 = true
  rw [eval_singleLiteralDetCircuit, Bool.true_xor, Bool.not_eq_true', decide_eq_false_iff_not]
  rw [det_layeredDAGSpec_eval]
  obtain ⟨hspace, t₀, hhalt₀, hf_eq⟩ := hM a
  have htime₀ : M.toNTM.RunsInTime w t₀ :=
    fun p hp ↦ hhalt₀.paths_halted p.toRunPath p.head_eq hp
  have htimeT : M.toNTM.RunsInTime w (T n) :=
    (runsInTime_of_runsInSpace hspace htime₀).mono
      (two_pow_coreLengthBound_log_le k_tapes State c n)
  have hhaltT : M.HaltsWithin (T n) (Cfg.init M.initial w) :=
    MultiTapeCTM.haltsWithin_of_paths_of_haltsWithin hhalt₀ fun p hp hlen ↦ htimeT ⟨p, hp⟩ hlen
  have hf_T : f a = M.branchCount (· == [true]) (T n) (Cfg.init M.initial w) := by
    rw [hf_eq]
    change M.branchCount (· == [true]) t₀ (Cfg.init M.initial w) =
      M.branchCount (· == [true]) (T n) (Cfg.init M.initial w)
    have h₁ := hhalt₀.branchCount_eq (le_max_left t₀ (T n)) (· == [true])
    have h₂ := hhaltT.branchCount_eq (le_max_right t₀ (T n)) (· == [true])
    exact h₁.symm.trans h₂
  have hfit_all : ∀ view, Relation.ReflTransGen M.toNTM.ViewStep (M.toNTM.initView w) view →
      Fits (B n) (registers view) :=
    fun _ hv ↦ fits_of_runsInSpace c hspace hv
  let P_mat : Matrix (Fin (N n)) (Fin (N n)) (ZMod k) := fun u v ↦
    (ctmStepMult M (B n) n u v w[queryIndex (k := k_tapes) (B n) u.val]? : ZMod k)
  have hstep_eq : (fun _ : Fin (T n) ↦
      (ctmStepSpec (k := k) M (B n) n).eval (fun i : Fin n ↦ w[i.val])) =
      fun _ ↦ P_mat := by
    funext _
    ext u v
    exact eval_ctmStepSpec_eq M (B n) w u v
  rw [hstep_eq, walkVec_const_dot_eq_pow_mulVec]
  have hstart_eq : (⟨startID M.toNTM (B n), hstart_lt n⟩ : Fin (N n)) =
      ⟨vertexID (B n) (M.toNTM.initView w), vertexID_lt (hfit_all _ .refl)⟩ :=
    Fin.ext (vertexID_init M.toNTM (B n) w).symm
  rw [hstart_eq]
  have hcount := ctmStepMult_pow_mulVec_eq_branchCount (k := k) M (B n) w hfit_all (T n)
    (M.toNTM.initView w) (Cfg.init M.initial w) .refl (viewRep_init (ntm := M.toNTM) w)
  rw [hcount, ← hf_T]
  exact (zmod_natCast_ne_zero_iff (k := k) (f a)).symm

/-- Bitstring-language form of $\mathrm{Mod}_k\mathrm{L} \subseteq \mathrm{DET}_k$ for `k ≥ 2`. -/
theorem ModL_encBits_subset_DETk {k : ℕ} (hk : 2 ≤ k) :
    ModL k MultiTapeTM.encBits ⊆ DETk k := by
  intro L hL
  exact (mem_DETkOn_encBits_iff (k := k) (A := L)).mp (ModL_subset_DETkOn hk hL)

/-- **$\mathrm{Mod}_k\mathrm{L} \subseteq \mathrm{DET}$** for every modulus `k ≥ 2`. -/
theorem ModL_subset_DETOn {k : ℕ} (hk : 2 ≤ k) {α : Type} {enc : α ↪ List Bool} :
    ModL k enc ⊆ DETOn enc :=
  (ModL_subset_DETkOn hk).trans (DETkOn_subset_DETOn hk enc)

/-! ### Private sanity check -/

section Sanity

private example {lang : Language Bool} (h : lang ∈ L MultiTapeTM.encBits) :
    lang ∈ DETk 2 ∧ lang ∈ DET :=
  let hmod := L_subset_ModL (k := 2) (by decide) h
  ⟨ModL_encBits_subset_DETk (by decide) hmod,
   DETk_subset_DET (by decide) (ModL_encBits_subset_DETk (by decide) hmod)⟩

end Sanity

end Cslib.Complexity
