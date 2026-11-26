/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.BoundedExec

import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Register-renaming transport for frontier-bounded Word RAM executions

This module provides `ExecBoundedExact.rename_post` and `ExecBounded.rename_post`, transporting
frontier-bounded structured Word RAM executions (`ExecBoundedExact` and `ExecBounded`) along an
injective register renaming `f : Fin r → Fin s` while preserving untouched registers and keeping all
memory accesses strictly below the address frontier `L`.

## Main results

* `Cslib.WordRAM.ExecBoundedExact.rename_post`: transport of `ExecBoundedExact` along an injective
  register renaming.
* `Cslib.WordRAM.ExecBounded.rename_post`: transport of `ExecBounded` along an injective register
  renaming.
-/

public section

namespace Cslib.WordRAM

/-- Transport `ExecBoundedExact` along an injective register renaming `f : Fin r → Fin s`,
preserving untouched registers and keeping all memory accesses strictly below `L`. -/
theorem ExecBoundedExact.rename_post {B : Basis} {r s w L n : ℕ}
    {f : Fin r → Fin s} (hf : Function.Injective f) {c : Code B r}
    {x : Data s} {y : Data r}
    (h : ExecBoundedExact w L c (x.comap f) y n) :
    ∃ z : Data s, ExecBoundedExact w L (c.rename f) x z n ∧
      z.comap f = y ∧ ∀ i : Fin s, (∀ j : Fin r, f j ≠ i) → z.regs i = x.regs i := by
  generalize hx : x.comap f = x₀ at h
  induction h generalizing x with
  | @op o x₁ y₁ hb ho =>
    subst hx
    have hbo : (o.rename f).BoundedAccess L x := by
      cases o <;> simp only [Op.rename, Op.BoundedAccess, Data.comap] at hb ⊢ <;> exact hb
    obtain ⟨z, hz, hzc, hzf⟩ := Exec.rename_post_of_exec hf (Exec.op ho)
    cases hz with
    | op hze => exact ⟨z, .op hbo hze, hzc, hzf⟩
  | @seq c₁ c₂ x₁ y₁ z₁ m n₁ h₁ h₂ ih₁ ih₂ =>
    subst hx
    obtain ⟨u, hu, huc, huf⟩ := ih₁ rfl
    obtain ⟨v, hv, hvc, hvf⟩ := ih₂ huc
    exact ⟨v, .seq hu hv, hvc, fun i hi => (hvf i hi).trans (huf i hi)⟩
  | @branch_pos cond pos neg x₁ y₁ n₁ hc h₁ ih =>
    subst hx
    obtain ⟨z, hz, hzc, hzf⟩ := ih rfl
    have hc' : (cond.rename f).Holds x := by
      cases cond <;> simpa [Cond.rename, Cond.Holds, Data.comap] using hc
    exact ⟨z, .branch_pos hc' hz, hzc, hzf⟩
  | @branch_neg cond pos neg x₁ y₁ n₁ hc h₁ ih =>
    subst hx
    obtain ⟨z, hz, hzc, hzf⟩ := ih rfl
    have hc' : ¬(cond.rename f).Holds x := by
      cases cond <;> simpa [Cond.rename, Cond.Holds, Data.comap] using hc
    exact ⟨z, .branch_neg hc' hz, hzc, hzf⟩
  | @loop_exit cond body x₁ hc =>
    subst hx
    have hc' : ¬(cond.rename f).Holds x := by
      cases cond <;> simpa [Cond.rename, Cond.Holds, Data.comap] using hc
    exact ⟨x, .loop_exit hc', rfl, fun _ _ => rfl⟩
  | @loop_iter cond body x₁ y₁ z₁ m n₁ hc h₁ h₂ ih₁ ih₂ =>
    subst hx
    obtain ⟨u, hu, huc, huf⟩ := ih₁ rfl
    obtain ⟨v, hv, hvc, hvf⟩ := ih₂ huc
    have hc' : (cond.rename f).Holds x := by
      cases cond <;> simpa [Cond.rename, Cond.Holds, Data.comap] using hc
    exact ⟨v, .loop_iter hc' hu hv, hvc, fun i hi => (hvf i hi).trans (huf i hi)⟩

/-- Transport `ExecBounded` along an injective register renaming `f : Fin r → Fin s`. -/
theorem ExecBounded.rename_post {B : Basis} {r s w L T : ℕ}
    {f : Fin r → Fin s} (hf : Function.Injective f) {c : Code B r}
    {x : Data s} {y : Data r}
    (h : ExecBounded w L c (x.comap f) y T) :
    ∃ z : Data s, ExecBounded w L (c.rename f) x z T ∧
      z.comap f = y ∧ ∀ i : Fin s, (∀ j : Fin r, f j ≠ i) → z.regs i = x.regs i := by
  obtain ⟨n, hn, he⟩ := h
  obtain ⟨z, hz, hzc, hzf⟩ := ExecBoundedExact.rename_post hf he
  exact ⟨z, ⟨n, hn, hz⟩, hzc, hzf⟩

end Cslib.WordRAM
