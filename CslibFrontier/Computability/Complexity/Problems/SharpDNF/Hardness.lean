/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Classes.SharpP.Metric
public import CslibFrontier.Computability.Complexity.Problems.SharpDNF
public import CslibFrontier.Computability.Complexity.Problems.SharpSAT
public import CslibFrontier.Logics.Propositional.DNF

import CslibFrontier.Computability.Complexity.CookLevin.Counting
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Logics.Propositional.CNF.PolyTime
import CslibFrontier.Logics.Propositional.DNF.ModelCount
import Mathlib.Data.List.GetD

/-!
# Metric `#P`-hardness of `#DNF`

De Morgan negation maps a CNF formula `φ` over `ℕ` to a DNF formula `CNF.negate φ` over the
same variables with complementary satisfying assignments (`sharpSAT_add_sharpDNF_negate`).
Combining this identity with Valiant / Cook–Levin `#P`-hardness of `#SAT` yields a polynomial-time
metric reduction proving `#DNF` is `#P`-hard under metric reductions
(`sharpDNF_sharpPMetricHard`).

## Main results

* `Cslib.Complexity.sharpSAT_add_sharpDNF_negate`:
  `SharpSAT φ + SharpDNF (CNF.negate φ) = 2 ^ numVars φ`.
* `Cslib.Complexity.sharpDNF_sharpPMetricHard`: `#DNF` is `#P`-hard under metric reductions.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL
open Turing.MultiTapeTM

private theorem vars_cnf_negate (φ : CNF ℕ) : CNF.vars (CNF.negate φ) = CNF.vars φ := by
  simp only [CNF.negate, CNF.vars, Clause.negate, List.map_flatten, List.map_map,
    Function.comp_def]

/-- Complementary counting identity between `#SAT` and `#DNF` under De Morgan negation. -/
theorem sharpSAT_add_sharpDNF_negate (φ : CNF ℕ) :
    SharpSAT φ + SharpDNF (CNF.negate φ) = 2 ^ CNF.numVars φ := by
  classical
  have hvars := vars_cnf_negate φ
  have hdv : CNF.distinctVars (CNF.negate φ) = CNF.distinctVars φ := by
    simp only [CNF.distinctVars, hvars]
  have hnv : CNF.numVars (CNF.negate φ) = CNF.numVars φ := by
    simp only [CNF.numVars, hvars]
  rw [SharpSAT, SharpDNF, DNF.modelCount_eq_card_filter, hdv, hnv]
  rw [CNF.modelCount_eq_card_filter
    (fun (σ : ℕ → Bool) (i : Fin (CNF.numVars φ)) => σ ((CNF.distinctVars φ).getD i.1 0))
    (fun x : Fin (CNF.numVars φ) → Bool =>
      CNF.eval (wordAssignment (CNF.distinctVars φ) (List.ofFn x)) φ = true)
    (fun σ τ _ _ => by
      constructor
      · intro h v hv
        have hlt : (CNF.distinctVars φ).idxOf v < CNF.numVars φ := by
          rw [← CNF.length_distinctVars φ]
          exact List.idxOf_lt_length_of_mem (CNF.mem_distinctVars.mpr hv)
        have hlt_len : (CNF.distinctVars φ).idxOf v < (CNF.distinctVars φ).length :=
          List.idxOf_lt_length_of_mem (CNF.mem_distinctVars.mpr hv)
        have := congrFun h ⟨_, hlt⟩
        rw [List.getD_eq_getElem _ _ hlt_len, List.getElem_idxOf] at this
        exact this
      · intro h
        funext i
        have hi : i.1 < (CNF.distinctVars φ).length := by rw [CNF.length_distinctVars φ]; exact i.2
        rw [List.getD_eq_getElem _ _ hi]
        exact h _ (CNF.mem_distinctVars.mp (List.getElem_mem hi)))
    (fun x => by
      constructor
      · intro hx
        refine ⟨wordAssignment (CNF.distinctVars φ) (List.ofFn x), hx, funext fun i => ?_⟩
        have hi : i.1 < (CNF.distinctVars φ).length := by rw [CNF.length_distinctVars φ]; exact i.2
        rw [List.getD_eq_getElem _ _ hi, wordAssignment,
          (CNF.nodup_distinctVars φ).idxOf_getElem _ hi,
          List.getD_eq_getElem _ _ (by simp [i.2]), List.getElem_ofFn]
      · rintro ⟨σ, hσ, rfl⟩
        refine (CNF.eval_congr fun v hv => ?_).trans hσ
        have hlt : (CNF.distinctVars φ).idxOf v < CNF.numVars φ := by
          rw [← CNF.length_distinctVars φ]
          exact List.idxOf_lt_length_of_mem (CNF.mem_distinctVars.mpr hv)
        have hlt_len : (CNF.distinctVars φ).idxOf v < (CNF.distinctVars φ).length :=
          List.idxOf_lt_length_of_mem (CNF.mem_distinctVars.mpr hv)
        rw [wordAssignment, List.getD_eq_getElem _ _ (by simp [hlt]), List.getElem_ofFn,
          List.getD_eq_getElem _ _ hlt_len, List.getElem_idxOf])]
  have hcompl :
      (Finset.univ.filter fun x : Fin (CNF.numVars φ) → Bool =>
        DNF.eval (wordAssignment (CNF.distinctVars φ) (List.ofFn x)) (CNF.negate φ) = true) =
      Finset.univ.filter fun x : Fin (CNF.numVars φ) → Bool =>
        ¬(CNF.eval (wordAssignment (CNF.distinctVars φ) (List.ofFn x)) φ = true) := by
    ext x
    simp [CNF.eval_negate]
  rw [hcompl, Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin]

/-- **`#DNF` is `#P`-hard under metric reductions**: proved from Cook–Levin `#SAT`
hardness via De Morgan negation `SharpSAT φ = 2 ^ numVars φ - SharpDNF (CNF.negate φ)`. -/
theorem sharpDNF_sharpPMetricHard : SharpPMetricHard encDNF encNat SharpDNF := by
  refine CookLevin.SharpSAT_sharpPHard.sharpPMetricHard.trans ?_
  refine ⟨CNF.negate, fun p => 2 ^ CNF.numVars p.1 - p.2, ?_, ?_, fun φ => ?_⟩
  · exact ComputableInPolyTime.map
      (ComputableInPolyTime.map (Literal.computableInPolyTime_negate encNat))
  · exact ComputableInPolyTime.binary_sub'
      (ComputableInPolyTime.binary_two_pow.comp
        ((CNF.computableInPolyTime_numVars encNat).comp (by fun_prop)))
      (by fun_prop)
  · have h := sharpSAT_add_sharpDNF_negate φ
    dsimp only
    omega

end Cslib.Complexity
