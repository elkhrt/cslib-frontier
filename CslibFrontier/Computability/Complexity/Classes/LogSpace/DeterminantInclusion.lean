/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Balanced
public import CslibFrontier.Computability.Complexity.Classes.LogSpace.DeterminantCircuit

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite Truth-Table Synthesis and the Inclusion $\mathrm{DET}_k \subseteq \mathrm{DET}$

This module proves that for every modulus $k \ge 2$, the modular determinant complexity class
$\mathrm{DET}_k$ is contained in Cook's integer determinant class $\mathrm{DET}$ under standard
Lean axioms (`Cslib.Complexity.DETk_subset_DET`).

## Main definitions

* `Cslib.Complexity.truthTableCircuit1`,
  `Cslib.Complexity.truthTableCircuit`: explicit De Morgan Boolean circuit synthesis
  for arbitrary fixed-width functions `(Fin w → Bool) → Fin out → Bool`.

## Main results

* `Cslib.Complexity.eval_truthTableCircuit`,
  `Cslib.Complexity.size_truthTableCircuit_le`,
  `Cslib.Complexity.depth_truthTableCircuit_le`: any Boolean map
  `(Fin w → Bool) → Fin out → Bool` is computed by a De Morgan circuit of size `≤ out * (5 * 2 ^ w)`
  and depth `≤ 3 * w + 1`.
* `Cslib.Complexity.detZModLanguage_mem_DET`,
  `Cslib.Complexity.DETk_subset_DET`,
  `Cslib.Complexity.DETkOn_subset_DETOn`: for every `k ≥ 2`,
  $\mathrm{det}_{\mathbb{Z}_k} \in \mathrm{DET}$ and $\mathrm{DET}_k \subseteq \mathrm{DET}$.
-/

public section

namespace Cslib.Complexity

open Cslib Cslib.Circuits Cslib.Circuits.Boolean

/-! ### Finite truth-table synthesis -/

section FiniteSynthesis

/-- Multiplexer circuit on 3 inputs `(cond, onTrue, onFalse) ↦ if cond then onTrue else onFalse`,
using 4 gates and depth 3. -/
private def mux1 : Circuit signature 3 1 :=
  let cTrue : Circuit signature 3 1 := Circuit.oneGate (σ := signature) .and ![0, 1]
  let notCond : Circuit signature 3 1 := Circuit.oneGate (σ := signature) .not ![0]
  let cFalse : Circuit signature 3 1 :=
    (Circuit.oneGate (σ := signature) .and ![0, 1]).comp
      (notCond.append (Circuit.wiring signature (fun _ : Fin 1 ↦ (2 : Fin 3))))
  (Circuit.oneGate (σ := signature) .or ![0, 1]).comp (cTrue.append cFalse)

private theorem eval_mux1 (x : Fin 3 → Bool) :
    mux1.eval interpretation x 0 = if x 0 then x 1 else x 2 := by
  let cTrue : Circuit signature 3 1 := Circuit.oneGate (σ := signature) .and ![0, 1]
  let notCond : Circuit signature 3 1 := Circuit.oneGate (σ := signature) .not ![0]
  let w2 : Circuit signature 3 1 := Circuit.wiring signature (fun _ : Fin 1 ↦ (2 : Fin 3))
  let cFalse : Circuit signature 3 1 :=
    (Circuit.oneGate (σ := signature) .and ![0, 1]).comp (notCond.append w2)
  change ((Circuit.oneGate (σ := signature) .or ![0, 1]).comp (cTrue.append cFalse)).eval
    interpretation x 0 = _
  rw [Circuit.eval_comp, Circuit.eval_oneGate]
  have hb0 : (cTrue.append cFalse).eval interpretation x (![0, 1] 0) = (x 0 && x 1) := by
    change (cTrue.append cFalse).eval interpretation x (Fin.castAdd 1 (0 : Fin 1)) = _
    rw [Circuit.eval_append, Fin.append_left]
    simp [cTrue, interpretation]
  have hb1 : (cTrue.append cFalse).eval interpretation x (![0, 1] 1) = (!x 0 && x 2) := by
    change (cTrue.append cFalse).eval interpretation x (Fin.natAdd 1 (0 : Fin 1)) = _
    rw [Circuit.eval_append, Fin.append_right]
    dsimp only [cFalse]
    rw [Circuit.eval_comp, Circuit.eval_oneGate]
    have ha0 : (notCond.append w2).eval interpretation x (![0, 1] 0) = !x 0 := by
      change (notCond.append w2).eval interpretation x (Fin.castAdd 1 (0 : Fin 1)) = _
      rw [Circuit.eval_append, Fin.append_left]
      simp [notCond, interpretation]
    have ha1 : (notCond.append w2).eval interpretation x (![0, 1] 1) = x 2 := by
      change (notCond.append w2).eval interpretation x (Fin.natAdd 1 (0 : Fin 1)) = _
      rw [Circuit.eval_append, Fin.append_right]
      simp [w2]
    change ((notCond.append w2).eval interpretation x (![0, 1] 0) &&
      (notCond.append w2).eval interpretation x (![0, 1] 1)) = _
    rw [ha0, ha1]
  change ((cTrue.append cFalse).eval interpretation x (![0, 1] 0) ||
    (cTrue.append cFalse).eval interpretation x (![0, 1] 1)) = _
  rw [hb0, hb1]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> rfl

private theorem size_mux1 : mux1.size = 4 := rfl

private theorem depth_mux1_le : mux1.depth ≤ 3 := by
  refine (Circuit.depth_comp_le _ _).trans ?_
  have h1 : (Circuit.oneGate (σ := signature) .and ![(0 : Fin 3), 1]).depth ≤ 1 := by simp
  have h2 : ((Circuit.oneGate (σ := signature) .and ![0, 1]).comp
      ((Circuit.oneGate (σ := signature) .not ![(0 : Fin 3)]).append
        (Circuit.wiring signature (fun _ : Fin 1 ↦ (2 : Fin 3))))).depth ≤ 2 := by
    refine (Circuit.depth_comp_le _ _).trans ?_
    have ha : ((Circuit.oneGate (σ := signature) .not ![(0 : Fin 3)]).append
        (Circuit.wiring signature (fun _ : Fin 1 ↦ (2 : Fin 3)))).depth ≤ 1 :=
      (Circuit.depth_append_le _ _).trans (max_le (by simp) (by simp))
    simp only [Circuit.depth_oneGate]; omega
  have happ := (Circuit.depth_append_le _ _).trans (max_le (h1.trans (by decide : 1 ≤ 2)) h2)
  simp only [Circuit.depth_oneGate]; omega

/-- Explicit finite truth-table circuit computing any `F : (Fin w → Bool) → Bool` in size
`≤ 5 * 2 ^ w` and depth `≤ 3 * w + 1`. -/
def truthTableCircuit1 : ∀ (w : ℕ), ((Fin w → Bool) → Bool) → Circuit signature w 1
  | 0, F => Circuit.oneGate (.const (F Fin.elim0)) Fin.elim0
  | w + 1, F =>
    let cT := (truthTableCircuit1 w (fun y ↦ F (Fin.cons true y))).comp
      (Circuit.wiring signature Fin.succ)
    let cF := (truthTableCircuit1 w (fun y ↦ F (Fin.cons false y))).comp
      (Circuit.wiring signature Fin.succ)
    mux1.comp ((Circuit.wiring signature (fun _ : Fin 1 ↦ (0 : Fin (w + 1)))).append
      (cT.append cF))

theorem eval_truthTableCircuit1 :
    ∀ (w : ℕ) (F : (Fin w → Bool) → Bool) (x : Fin w → Bool),
      (truthTableCircuit1 w F).eval interpretation x 0 = F x
  | 0, F, x => by have hx : x = Fin.elim0 := funext fun i ↦ Fin.elim0 i; subst hx; rfl
  | w + 1, F, x => by
    simp only [truthTableCircuit1, Circuit.eval_comp, eval_mux1]
    let cT := (truthTableCircuit1 w (fun y ↦ F (Fin.cons true y))).comp
      (Circuit.wiring signature Fin.succ)
    let cF := (truthTableCircuit1 w (fun y ↦ F (Fin.cons false y))).comp
      (Circuit.wiring signature Fin.succ)
    let w0 := Circuit.wiring signature (fun _ : Fin 1 ↦ (0 : Fin (w + 1)))
    have h0 : (w0.append (cT.append cF)).eval interpretation x 0 = x 0 := by
      have : (0 : Fin 3) = Fin.castAdd 2 (0 : Fin 1) := rfl
      rw [this, Circuit.eval_append, Fin.append_left, Circuit.eval_wiring]; rfl
    have h1 : (w0.append (cT.append cF)).eval interpretation x 1 =
        F (Fin.cons true (x ∘ Fin.succ)) := by
      have : (1 : Fin 3) = Fin.natAdd 1 (Fin.castAdd 1 (0 : Fin 1)) := rfl
      rw [this, Circuit.eval_append, Fin.append_right, Circuit.eval_append, Fin.append_left,
        Circuit.eval_comp, eval_truthTableCircuit1]; rfl
    have h2 : (w0.append (cT.append cF)).eval interpretation x 2 =
        F (Fin.cons false (x ∘ Fin.succ)) := by
      have : (2 : Fin 3) = Fin.natAdd 1 (Fin.natAdd 1 (0 : Fin 1)) := rfl
      rw [this, Circuit.eval_append, Fin.append_right, Circuit.eval_append, Fin.append_right,
        Circuit.eval_comp, eval_truthTableCircuit1]; rfl
    rw [h0, h1, h2]
    have hcons : Fin.cons (x 0) (x ∘ Fin.succ) = x := Fin.cons_self_tail x
    cases hx0 : x 0 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> rw [← hx0, hcons]

private theorem size_truthTableCircuit1_add_four_le :
    ∀ (w : ℕ) (F : (Fin w → Bool) → Bool), (truthTableCircuit1 w F).size + 4 ≤ 5 * 2 ^ w
  | 0, _ => by simp [truthTableCircuit1]
  | w + 1, F => by
    simp only [truthTableCircuit1, Circuit.size_comp, Circuit.size_append, size_mux1,
      Circuit.size_wiring, pow_succ']
    have hT := size_truthTableCircuit1_add_four_le w (fun y ↦ F (Fin.cons true y))
    have hF := size_truthTableCircuit1_add_four_le w (fun y ↦ F (Fin.cons false y))
    omega

theorem size_truthTableCircuit1_le (w : ℕ) (F : (Fin w → Bool) → Bool) :
    (truthTableCircuit1 w F).size ≤ 5 * 2 ^ w :=
  (Nat.le_add_right _ 4).trans (size_truthTableCircuit1_add_four_le w F)

theorem depth_truthTableCircuit1_le :
    ∀ (w : ℕ) (F : (Fin w → Bool) → Bool), (truthTableCircuit1 w F).depth ≤ 3 * w + 1
  | 0, _ => by simp [truthTableCircuit1]
  | w + 1, F => by
    dsimp only [truthTableCircuit1]; refine (Circuit.depth_comp_le _ _).trans ?_
    let w0 : Circuit signature (w + 1) 1 :=
      Circuit.wiring signature (fun _ : Fin 1 ↦ (0 : Fin (w + 1)))
    have hT : ((truthTableCircuit1 w (fun y ↦ F (Fin.cons true y))).comp
        (Circuit.wiring signature Fin.succ)).depth ≤ 3 * w + 1 := by
      refine (Circuit.depth_comp_le _ _).trans ?_
      have := depth_truthTableCircuit1_le w (fun y ↦ F (Fin.cons true y))
      simp only [Circuit.depth_wiring]; omega
    have hF : ((truthTableCircuit1 w (fun y ↦ F (Fin.cons false y))).comp
        (Circuit.wiring signature Fin.succ)).depth ≤ 3 * w + 1 := by
      refine (Circuit.depth_comp_le _ _).trans ?_
      have := depth_truthTableCircuit1_le w (fun y ↦ F (Fin.cons false y))
      simp only [Circuit.depth_wiring]; omega
    have happ₂ := (Circuit.depth_append_le _ _).trans (max_le hT hF)
    have hw0 : w0.depth ≤ 3 * w + 1 := by simp [w0]
    have happ₁ := (Circuit.depth_append_le w0 _).trans (max_le hw0 happ₂)
    dsimp only [w0] at happ₁; have hmux := depth_mux1_le; omega

/-- Multi-output finite truth-table circuit computing `F : (Fin w → Bool) → Fin out → Bool`. -/
def truthTableCircuit (w out : ℕ) (F : (Fin w → Bool) → Fin out → Bool) :
    Circuit signature w out :=
  Circuit.pi fun j ↦ truthTableCircuit1 w (fun x ↦ F x j)

theorem eval_truthTableCircuit (w out : ℕ) (F : (Fin w → Bool) → Fin out → Bool)
    (x : Fin w → Bool) :
    (truthTableCircuit w out F).eval interpretation x = F x := by
  funext j
  simp [truthTableCircuit, eval_truthTableCircuit1]

theorem size_truthTableCircuit_le (w out : ℕ) (F : (Fin w → Bool) → Fin out → Bool) :
    (truthTableCircuit w out F).size ≤ out * (5 * 2 ^ w) := by
  rw [truthTableCircuit, Circuit.size_pi]
  calc ∑ j : Fin out, (truthTableCircuit1 w (fun x ↦ F x j)).size
      ≤ ∑ _j : Fin out, 5 * 2 ^ w :=
        Finset.sum_le_sum fun j _ ↦ size_truthTableCircuit1_le w _
    _ = out * (5 * 2 ^ w) := by simp

theorem depth_truthTableCircuit_le (w out : ℕ) (F : (Fin w → Bool) → Fin out → Bool) :
    (truthTableCircuit w out F).depth ≤ 3 * w + 1 := by
  exact Circuit.depth_pi_le _ fun j ↦ depth_truthTableCircuit1_le w _

/-- Lift `fanInAtMost_mapOp_toOracle` from `Program` to `Circuit`. -/
theorem circuit_fanInAtMost_mapOp_toOracle {a b r : ℕ} (C : Circuit signature a b)
    (hr : 2 ≤ r) : (C.mapOp toOracle).FanInAtMost r :=
  fanInAtMost_mapOp_toOracle C.program hr

end FiniteSynthesis

/-! ### Reduction from $\mathrm{det}_{\mathbb{Z}_k}$ to $\mathrm{det}_{\mathbb{Z}}$ -/

section DetZModInDET

private theorem natAbs_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    (∑ i ∈ s, f i).natAbs ≤ ∑ i ∈ s, (f i).natAbs := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add_left ih _)

private theorem natAbs_prod_eq {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    (∏ i ∈ s, f i).natAbs = ∏ i ∈ s, (f i).natAbs := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Int.natAbs_mul, ih]

private theorem factorial_le_two_pow_sq : ∀ m : ℕ, m.factorial ≤ 2 ^ (m * m)
  | 0 => by simp
  | m + 1 => by
    rw [Nat.factorial_succ]
    have hm1 : m + 1 ≤ 2 ^ (2 * m + 1) :=
      (Nat.lt_two_pow_self (n := m + 1)).le.trans
        (Nat.pow_le_pow_right (by decide) (by omega))
    calc (m + 1) * m.factorial
        ≤ 2 ^ (2 * m + 1) * 2 ^ (m * m) := Nat.mul_le_mul hm1 (factorial_le_two_pow_sq m)
      _ = 2 ^ ((m + 1) * (m + 1)) := by rw [← pow_add]; congr 1; ring

private theorem det_int_natAbs_lt {m w : ℕ} (M : Matrix (Fin m) (Fin m) ℤ)
    (hM : ∀ i j, (M i j).natAbs < 2 ^ w) :
    M.det.natAbs < 2 ^ (m * m + m * w + 1) := by
  rw [Matrix.det_apply]
  have hterm (σ : Equiv.Perm (Fin m)) :
      (Equiv.Perm.sign σ • ∏ i : Fin m, M (σ i) i).natAbs ≤ 2 ^ (m * w) := by
    have hsign : (Equiv.Perm.sign σ • ∏ i : Fin m, M (σ i) i).natAbs =
        (∏ i : Fin m, M (σ i) i).natAbs := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
    rw [hsign, natAbs_prod_eq]
    calc ∏ i : Fin m, (M (σ i) i).natAbs
        ≤ ∏ _i : Fin m, 2 ^ w :=
          Finset.prod_le_prod fun i _ ↦ (hM (σ i) i).le
      _ = (2 ^ w) ^ m := by simp
      _ = 2 ^ (m * w) := by rw [← pow_mul, mul_comm]
  calc (∑ σ : Equiv.Perm (Fin m), Equiv.Perm.sign σ • ∏ i : Fin m, M (σ i) i).natAbs
      ≤ ∑ σ : Equiv.Perm (Fin m), (Equiv.Perm.sign σ • ∏ i : Fin m, M (σ i) i).natAbs :=
        natAbs_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin m), 2 ^ (m * w) :=
        Finset.sum_le_sum fun σ _ ↦ hterm σ
    _ = m.factorial * 2 ^ (m * w) := by simp [Fintype.card_perm]
    _ ≤ 2 ^ (m * m) * 2 ^ (m * w) := Nat.mul_le_mul_right _ (factorial_le_two_pow_sq m)
    _ = 2 ^ (m * m + m * w) := (pow_add 2 (m * m) (m * w)).symm
    _ < 2 ^ (m * m + m * w + 1) :=
        Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _)

private def andTree (t : ℕ) : Circuit signature t 1 :=
  Circuit.balanced (Circuit.oneGate .and ![0, 1])
    (Circuit.oneGate (.const true) Fin.elim0)
    (List.ofFn fun i : Fin t ↦ Circuit.wiring signature (fun _ : Fin 1 ↦ i))

private theorem eval_andTree (t : ℕ) (y : Fin t → Bool) :
    (andTree t).eval interpretation y 0 = decide (∀ i : Fin t, y i = true) := by
  have hfold : ∀ l : List (Circuit signature t 1),
      ((Circuit.balanced (Circuit.oneGate (σ := signature) .and ![0, 1])
        (Circuit.oneGate (σ := signature) (.const true) Fin.elim0) l).eval
        interpretation y) 0 =
        l.all (fun C ↦ C.eval interpretation y 0) := by
    intro l
    rw [Circuit.eval_balanced]
    refine List.balancedFold_induction
      (p := fun l (res : Fin 1 → Bool) ↦ res 0 = l.all (fun C ↦ C.eval interpretation y 0))
      (?_) (fun _ ↦ ?_) (fun l₁ l₂ r₁ r₂ _ _ ih₁ ih₂ ↦ ?_) l
    · rfl
    · simp
    · change (r₁ 0 && r₂ 0) = _
      rw [ih₁, ih₂, List.all_append]
  unfold andTree
  rw [hfold, Bool.eq_iff_iff, List.all_eq_true, decide_eq_true_eq]
  simp [List.mem_ofFn]

private theorem size_andTree_le (t : ℕ) : (andTree t).size ≤ t + 1 := by
  have h := Circuit.size_balanced_le (Circuit.oneGate (σ := signature) .and ![0, 1])
    (Circuit.oneGate (.const true) Fin.elim0)
    (List.ofFn fun i : Fin t ↦ Circuit.wiring signature (fun _ : Fin 1 ↦ i))
  have hsum : ((List.ofFn fun i : Fin t ↦
      Circuit.wiring signature (fun _ : Fin 1 ↦ i)).map Circuit.size).sum = 0 := by
    rw [List.map_ofFn]
    simp [Function.comp_def, Circuit.size_wiring]
  unfold andTree
  rw [hsum] at h
  simp only [Circuit.size_oneGate, List.length_ofFn, mul_one] at h
  omega

private theorem depth_andTree_le (t : ℕ) : (andTree t).depth ≤ 1 + Nat.clog 2 t := by
  have h := Circuit.depth_balanced_le_max (Circuit.oneGate (σ := signature) .and ![0, 1])
    (Circuit.oneGate (.const true) Fin.elim0) (D := 0)
    (l := List.ofFn fun i : Fin t ↦ Circuit.wiring signature (fun _ : Fin 1 ↦ i))
    (fun C hC ↦ by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hC
      simp)
  simpa [andTree] using h

private theorem zmodBitWidth_pos {k : ℕ} (hk : 2 ≤ k) : 0 < zmodBitWidth k :=
  Nat.pos_of_ne_zero fun h0 ↦ by
    have := Nat.lt_size_self k
    rw [show Nat.size k = 0 from h0] at this
    omega

private def decodeZMod (k : ℕ) (b : Fin (zmodBitWidth k) → Bool) : ZMod k :=
  (decodeBits b : ZMod k)

private def encodeZMod (k : ℕ) (z : ZMod k) : Fin (zmodBitWidth k) → Bool :=
  encodeBits (zmodBitWidth k) z.val

private theorem decode_encodeZMod {k : ℕ} [NeZero k] (z : ZMod k) :
    decodeZMod k (encodeZMod k z) = z := by
  unfold decodeZMod encodeZMod
  have hlt : z.val < 2 ^ zmodBitWidth k := (ZMod.val_lt z).trans (Nat.lt_size_self k)
  rw [decodeBits_encodeBits hlt, ZMod.natCast_zmod_val]

private def targetSlice (k m : ℕ) : Fin (zmodBitWidth k) → Fin (DetZModInstance.encodedLen k m) :=
  fun t ↦ Fin.castAdd (m * m * zmodBitWidth k) (Fin.natAdd (m + 1) t)

private def entrySlice (k m : ℕ) (p : Fin (m * m)) :
    Fin (zmodBitWidth k) → Fin (DetZModInstance.encodedLen k m) :=
  fun t ↦ Fin.natAdd ((m + 1) + zmodBitWidth k)
    ⟨p.val * zmodBitWidth k + t.val, by
      have hp := p.isLt; have ht := t.isLt; nlinarith⟩

private def headerWire (k m : ℕ) (i : Fin (m + 1)) : Fin (DetZModInstance.encodedLen k m) :=
  Fin.castAdd (m * m * zmodBitWidth k) (Fin.castAdd (zmodBitWidth k) i)

private def headerChecksCircuit (k m : ℕ) :
    Circuit signature (DetZModInstance.encodedLen k m) (m + 1) :=
  Circuit.pi fun i : Fin (m + 1) ↦
    if i.val < m then Circuit.wiring signature (fun _ : Fin 1 ↦ headerWire k m i)
    else
      (Circuit.oneGate (σ := signature) .not ![(0 : Fin 1)]).comp
        (Circuit.wiring signature (fun _ : Fin 1 ↦ headerWire k m i))

private def allValidCircuit (k m : ℕ) :
    Circuit signature (DetZModInstance.encodedLen k m) 1 :=
  let w := zmodBitWidth k
  let Q := DetZModInstance.encodedLen k m
  let ltKCheck : Circuit signature w 1 :=
    truthTableCircuit1 w fun b ↦ decide (decodeBits b < k)
  let targetLtK : Circuit signature Q 1 :=
    ltKCheck.comp (Circuit.wiring signature (targetSlice k m))
  let entriesLtK : Circuit signature Q (m * m) :=
    Circuit.pi fun p ↦ ltKCheck.comp (Circuit.wiring signature (entrySlice k m p))
  (andTree ((m + 1) + 1 + m * m)).comp
    (((headerChecksCircuit k m).append targetLtK).append entriesLtK)

private def clampedFlatCircuit (k : ℕ) (hk : 2 ≤ k) (m : ℕ) :
    Circuit signature (DetZModInstance.encodedLen k m) (m * m * zmodBitWidth k) :=
  let w := zmodBitWidth k
  have hw_pos : 0 < w := zmodBitWidth_pos hk
  let clampK : Circuit signature w w :=
    truthTableCircuit w w fun b ↦ if decodeBits b < k then b else encodeBits w 0
  Circuit.pi fun idx : Fin (m * m * w) ↦
    let p : Fin (m * m) :=
      ⟨idx.val / w, Nat.div_lt_of_lt_mul (by have hi := idx.isLt; nlinarith)⟩
    let t : Fin w := ⟨idx.val % w, Nat.mod_lt _ hw_pos⟩
    (Circuit.wiring signature (fun _ : Fin 1 ↦ t)).comp
      (clampK.comp (Circuit.wiring signature (entrySlice k m p)))

private def preLayerDM (k : ℕ) (hk : 2 ≤ k) (m : ℕ) :
    Circuit signature (DetZModInstance.encodedLen k m)
      (1 + zmodBitWidth k + m * m * zmodBitWidth k) :=
  (((allValidCircuit k m).append (Circuit.wiring signature (targetSlice k m))).append
    (clampedFlatCircuit k hk m))

private def detBoundB (k m : ℕ) : ℕ :=
  m * m + m * zmodBitWidth k + 1

private def intQuerySrc (k m : ℕ) (idx : Fin (detBoundB k m + 1)) :
    Fin (DetIntInstance.encodedLen m (zmodBitWidth k) idx.val) →
      Source (1 + zmodBitWidth k + m * m * zmodBitWidth k) :=
  let w := zmodBitWidth k
  Fin.addCases
    (Fin.addCases
      (Fin.addCases
        (fun i : Fin (m + 1) ↦ .inr (decide (i.val < m)))
        (fun i : Fin (w + 1) ↦ .inr (decide (i.val < w))))
      (fun i : Fin (idx.val + 1) ↦ .inr (decide (i.val < idx.val))))
    (fun p : Fin (m * m * (w + 1)) ↦
      let blk : Fin (m * m) :=
        ⟨p.val / (w + 1), Nat.div_lt_of_lt_mul (by have hp := p.isLt; nlinarith)⟩
      let off : ℕ := p.val % (w + 1)
      if hoff : off = 0 then .inr false
      else
        let t : Fin w := ⟨off - 1, by
          have : off < w + 1 := Nat.mod_lt p.val (Nat.succ_pos w)
          omega⟩
        .inl (Fin.natAdd (1 + w) ⟨blk.val * w + t.val, by
          have hb := blk.isLt; have ht := t.isLt; nlinarith⟩))

private def detZModMidLayer (k : ℕ) (hk : 2 ≤ k) (m : ℕ) :
    Circuit oracleSignature (DetZModInstance.encodedLen k m)
      ((1 + zmodBitWidth k) + (detBoundB k m + 1)) :=
  let w := zmodBitWidth k
  let B := detBoundB k m
  let preLayer : Circuit oracleSignature (DetZModInstance.encodedLen k m)
      (1 + w + m * m * w + 2) :=
    (constBank (1 + w + m * m * w)).comp ((preLayerDM k hk m).mapOp toOracle)
  let intQueries : Circuit oracleSignature (1 + w + m * m * w + 2) (B + 1) :=
    Circuit.pi fun idx : Fin (B + 1) ↦
      Circuit.oneGate (.query (DetIntInstance.encodedLen m w idx.val))
        fun a ↦ sourceWire (intQuerySrc k m idx a)
  let keepValidAndTarget : Circuit oracleSignature (1 + w + m * m * w + 2) (1 + w) :=
    Circuit.wiring oracleSignature fun i : Fin (1 + w) ↦
      sourceWire (Sum.inl (Fin.castAdd (m * m * w) i) : Source (1 + w + m * m * w))
  (keepValidAndTarget.append intQueries).comp preLayer

private def sumTreeCircuit (k m : ℕ) :
    Circuit signature ((1 + zmodBitWidth k) + (detBoundB k m + 1)) (zmodBitWidth k) :=
  let w := zmodBitWidth k
  let B := detBoundB k m
  let addZModOp : Circuit signature (w + w) w :=
    truthTableCircuit (w + w) w fun xy ↦
      encodeZMod k (decodeZMod k (xy ∘ Fin.castAdd w) + decodeZMod k (xy ∘ Fin.natAdd w))
  let zeroZModCircuit : Circuit signature ((1 + w) + (B + 1)) w :=
    Circuit.pi fun t ↦ Circuit.oneGate (.const (encodeZMod k 0 t)) Fin.elim0
  let bitTermCircuit (r : Fin B) : Circuit signature ((1 + w) + (B + 1)) w :=
    (truthTableCircuit 1 w fun b ↦
      if b 0 then encodeZMod k ((2 : ZMod k) ^ r.val) else encodeZMod k 0).comp
      (Circuit.wiring signature fun _ : Fin 1 ↦ Fin.natAdd (1 + w) r.succ)
  Circuit.balanced addZModOp zeroZModCircuit (List.ofFn bitTermCircuit)

private def postArgsCircuit (k m : ℕ) :
    Circuit signature ((1 + zmodBitWidth k) + (detBoundB k m + 1))
      (1 + (1 + (zmodBitWidth k + zmodBitWidth k))) :=
  let w := zmodBitWidth k
  let B := detBoundB k m
  let validW : Circuit signature ((1 + w) + (B + 1)) 1 :=
    Circuit.wiring signature fun _ ↦ Fin.castAdd (B + 1) (Fin.castAdd w 0)
  let negW : Circuit signature ((1 + w) + (B + 1)) 1 :=
    Circuit.wiring signature fun _ ↦ Fin.natAdd (1 + w) 0
  let tgtW : Circuit signature ((1 + w) + (B + 1)) w :=
    Circuit.wiring signature fun t ↦ Fin.castAdd (B + 1) (Fin.natAdd 1 t)
  validW.append (negW.append ((sumTreeCircuit k m).append tgtW))

private def finalVerdictFn (k : ℕ)
    (args : Fin (1 + (1 + (zmodBitWidth k + zmodBitWidth k))) → Bool) : Bool :=
  let w := zmodBitWidth k
  let validAll := args (Fin.castAdd (1 + (w + w)) 0)
  let rest₁ := args ∘ Fin.natAdd 1
  let negBit := rest₁ (Fin.castAdd (w + w) 0)
  let rest₂ := rest₁ ∘ Fin.natAdd 1
  let sumVal := decodeZMod k (rest₂ ∘ Fin.castAdd w)
  let tgtVal := decodeZMod k (rest₂ ∘ Fin.natAdd w)
  validAll && decide ((if negBit then -sumVal else sumVal) = tgtVal)

private def detZModPostLayerDM (k m : ℕ) :
    Circuit signature ((1 + zmodBitWidth k) + (detBoundB k m + 1)) 1 :=
  let w := zmodBitWidth k
  (truthTableCircuit1 (1 + (1 + (w + w))) (finalVerdictFn k)).comp (postArgsCircuit k m)

private def detZModFullCircuit (k : ℕ) (hk : 2 ≤ k) (m : ℕ) :
    Circuit oracleSignature (DetZModInstance.encodedLen k m) 1 :=
  ((detZModPostLayerDM k m).mapOp toOracle).comp (detZModMidLayer k hk m)

private theorem size_detZModFullCircuit_le {k : ℕ} (hk : 2 ≤ k) (m : ℕ) :
    (detZModFullCircuit k hk m).size ≤
      (20 * 2 ^ (2 * zmodBitWidth k + 2) + 20) * (DetZModInstance.encodedLen k m + 2) ^ 3 := by
  set w := zmodBitWidth k
  set Q := DetZModInstance.encodedLen k m
  set B := detBoundB k m
  have hw_pos : 0 < w := zmodBitWidth_pos hk
  have hQ_eq : Q = (m + 1) + w + m * m * w := rfl
  have hB_eq : B = m * m + m * w + 1 := rfl
  have hmmw : m * m * w ≤ Q := by omega
  have hmm : m * m ≤ Q := le_trans (Nat.le_mul_of_pos_right _ hw_pos) hmmw
  have hmw : m * w ≤ Q := by
    rcases Nat.eq_zero_or_pos m with rfl | hm_pos
    · simp
    · have : m * 1 * w ≤ m * m * w := Nat.mul_le_mul_right w (Nat.mul_le_mul_left m hm_pos)
      rw [mul_one] at this; omega
  have hB_le : B ≤ (Q + 2) ^ 2 := by nlinarith
  have hsize_head : (headerChecksCircuit k m).size ≤ m + 1 := by
    unfold headerChecksCircuit
    rw [Circuit.size_pi]
    calc ∑ i : Fin (m + 1), _ ≤ ∑ _i : Fin (m + 1), 1 :=
          Finset.sum_le_sum fun i _ ↦ by split_ifs <;> simp
      _ = m + 1 := by simp
  have hsize_valid : (allValidCircuit k m).size ≤
      (2 * m + 4 + m * m) + (1 + m * m) * (5 * 2 ^ w) := by
    unfold allValidCircuit
    simp only [Circuit.size_comp, Circuit.size_append, Circuit.size_wiring]
    have htlt : (truthTableCircuit1 (zmodBitWidth k) fun b ↦ decide (decodeBits b < k)).size ≤
        5 * 2 ^ w := size_truthTableCircuit1_le (zmodBitWidth k) _
    have helt : (Circuit.pi fun p : Fin (m * m) ↦
        (truthTableCircuit1 (zmodBitWidth k) fun b ↦ decide (decodeBits b < k)).comp
          (Circuit.wiring signature (entrySlice k m p))).size ≤ m * m * (5 * 2 ^ w) := by
      rw [Circuit.size_pi]
      calc ∑ p : Fin (m * m), _ ≤ ∑ _p : Fin (m * m), 5 * 2 ^ w :=
            Finset.sum_le_sum fun p _ ↦ by
              simpa [Circuit.size_comp] using size_truthTableCircuit1_le (zmodBitWidth k) _
        _ = m * m * (5 * 2 ^ w) := by simp
    have hand := size_andTree_le ((m + 1) + 1 + m * m)
    rw [add_mul, one_mul]
    omega
  have hsize_clamp : (clampedFlatCircuit k hk m).size ≤ m * m * w * (w * (5 * 2 ^ w)) := by
    unfold clampedFlatCircuit
    rw [Circuit.size_pi]
    calc ∑ idx : Fin (m * m * w), _ ≤ ∑ _idx : Fin (m * m * w), w * (5 * 2 ^ w) :=
          Finset.sum_le_sum fun idx _ ↦ by
            simpa [Circuit.size_comp] using size_truthTableCircuit_le w w _
      _ = m * m * w * (w * (5 * 2 ^ w)) := by simp
  have hsize_preDM : (preLayerDM k hk m).size ≤
      (2 * m + 4 + m * m) + (1 + m * m) * (5 * 2 ^ w) + m * m * w * (w * (5 * 2 ^ w)) := by
    unfold preLayerDM
    simp only [Circuit.size_append, Circuit.size_wiring]
    omega
  have hsize_mid : (detZModMidLayer k hk m).size ≤
      2 + (2 * m + 4 + m * m) + (1 + m * m) * (5 * 2 ^ w) +
        m * m * w * (w * (5 * 2 ^ w)) + (B + 1) := by
    unfold detZModMidLayer
    simp only [Circuit.size_comp, Circuit.size_append, Circuit.size_wiring, size_constBank,
      Circuit.size_mapOp, Circuit.size_pi, Circuit.size_oneGate, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_one]
    omega
  have hsize_post : (detZModPostLayerDM k m).size ≤
      5 * 2 ^ (2 * w + 2) + w + B * (w * 10) + B * (w * (5 * 2 ^ (w + w))) := by
    have hsum : (sumTreeCircuit k m).size ≤
        w + B * (w * 10) + B * (w * (5 * 2 ^ (w + w))) := by
      unfold sumTreeCircuit
      have hb := Circuit.size_balanced_le
        (truthTableCircuit (w + w) w fun xy ↦
          encodeZMod k (decodeZMod k (xy ∘ Fin.castAdd w) + decodeZMod k (xy ∘ Fin.natAdd w)))
        (Circuit.pi fun t ↦ Circuit.oneGate (.const (encodeZMod k 0 t)) Fin.elim0)
        (List.ofFn fun r : Fin B ↦
          (truthTableCircuit 1 w fun b ↦
            if b 0 then encodeZMod k ((2 : ZMod k) ^ r.val) else encodeZMod k 0).comp
            (Circuit.wiring signature fun _ : Fin 1 ↦ Fin.natAdd (1 + w) r.succ))
      have hzero : (Circuit.pi (n := (1 + w) + (B + 1)) fun t : Fin w ↦
          Circuit.oneGate (σ := signature) (.const (encodeZMod k 0 t)) Fin.elim0).size = w := by
        simp
      have hadd := size_truthTableCircuit_le (w + w) w (fun xy ↦
        encodeZMod k (decodeZMod k (xy ∘ Fin.castAdd w) + decodeZMod k (xy ∘ Fin.natAdd w)))
      have hlist : ((List.ofFn fun r : Fin B ↦
          ((truthTableCircuit 1 w fun b ↦
            if b 0 then encodeZMod k ((2 : ZMod k) ^ r.val) else encodeZMod k 0).comp
            (Circuit.wiring signature fun _ : Fin 1 ↦ Fin.natAdd (1 + w) r.succ))).map
          Circuit.size).sum ≤ B * (w * 10) := by
        rw [List.map_ofFn]
        calc (List.ofFn fun r : Fin B ↦ _).sum = ∑ r : Fin B, _ := List.sum_ofFn
          _ ≤ ∑ _r : Fin B, w * 10 := Finset.sum_le_sum fun r _ ↦ by
                simpa [Circuit.size_comp] using size_truthTableCircuit_le 1 w _
          _ = B * (w * 10) := by simp
      rw [List.length_ofFn, hzero] at hb
      exact hb.trans (Nat.add_le_add (Nat.add_le_add_left hlist w) (Nat.mul_le_mul_left B hadd))
    have hfin : (truthTableCircuit1 (1 + (1 + (zmodBitWidth k + zmodBitWidth k)))
        (finalVerdictFn k)).size ≤ 5 * 2 ^ (2 * w + 2) := by
      have heq : 1 + (1 + (zmodBitWidth k + zmodBitWidth k)) = 2 * w + 2 := by
        dsimp only [w]; omega
      simpa [heq] using
        size_truthTableCircuit1_le (1 + (1 + (zmodBitWidth k + zmodBitWidth k))) (finalVerdictFn k)
    unfold detZModPostLayerDM postArgsCircuit
    simp only [Circuit.size_comp, Circuit.size_append, Circuit.size_wiring]
    omega
  change (detZModFullCircuit k hk m).size ≤ (20 * 2 ^ (2 * w + 2) + 20) * (Q + 2) ^ 3
  unfold detZModFullCircuit
  rw [Circuit.size_comp, Circuit.size_mapOp]
  have hpow_1 : 5 * 2 ^ w ≤ 5 * 2 ^ (2 * w + 2) :=
    Nat.mul_le_mul_left 5 (Nat.pow_le_pow_right (by decide) (by omega))
  have hpow_w : w * (5 * 2 ^ (w + w)) ≤ 5 * 2 ^ (2 * w + 2) * (Q + 2) := by
    have h2 : 2 ^ (w + w) ≤ 2 ^ (2 * w + 2) := Nat.pow_le_pow_right (by decide) (by omega)
    calc w * (5 * 2 ^ (w + w)) = (5 * 2 ^ (w + w)) * w := by ring
      _ ≤ (5 * 2 ^ (2 * w + 2)) * (Q + 2) := Nat.mul_le_mul (Nat.mul_le_mul_left 5 h2) (by omega)
  have h10 : w * 10 ≤ 5 * 2 ^ (2 * w + 2) := by
    have hw2 : w ≤ 2 ^ w := Nat.lt_two_pow_self.le
    have h2w : 2 * 2 ^ w ≤ 2 ^ (2 * w + 2) := by
      rw [show 2 * 2 ^ w = 2 ^ (w + 1) from (pow_succ' 2 w).symm]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    calc w * 10 = 5 * (2 * w) := by ring
      _ ≤ 5 * (2 * 2 ^ w) := Nat.mul_le_mul_left 5 (Nat.mul_le_mul_left 2 hw2)
      _ ≤ 5 * 2 ^ (2 * w + 2) := Nat.mul_le_mul_left 5 h2w
  have hQ1 : Q + 2 ≤ (Q + 2) ^ 3 :=
    (pow_one (Q + 2)).symm.trans_le (Nat.pow_le_pow_right (by omega) (by decide))
  have hQ2 : (Q + 2) ^ 2 ≤ (Q + 2) ^ 3 := Nat.pow_le_pow_right (by omega) (by decide)
  have helt_fin_b :
      5 * 2 ^ (2 * w + 2) + (1 + m * m) * (5 * 2 ^ w) ≤ 5 * 2 ^ (2 * w + 2) * (Q + 2) ^ 3 :=
    (Nat.add_le_add (by simp) (Nat.mul_le_mul_left _ hpow_1)).trans <|
      (show 1 * (5 * 2 ^ (2 * w + 2)) + (1 + m * m) * (5 * 2 ^ (2 * w + 2)) =
          (2 + m * m) * (5 * 2 ^ (2 * w + 2)) by ring).trans_le <|
        (Nat.mul_le_mul_right _ ((show 2 + m * m ≤ Q + 2 by omega).trans hQ1)).trans_eq (by ring)
  have hclamp_b : m * m * w * (w * (5 * 2 ^ w)) ≤ 5 * 2 ^ (2 * w + 2) * (Q + 2) ^ 3 :=
    (show m * m * w * (w * (5 * 2 ^ w)) = (m * m * w * w) * (5 * 2 ^ w) by ring).trans_le <|
      (Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) hpow_1).trans <|
        (show ((Q + 2) * (Q + 2)) * (5 * 2 ^ (2 * w + 2)) =
            5 * 2 ^ (2 * w + 2) * (Q + 2) ^ 2 by ring).trans_le (Nat.mul_le_mul_left _ hQ2)
  have h10_b : B * (w * 10) ≤ 5 * 2 ^ (2 * w + 2) * (Q + 2) ^ 3 :=
    (Nat.mul_le_mul (hB_le.trans hQ2) h10).trans_eq (by ring)
  have hsum_b : B * (w * (5 * 2 ^ (w + w))) ≤ 5 * 2 ^ (2 * w + 2) * (Q + 2) ^ 3 :=
    (Nat.mul_le_mul hB_le hpow_w).trans_eq (by ring)
  have hsmall_b : w + (B + 1) + 2 + (2 * m + 4 + m * m) ≤ 20 * (Q + 2) ^ 3 := by
    have : B ≤ (Q + 2) ^ 3 := hB_le.trans hQ2; omega
  rw [add_mul]
  have h20 : 20 * 2 ^ (2 * w + 2) * (Q + 2) ^ 3 = 4 * (5 * 2 ^ (2 * w + 2) * (Q + 2) ^ 3) := by
    ring
  rw [h20]; omega

private theorem fanIn_detZModFullCircuit {k : ℕ} (hk : 2 ≤ k) (m : ℕ) :
    (detZModFullCircuit k hk m).FanInAtMost
      ((20 * 2 ^ (2 * zmodBitWidth k + 2) + 20) * (DetZModInstance.encodedLen k m + 2) ^ 3) := by
  set w := zmodBitWidth k; set Q := DetZModInstance.encodedLen k m; set B := detBoundB k m
  set R := (20 * 2 ^ (2 * w + 2) + 20) * (Q + 2) ^ 3
  have hw_pos : 0 < w := zmodBitWidth_pos hk
  have hQ_eq : Q = (m + 1) + w + m * m * w := rfl
  have hB_eq : B = m * m + m * w + 1 := rfl
  have h2R : 2 ≤ R := by
    have h1 : 1 ≤ (Q + 2) ^ 3 := Nat.one_le_pow 3 (Q + 2) (by omega)
    exact (Nat.mul_one 2).symm.trans_le (Nat.mul_le_mul (by omega) h1)
  unfold detZModFullCircuit detZModMidLayer
  refine (circuit_fanInAtMost_mapOp_toOracle _ h2R).comp <|
    ((Circuit.fanInAtMost_wiring _ _).append ?_).comp
      ((fanInAtMost_constBank _ _).comp (circuit_fanInAtMost_mapOp_toOracle _ h2R))
  refine Circuit.fanInAtMost_pi fun idx ↦ (Circuit.fanInAtMost_oneGate _ _ _).2 ?_
  change DetIntInstance.encodedLen m w idx.val ≤ R
  have hidx : idx.val ≤ B := Nat.lt_succ_iff.mp idx.isLt
  have hmmw : m * m * w ≤ Q := by omega
  have hmm : m * m ≤ Q := le_trans (Nat.le_mul_of_pos_right _ hw_pos) hmmw
  have hmw : m * w ≤ Q := by
    rcases Nat.eq_zero_or_pos m with rfl | hm_pos
    · simp
    · have : m * 1 * w ≤ m * m * w := Nat.mul_le_mul_right w (Nat.mul_le_mul_left m hm_pos)
      rw [mul_one] at this; omega
  dsimp only [R]
  rw [DetIntInstance.encodedLen_eq]
  have henc_le : (m + 1) + (w + 1) + (idx.val + 1) + m * m * (w + 1) ≤ 20 * (Q + 2) ^ 3 := by
    have h1 : m * m * (w + 1) = m * m * w + m * m := by ring
    have hQ1 : Q + 2 ≤ (Q + 2) ^ 3 :=
      (pow_one (Q + 2)).symm.trans_le (Nat.pow_le_pow_right (by omega) (by decide))
    omega
  exact henc_le.trans (Nat.mul_le_mul_right ((Q + 2) ^ 3) (by omega))

private theorem depthWith_append_le_of_le {σ : Signature} {n m p D : ℕ}
    (cost : σ.Op → ℕ) (c : Circuit σ n m) (d : Circuit σ n p)
    (hc : c.depthWith cost ≤ D) (hd : d.depthWith cost ≤ D) :
    (c.append d).depthWith cost ≤ D :=
  (Circuit.depthWith_append_le cost c d).trans <| by
    by_cases h : c.depthWith cost ≤ d.depthWith cost
    · rw [max_eq_right h]; exact hd
    · rw [max_eq_left (le_of_not_ge h)]; exact hc

private theorem depth_append_le_of_le {σ : Signature} {n m p D : ℕ}
    (c : Circuit σ n m) (d : Circuit σ n p) (hc : c.depth ≤ D) (hd : d.depth ≤ D) :
    (c.append d).depth ≤ D := by
  rw [← Circuit.depthWith_one] at hc hd ⊢; exact depthWith_append_le_of_le 1 c d hc hd

private theorem depth_comp_le_of_le {σ : Signature} {n m p D₁ D₂ : ℕ}
    (d : Circuit σ m p) (c : Circuit σ n m) (hd : d.depth ≤ D₁) (hc : c.depth ≤ D₂) :
    (d.comp c).depth ≤ D₁ + D₂ := by
  rw [← Circuit.depthWith_one] at hd hc ⊢
  exact (Circuit.depthWith_comp_le 1 d c).trans (Nat.add_le_add hd hc)

private theorem q2_le_two_pow_log {k m : ℕ} :
    DetZModInstance.encodedLen k m + 2 ≤
      2 ^ (Nat.log 2 (DetZModInstance.encodedLen k m) + 2) := by
  have hlt := Nat.lt_pow_succ_log_self Nat.one_lt_two (DetZModInstance.encodedLen k m)
  have h1 : 1 ≤ 2 ^ Nat.log 2 (DetZModInstance.encodedLen k m) := Nat.one_le_pow _ 2 (by decide)
  rw [pow_succ] at hlt; rw [pow_succ, pow_succ]; omega

private theorem clog_le_six_log {k m X : ℕ}
    (hX : X ≤ (DetZModInstance.encodedLen k m + 2) ^ 3) :
    Nat.clog 2 X ≤ 6 * (Nat.log 2 (DetZModInstance.encodedLen k m) + 1) := by
  refine (Nat.clog_le_iff_le_pow (by decide)).mpr <| hX.trans ?_
  calc (DetZModInstance.encodedLen k m + 2) ^ 3
      ≤ (2 ^ (Nat.log 2 (DetZModInstance.encodedLen k m) + 2)) ^ 3 :=
        Nat.pow_le_pow_left q2_le_two_pow_log 3
    _ = 2 ^ ((Nat.log 2 (DetZModInstance.encodedLen k m) + 2) * 3) := (pow_mul 2 _ 3).symm
    _ ≤ 2 ^ (6 * (Nat.log 2 (DetZModInstance.encodedLen k m) + 1)) :=
        Nat.pow_le_pow_right (by decide) (by omega)

private theorem depthWith_mapOp_toOracle_eq {a b : ℕ} (D : Circuit signature a b) :
    (D.mapOp toOracle).depthWith nc1OracleDepthWeight = D.depth := by
  rw [Circuit.depthWith_mapOp]; exact D.depthWith_one

private theorem depth_headerChecksCircuit_le (k m : ℕ) :
    (headerChecksCircuit k m).depth ≤ 1 := by
  unfold headerChecksCircuit
  refine Circuit.depth_pi_le _ fun i ↦ ?_
  split_ifs
  · exact (Circuit.depth_wiring _).trans_le (Nat.zero_le _)
  · exact (depth_comp_le_of_le (D₁ := 1) (D₂ := 0) _ _
      (by simp) (Circuit.depth_wiring _).le).trans (by omega)

private theorem depth_allValidCircuit_le {k : ℕ} (hk : 2 ≤ k) (m : ℕ) :
    (allValidCircuit k m).depth ≤
      (3 * zmodBitWidth k + 2) + 6 * (Nat.log 2 (DetZModInstance.encodedLen k m) + 1) := by
  have hw_pos : 0 < zmodBitWidth k := zmodBitWidth_pos hk
  have hQ_eq := DetZModInstance.encodedLen_eq k m
  have hmm : m * m ≤ DetZModInstance.encodedLen k m :=
    le_trans (Nat.le_mul_of_pos_right _ hw_pos) (by omega)
  have h2Q_pow : 2 * (DetZModInstance.encodedLen k m + 2) ≤
      (DetZModInstance.encodedLen k m + 2) ^ 3 :=
    calc 2 * (DetZModInstance.encodedLen k m + 2)
        ≤ (DetZModInstance.encodedLen k m + 2) * (DetZModInstance.encodedLen k m + 2) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = (DetZModInstance.encodedLen k m + 2) ^ 2 := (sq _).symm
      _ ≤ (DetZModInstance.encodedLen k m + 2) ^ 3 := Nat.pow_le_pow_right (by omega) (by decide)
  have hclog := clog_le_six_log (k := k) (m := m) (X := (m + 1) + 1 + m * m) (by omega)
  unfold allValidCircuit
  refine (depth_comp_le_of_le (D₂ := 3 * zmodBitWidth k + 1) _ _
    ((depth_andTree_le ((m + 1) + 1 + m * m)).trans (Nat.add_le_add_left hclog 1)) ?_).trans
    (by omega)
  refine depth_append_le_of_le _ _
    (depth_append_le_of_le _ _ ((depth_headerChecksCircuit_le k m).trans (by omega))
      ((depth_comp_le_of_le _ _ (depth_truthTableCircuit1_le (zmodBitWidth k) _)
        (Circuit.depth_wiring _).le).trans_eq (Nat.add_zero _)))
    (Circuit.depth_pi_le _ fun _ ↦
      (depth_comp_le_of_le _ _ (depth_truthTableCircuit1_le (zmodBitWidth k) _)
        (Circuit.depth_wiring _).le).trans_eq (Nat.add_zero _))

private theorem depth_clampedFlatCircuit_le {k : ℕ} (hk : 2 ≤ k) (m : ℕ) :
    (clampedFlatCircuit k hk m).depth ≤ 3 * zmodBitWidth k + 1 := by
  unfold clampedFlatCircuit
  refine Circuit.depth_pi_le _ fun _ ↦ ?_
  refine (depth_comp_le_of_le (D₂ := 3 * zmodBitWidth k + 1) _ _
    (Circuit.depth_wiring _).le ?_).trans_eq (Nat.zero_add _)
  exact (depth_comp_le_of_le _ _ (depth_truthTableCircuit_le (zmodBitWidth k) (zmodBitWidth k) _)
    (Circuit.depth_wiring _).le).trans_eq (Nat.add_zero _)

private theorem depth_preLayerDM_le {k : ℕ} (hk : 2 ≤ k) (m : ℕ) :
    (preLayerDM k hk m).depth ≤
      (3 * zmodBitWidth k + 2) + 6 * (Nat.log 2 (DetZModInstance.encodedLen k m) + 1) := by
  unfold preLayerDM
  exact depth_append_le_of_le _ _
    (depth_append_le_of_le _ _ (depth_allValidCircuit_le hk m)
      ((Circuit.depth_wiring _).trans_le (Nat.zero_le _)))
    ((depth_clampedFlatCircuit_le hk m).trans (by omega))

private theorem depthWith_detZModMidLayer_le {k : ℕ} (hk : 2 ≤ k) (m : ℕ) :
    (detZModMidLayer k hk m).depthWith nc1OracleDepthWeight ≤
      (3 * zmodBitWidth k + 4) + 12 * (Nat.log 2 (DetZModInstance.encodedLen k m) + 1) := by
  have hw_pos : 0 < zmodBitWidth k := zmodBitWidth_pos hk
  have hQ_eq := DetZModInstance.encodedLen_eq k m
  have hB_eq : detBoundB k m = m * m + m * zmodBitWidth k + 1 := rfl
  have hmmw : m * m * zmodBitWidth k ≤ DetZModInstance.encodedLen k m := by omega
  have hmm : m * m ≤ DetZModInstance.encodedLen k m :=
    le_trans (Nat.le_mul_of_pos_right _ hw_pos) hmmw
  have hmw : m * zmodBitWidth k ≤ DetZModInstance.encodedLen k m := by
    rcases Nat.eq_zero_or_pos m with rfl | hm_pos
    · simp
    · have : m * 1 * zmodBitWidth k ≤ m * m * zmodBitWidth k :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left m hm_pos)
      rw [mul_one] at this; omega
  let preLayer : Circuit oracleSignature (DetZModInstance.encodedLen k m)
      (1 + zmodBitWidth k + m * m * zmodBitWidth k + 2) :=
    (constBank (1 + zmodBitWidth k + m * m * zmodBitWidth k)).comp
      ((preLayerDM k hk m).mapOp toOracle)
  let intQueries : Circuit oracleSignature (1 + zmodBitWidth k + m * m * zmodBitWidth k + 2)
      (detBoundB k m + 1) :=
    Circuit.pi fun idx : Fin (detBoundB k m + 1) ↦
      Circuit.oneGate (.query (DetIntInstance.encodedLen m (zmodBitWidth k) idx.val))
        fun a ↦ sourceWire (intQuerySrc k m idx a)
  let keepValidAndTarget :
      Circuit oracleSignature (1 + zmodBitWidth k + m * m * zmodBitWidth k + 2)
        (1 + zmodBitWidth k) :=
    Circuit.wiring oracleSignature fun i : Fin (1 + zmodBitWidth k) ↦
      sourceWire (Sum.inl (Fin.castAdd (m * m * zmodBitWidth k) i) :
        Source (1 + zmodBitWidth k + m * m * zmodBitWidth k))
  have hpre : preLayer.depthWith nc1OracleDepthWeight ≤
      (3 * zmodBitWidth k + 3) + 6 * (Nat.log 2 (DetZModInstance.encodedLen k m) + 1) := by
    refine (Circuit.depthWith_comp_le (σ := oracleSignature) nc1OracleDepthWeight
      (constBank (1 + zmodBitWidth k + m * m * zmodBitWidth k))
      ((preLayerDM k hk m).mapOp toOracle)).trans ?_
    have hconst := depthWith_constBank_nc1_le (1 + zmodBitWidth k + m * m * zmodBitWidth k)
    have hpreDM := depth_preLayerDM_le hk m
    rw [depthWith_mapOp_toOracle_eq]; omega
  have happ : (keepValidAndTarget.append intQueries).depthWith nc1OracleDepthWeight ≤
      6 * (Nat.log 2 (DetZModInstance.encodedLen k m) + 1) + 1 := by
    refine depthWith_append_le_of_le (σ := oracleSignature) nc1OracleDepthWeight
      keepValidAndTarget intQueries
      ((Circuit.depthWith_wiring _ _).trans_le (Nat.zero_le _)) ?_
    refine Circuit.depthWith_pi_le (σ := oracleSignature) nc1OracleDepthWeight _ fun idx ↦ ?_
    simp only [Circuit.depthWith_oneGate, nc1OracleDepthWeight_query]
    have hlen_le : DetIntInstance.encodedLen m (zmodBitWidth k) idx.val ≤
        (DetZModInstance.encodedLen k m + 2) ^ 3 := by
      have hidx : idx.val ≤ detBoundB k m := Nat.lt_succ_iff.mp idx.isLt
      rw [DetIntInstance.encodedLen_eq]
      have h1 : m * m * (zmodBitWidth k + 1) = m * m * zmodBitWidth k + m * m := by ring
      have h16 : 5 ≤ (DetZModInstance.encodedLen k m + 2) *
          (DetZModInstance.encodedLen k m + 2) := by
        have h4 : 4 ≤ DetZModInstance.encodedLen k m + 2 := by omega
        have := Nat.mul_le_mul h4 h4; omega
      have h5Q : 5 * (DetZModInstance.encodedLen k m + 2) ≤
          (DetZModInstance.encodedLen k m + 2) ^ 3 :=
        calc 5 * (DetZModInstance.encodedLen k m + 2)
            ≤ ((DetZModInstance.encodedLen k m + 2) * (DetZModInstance.encodedLen k m + 2)) *
              (DetZModInstance.encodedLen k m + 2) := Nat.mul_le_mul_right _ h16
          _ = (DetZModInstance.encodedLen k m + 2) ^ 3 := by ring
      omega
    have hlog : Nat.log 2 (DetIntInstance.encodedLen m (zmodBitWidth k) idx.val) ≤
        6 * (Nat.log 2 (DetZModInstance.encodedLen k m) + 1) := by
      by_cases h0 : DetIntInstance.encodedLen m (zmodBitWidth k) idx.val = 0
      · simp [h0]
      · have h2 : DetIntInstance.encodedLen m (zmodBitWidth k) idx.val <
            2 ^ (6 * (Nat.log 2 (DetZModInstance.encodedLen k m) + 1) + 1) :=
          calc DetIntInstance.encodedLen m (zmodBitWidth k) idx.val
              ≤ (DetZModInstance.encodedLen k m + 2) ^ 3 := hlen_le
            _ ≤ (2 ^ (Nat.log 2 (DetZModInstance.encodedLen k m) + 2)) ^ 3 :=
                Nat.pow_le_pow_left q2_le_two_pow_log 3
            _ = 2 ^ ((Nat.log 2 (DetZModInstance.encodedLen k m) + 2) * 3) := (pow_mul 2 _ 3).symm
            _ < 2 ^ (6 * (Nat.log 2 (DetZModInstance.encodedLen k m) + 1) + 1) :=
                Nat.pow_lt_pow_right (by decide) (by omega)
        exact Nat.lt_succ_iff.mp ((Nat.log_lt_iff_lt_pow (by decide) h0).mpr h2)
    omega
  change ((keepValidAndTarget.append intQueries).comp preLayer).depthWith nc1OracleDepthWeight ≤ _
  exact (Circuit.depthWith_comp_le (σ := oracleSignature) nc1OracleDepthWeight
    (keepValidAndTarget.append intQueries) preLayer).trans
    ((Nat.add_le_add happ hpre).trans (by omega))

private theorem depth_detZModPostLayerDM_le {k : ℕ} (hk : 2 ≤ k) (m : ℕ) :
    (detZModPostLayerDM k m).depth ≤
      (6 * zmodBitWidth k + 11) +
        (6 * zmodBitWidth k + 1) * (6 * (Nat.log 2 (DetZModInstance.encodedLen k m) + 1)) := by
  have hw_pos : 0 < zmodBitWidth k := zmodBitWidth_pos hk
  have hQ_eq := DetZModInstance.encodedLen_eq k m
  have hB_eq : detBoundB k m = m * m + m * zmodBitWidth k + 1 := rfl
  have hmmw : m * m * zmodBitWidth k ≤ DetZModInstance.encodedLen k m := by omega
  have hmm : m * m ≤ DetZModInstance.encodedLen k m :=
    le_trans (Nat.le_mul_of_pos_right _ hw_pos) hmmw
  have hmw : m * zmodBitWidth k ≤ DetZModInstance.encodedLen k m := by
    rcases Nat.eq_zero_or_pos m with rfl | hm_pos
    · simp
    · have : m * 1 * zmodBitWidth k ≤ m * m * zmodBitWidth k :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left m hm_pos)
      rw [mul_one] at this; omega
  have h2Q_pow : 2 * (DetZModInstance.encodedLen k m + 2) ≤
      (DetZModInstance.encodedLen k m + 2) ^ 3 :=
    calc 2 * (DetZModInstance.encodedLen k m + 2)
        ≤ (DetZModInstance.encodedLen k m + 2) * (DetZModInstance.encodedLen k m + 2) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = (DetZModInstance.encodedLen k m + 2) ^ 2 := (sq _).symm
      _ ≤ (DetZModInstance.encodedLen k m + 2) ^ 3 := Nat.pow_le_pow_right (by omega) (by decide)
  have hsum : (sumTreeCircuit k m).depth ≤
      4 + (6 * zmodBitWidth k + 1) * (6 * (Nat.log 2 (DetZModInstance.encodedLen k m) + 1)) := by
    let addZModOp : Circuit signature (zmodBitWidth k + zmodBitWidth k) (zmodBitWidth k) :=
      truthTableCircuit (zmodBitWidth k + zmodBitWidth k) (zmodBitWidth k) fun xy ↦
        encodeZMod k (decodeZMod k (xy ∘ Fin.castAdd (zmodBitWidth k)) +
          decodeZMod k (xy ∘ Fin.natAdd (zmodBitWidth k)))
    have hadd : addZModOp.depth ≤ 6 * zmodBitWidth k + 1 :=
      (depth_truthTableCircuit_le (zmodBitWidth k + zmodBitWidth k) (zmodBitWidth k) _).trans_eq
        (by omega)
    have hclog := clog_le_six_log (k := k) (m := m) (X := detBoundB k m) (by omega)
    unfold sumTreeCircuit
    refine (Circuit.depth_balanced_le addZModOp _ (D := 4)
      (fun C hC ↦ by
        obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hC
        exact (depth_comp_le_of_le _ _ (depth_truthTableCircuit_le 1 (zmodBitWidth k) _)
          (Circuit.depth_wiring _).le).trans (by omega))
      (fun _ ↦ Circuit.depth_pi_le (D := 4) _ fun _ ↦ by simp)).trans ?_
    rw [List.length_ofFn]
    exact Nat.add_le_add le_rfl (Nat.mul_le_mul hadd hclog)
  have hp : (postArgsCircuit k m).depth ≤
      4 + (6 * zmodBitWidth k + 1) * (6 * (Nat.log 2 (DetZModInstance.encodedLen k m) + 1)) := by
    unfold postArgsCircuit
    refine depth_append_le_of_le _ _ ((Circuit.depth_wiring _).trans_le (Nat.zero_le _)) ?_
    refine depth_append_le_of_le _ _ ((Circuit.depth_wiring _).trans_le (Nat.zero_le _)) ?_
    exact depth_append_le_of_le _ _ hsum ((Circuit.depth_wiring _).trans_le (Nat.zero_le _))
  have hf : (truthTableCircuit1 (1 + (1 + (zmodBitWidth k + zmodBitWidth k)))
      (finalVerdictFn k)).depth ≤ 6 * zmodBitWidth k + 7 :=
    (depth_truthTableCircuit1_le (1 + (1 + (zmodBitWidth k + zmodBitWidth k)))
      (finalVerdictFn k)).trans_eq (by omega)
  unfold detZModPostLayerDM
  exact (depth_comp_le_of_le _ _ hf hp).trans (by omega)

private theorem depth_detZModFull_arith (w l : ℕ) (hw : 0 < w) :
    ((6 * w + 11) + (6 * w + 1) * (6 * (l + 1))) + ((3 * w + 4) + 12 * (l + 1)) ≤
      (48 * w + 30) * (l + 1) := by
  nlinarith

private theorem depth_detZModFullCircuit_le {k : ℕ} (hk : 2 ≤ k) (m : ℕ) :
    (detZModFullCircuit k hk m).depthWith nc1OracleDepthWeight ≤
      (48 * zmodBitWidth k + 30) * (Nat.log 2 (DetZModInstance.encodedLen k m) + 1) := by
  unfold detZModFullCircuit
  refine (Circuit.depthWith_comp_le (σ := oracleSignature) nc1OracleDepthWeight
    ((detZModPostLayerDM k m).mapOp toOracle) (detZModMidLayer k hk m)).trans ?_
  rw [depthWith_mapOp_toOracle_eq]
  exact (Nat.add_le_add (depth_detZModPostLayerDM_le hk m)
    (depthWith_detZModMidLayer_le hk m)).trans
    (depth_detZModFull_arith (zmodBitWidth k) (Nat.log 2 (DetZModInstance.encodedLen k m))
      (zmodBitWidth_pos hk))

private theorem eval_headerChecksCircuit (k m : ℕ)
    (x : Fin (DetZModInstance.encodedLen k m) → Bool) (i : Fin (m + 1)) :
    (headerChecksCircuit k m).eval interpretation x i =
      decide (x (headerWire k m i) = decide (i.val < m)) := by
  unfold headerChecksCircuit
  rw [Circuit.eval_pi]
  dsimp only []
  by_cases him : i.val < m
  · rw [ite_eq_left him, Circuit.eval_wiring]
    simp [him]
  · rw [ite_eq_right him, Circuit.eval_comp, Circuit.eval_oneGate, Circuit.eval_wiring]
    simp [interpretation, him]

private theorem eval_allValidCircuit (k m : ℕ)
    (x : Fin (DetZModInstance.encodedLen k m) → Bool) :
    (allValidCircuit k m).eval interpretation x 0 =
      decide ((∀ i : Fin (m + 1),
          x (Fin.castAdd (m * m * zmodBitWidth k) (Fin.castAdd (zmodBitWidth k) i)) =
            decide (i.val < m)) ∧
        decodeBits (x ∘ targetSlice k m) < k ∧
        ∀ p : Fin (m * m), decodeBits (x ∘ entrySlice k m p) < k) := by
  set w := zmodBitWidth k
  unfold allValidCircuit
  simp only [Circuit.eval_comp, eval_andTree]
  rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
  constructor
  · intro hall
    refine ⟨fun i ↦ ?_, ?_, fun p ↦ ?_⟩
    · have hi := hall (Fin.castAdd (m * m) (Fin.castAdd 1 i))
      rw [Circuit.eval_append, Fin.append_left, Circuit.eval_append, Fin.append_left,
        eval_headerChecksCircuit, decide_eq_true_eq] at hi
      exact hi
    · have ht := hall (Fin.castAdd (m * m) (Fin.natAdd (m + 1) 0))
      simpa only [Circuit.eval_append, Fin.append_left, Fin.append_right, Circuit.eval_comp,
        eval_truthTableCircuit1, Circuit.eval_wiring, decide_eq_true_eq] using ht
    · have hp := hall (Fin.natAdd ((m + 1) + 1) p)
      simpa only [Circuit.eval_append, Fin.append_right, Circuit.eval_pi, Circuit.eval_comp,
        eval_truthTableCircuit1, Circuit.eval_wiring, decide_eq_true_eq] using hp
  · rintro ⟨hhead, htgt, hent⟩ idx
    refine Fin.addCases ?_ ?_ idx
    · intro i
      refine Fin.addCases ?_ ?_ i
      · intro i₀
        rw [Circuit.eval_append, Fin.append_left, Circuit.eval_append, Fin.append_left,
          eval_headerChecksCircuit, decide_eq_true_eq]
        exact hhead i₀
      · intro j₀
        obtain rfl : j₀ = 0 := Subsingleton.elim j₀ 0
        simpa only [Circuit.eval_append, Fin.append_left, Fin.append_right, Circuit.eval_comp,
          eval_truthTableCircuit1, Circuit.eval_wiring, decide_eq_true_eq] using htgt
    · intro p
      simpa only [Circuit.eval_append, Fin.append_right, Circuit.eval_pi, Circuit.eval_comp,
        eval_truthTableCircuit1, Circuit.eval_wiring, decide_eq_true_eq] using hent p

private theorem computes_detZModFullCircuit {k : ℕ} (hk : 2 ≤ k) (m : ℕ) :
    (detZModFullCircuit k hk m).Computes (oracleInterpretation detIntLanguage)
      (single ((detZModLanguage k).slice (DetZModInstance.encodedLen k m))) := by
  have hk_ne : NeZero k := ⟨by omega⟩
  set w := zmodBitWidth k
  set Q := DetZModInstance.encodedLen k m
  set B := detBoundB k m
  have hw_pos : 0 < w := zmodBitWidth_pos hk
  intro x
  funext j
  obtain rfl : j = 0 := Subsingleton.elim j 0
  dsimp only [single]
  let clampedNat (p : Fin (m * m)) : ℕ :=
    if decodeBits (x ∘ entrySlice k m p) < k then decodeBits (x ∘ entrySlice k m p) else 0
  let M_int : Matrix (Fin m) (Fin m) ℤ :=
    fun i j ↦ (clampedNat (finProdFinEquiv (i, j)) : ℤ)
  have hM_int_lt (i j : Fin m) : (M_int i j).natAbs < 2 ^ w := by
    have hk_lt : k < 2 ^ w := Nat.lt_size_self k
    dsimp only [M_int, clampedNat]
    rw [Int.natAbs_natCast]
    split_ifs with hlt
    · exact hlt.trans hk_lt
    · exact Nat.pos_of_ne_zero (by positivity)
  let preL := (constBank (1 + w + m * m * w)).comp ((preLayerDM k hk m).mapOp toOracle)
  have hpre_src (s : Source (1 + w + m * m * w)) :
      (preL.eval (oracleInterpretation detIntLanguage) x) (sourceWire s) =
        s.elim ((preLayerDM k hk m).eval interpretation x) id := by
    simp only [preL, Circuit.eval_comp, eval_constBank_sourceWire,
      Circuit.eval_mapOp (I := interpretation)]
  have hintQuery_word (idx : Fin (B + 1)) :
      List.ofFn (fun a ↦ (preL.eval (oracleInterpretation detIntLanguage) x)
        (sourceWire (intQuerySrc k m idx a))) =
      (⟨m, w, idx.val, M_int, hM_int_lt⟩ : DetIntInstance).encode := by
    let evalSrc (s : Source (1 + w + m * m * w)) : Bool :=
      (preL.eval (oracleInterpretation detIntLanguage) x) (sourceWire s)
    change List.ofFn (fun a : Fin ((m + 1) + (w + 1) + (idx.val + 1) + m * m * (w + 1)) ↦
      evalSrc (intQuerySrc k m idx a)) = _
    have hcomp :
        (fun a : Fin ((m + 1) + (w + 1) + (idx.val + 1) + m * m * (w + 1)) ↦
          evalSrc (intQuerySrc k m idx a)) =
        Fin.addCases
          (Fin.addCases
            (Fin.addCases
              (fun i : Fin (m + 1) ↦ decide (i.val < m))
              (fun i : Fin (w + 1) ↦ decide (i.val < w)))
            (fun i : Fin (idx.val + 1) ↦ decide (i.val < idx.val)))
          (fun p : Fin (m * m * (w + 1)) ↦
            let blk : Fin (m * m) :=
              ⟨p.val / (w + 1), Nat.div_lt_of_lt_mul (by have hp := p.isLt; nlinarith)⟩
            let s : Fin (w + 1) := ⟨p.val % (w + 1), Nat.mod_lt _ (Nat.succ_pos w)⟩
            let e : ℤ := M_int (finProdFinEquiv.symm blk).1 (finProdFinEquiv.symm blk).2
            Fin.cons (α := fun _ ↦ Bool) (decide (e < 0)) (encodeBits w e.natAbs) s) := by
      funext a
      refine Fin.addCases ?_ ?_ a
      · intro i
        refine Fin.addCases ?_ ?_ i
        · intro i₁
          refine Fin.addCases ?_ ?_ i₁
          · intro a₀
            change evalSrc (intQuerySrc k m idx
              (Fin.castAdd (m * m * (w + 1))
                (Fin.castAdd (idx.val + 1) (Fin.castAdd (w + 1) a₀)))) = _
            unfold intQuerySrc
            rw [Fin.addCases_left, Fin.addCases_left, Fin.addCases_left,
              Fin.addCases_left, Fin.addCases_left, Fin.addCases_left]
            exact hpre_src (.inr (decide (a₀.val < m)))
          · intro b₀
            change evalSrc (intQuerySrc k m idx
              (Fin.castAdd (m * m * (w + 1))
                (Fin.castAdd (idx.val + 1) (Fin.natAdd (m + 1) b₀)))) = _
            unfold intQuerySrc
            rw [Fin.addCases_left, Fin.addCases_left, Fin.addCases_right,
              Fin.addCases_left, Fin.addCases_left, Fin.addCases_right]
            exact hpre_src (.inr (decide (b₀.val < w)))
        · intro c₀
          change evalSrc (intQuerySrc k m idx
            (Fin.castAdd (m * m * (w + 1))
              (Fin.natAdd ((m + 1) + (w + 1)) c₀))) = _
          unfold intQuerySrc
          rw [Fin.addCases_left, Fin.addCases_right, Fin.addCases_left, Fin.addCases_right]
          exact hpre_src (.inr (decide (c₀.val < idx.val)))
      · intro p
        change evalSrc (intQuerySrc k m idx
          (Fin.natAdd ((m + 1) + (w + 1) + (idx.val + 1)) p)) = _
        unfold intQuerySrc
        rw [Fin.addCases_right, Fin.addCases_right]
        dsimp only [evalSrc]
        let blk : Fin (m * m) :=
          ⟨p.val / (w + 1), Nat.div_lt_of_lt_mul (by have hp := p.isLt; nlinarith)⟩
        have hentry_eq : M_int (finProdFinEquiv.symm blk).1 (finProdFinEquiv.symm blk).2 =
            (clampedNat blk : ℤ) := by
          dsimp only [M_int]
          rw [Prod.mk.eta, Equiv.apply_symm_apply]
        by_cases hoff : p.val % (w + 1) = 0
        · rw [dite_eq_left hoff, hpre_src]
          dsimp only [Sum.elim_inr, id_eq]
          have h0 : (⟨p.val % (w + 1), Nat.mod_lt _ (Nat.succ_pos w)⟩ : Fin (w + 1)) = 0 := by
            ext; exact hoff
          rw [h0, Fin.cons_zero]
          change false =
            decide (M_int (finProdFinEquiv.symm blk).1 (finProdFinEquiv.symm blk).2 < 0)
          rw [hentry_eq]
          simp
        · rw [dite_eq_right hoff, hpre_src]
          dsimp only [Sum.elim_inl]
          let t : Fin w := ⟨p.val % (w + 1) - 1, by
            have : p.val % (w + 1) < w + 1 := Nat.mod_lt p.val (by omega)
            omega⟩
          have hsucc : (⟨p.val % (w + 1), Nat.mod_lt _ (Nat.succ_pos w)⟩ : Fin (w + 1)) =
              t.succ := by ext; simp [t]; omega
          rw [hsucc, Fin.cons_succ]
          change ((preLayerDM k hk m).eval interpretation x)
            (Fin.natAdd (1 + zmodBitWidth k)
              ⟨blk.val * zmodBitWidth k + t.val, by
                have hb := blk.isLt; have ht := t.isLt; dsimp only [w] at ht; nlinarith⟩) =
            encodeBits w (M_int (finProdFinEquiv.symm blk).1 (finProdFinEquiv.symm blk).2).natAbs t
          rw [hentry_eq, Int.natAbs_natCast]
          unfold preLayerDM clampedFlatCircuit
          rw [Circuit.eval_append, Fin.append_right, Circuit.eval_pi]
          dsimp only []
          have hdiv_idx : (blk.val * zmodBitWidth k + t.val) / zmodBitWidth k = blk.val := by
            rw [Nat.mul_comm, Nat.mul_add_div hw_pos, Nat.div_eq_of_lt t.isLt, add_zero]
          have hmod_idx : (blk.val * zmodBitWidth k + t.val) % zmodBitWidth k = t.val := by
            rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt t.isLt]
          have hblk_eq : (⟨(blk.val * zmodBitWidth k + t.val) / zmodBitWidth k,
              Nat.div_lt_of_lt_mul (by
                have hb := blk.isLt; have ht := t.isLt; dsimp only [w] at ht; nlinarith)⟩ :
              Fin (m * m)) = blk := Fin.ext hdiv_idx
          have ht_eq : (⟨(blk.val * zmodBitWidth k + t.val) % zmodBitWidth k,
              Nat.mod_lt _ hw_pos⟩ : Fin (zmodBitWidth k)) = t := Fin.ext hmod_idx
          rw [Circuit.eval_comp, Circuit.eval_wiring, Function.comp_apply,
            Circuit.eval_comp, eval_truthTableCircuit, Circuit.eval_wiring,
            hblk_eq, ht_eq]
          dsimp only [clampedNat, w]
          split_ifs with hlt
          · rw [encodeBits_decodeBits]
          · rfl
    rw [hcomp, ofFn_addCases, ofFn_addCases, ofFn_addCases,
      ofFn_decide_lt, ofFn_decide_lt, ofFn_decide_lt,
      ofFn_mul_eq_flatten (Nat.succ_pos w) (fun blk s ↦
        let e : ℤ := M_int (finProdFinEquiv.symm blk).1 (finProdFinEquiv.symm blk).2
        Fin.cons (α := fun _ ↦ Bool) (decide (e < 0)) (encodeBits w e.natAbs) s)]
    rw [DetIntInstance.encode_eq]
    simp only [List.append_assoc]
  let yMid := (detZModMidLayer k hk m).eval (oracleInterpretation detIntLanguage) x
  have hyMid_valid : yMid (Fin.castAdd (B + 1) (Fin.castAdd w 0)) =
      (allValidCircuit k m).eval interpretation x 0 := by
    dsimp only [yMid, detZModMidLayer]
    rw [Circuit.eval_comp, Circuit.eval_append, Fin.append_left, Circuit.eval_wiring]
    change preL.eval (oracleInterpretation detIntLanguage) x
      (sourceWire (Sum.inl (Fin.castAdd (m * m * zmodBitWidth k)
        (Fin.castAdd (zmodBitWidth k) 0)))) = _
    rw [hpre_src]
    dsimp only [Sum.elim_inl, preLayerDM]
    rw [Circuit.eval_append, Fin.append_left, Circuit.eval_append, Fin.append_left]
  have hyMid_tgt : (fun t : Fin w ↦ yMid (Fin.castAdd (B + 1) (Fin.natAdd 1 t))) =
      x ∘ targetSlice k m := by
    funext t
    dsimp only [yMid, detZModMidLayer]
    rw [Circuit.eval_comp, Circuit.eval_append, Fin.append_left, Circuit.eval_wiring]
    change preL.eval (oracleInterpretation detIntLanguage) x
      (sourceWire (Sum.inl (Fin.castAdd (m * m * zmodBitWidth k) (Fin.natAdd 1 t)))) = _
    rw [hpre_src]
    dsimp only [Sum.elim_inl, preLayerDM]
    rw [Circuit.eval_append, Fin.append_left, Circuit.eval_append, Fin.append_right,
      Circuit.eval_wiring]
  have hyMid_query (idx : Fin (B + 1)) :
      yMid (Fin.natAdd (1 + w) idx) =
        (⟨m, w, idx.val, M_int, hM_int_lt⟩ : DetIntInstance).verdict := by
    dsimp only [yMid, detZModMidLayer]
    rw [Circuit.eval_comp, Circuit.eval_append, Fin.append_right, Circuit.eval_pi]
    dsimp only []
    rw [Circuit.eval_oneGate, oracleInterpretation_query]
    change detIntLanguage.slice (DetIntInstance.encodedLen m w idx.val)
      (fun a ↦ preL.eval (oracleInterpretation detIntLanguage) x
        (sourceWire (intQuerySrc k m idx a))) = _
    rw [Bool.eq_iff_iff, Language.slice_eq_true_iff, hintQuery_word idx,
      mem_detIntLanguage_encode]
  have hfull :
      (detZModFullCircuit k hk m).eval (oracleInterpretation detIntLanguage) x 0 =
        ((allValidCircuit k m).eval interpretation x 0 &&
          decide ((M_int.det : ZMod k) = decodeZMod k (x ∘ targetSlice k m))) := by
    unfold detZModFullCircuit
    rw [Circuit.eval_comp, Circuit.eval_mapOp (I := interpretation)]
    change (detZModPostLayerDM k m).eval interpretation yMid 0 = _
    unfold detZModPostLayerDM
    rw [Circuit.eval_comp, eval_truthTableCircuit1]
    have balancedFold_sum :
        ∀ l : List (Circuit signature ((1 + w) + (B + 1)) w),
          decodeZMod k ((Circuit.balanced
            (truthTableCircuit (w + w) w fun xy ↦
              encodeZMod k (decodeZMod k (xy ∘ Fin.castAdd w) + decodeZMod k (xy ∘ Fin.natAdd w)))
            (Circuit.pi fun t ↦ Circuit.oneGate (.const (encodeZMod k 0 t)) Fin.elim0) l).eval
            interpretation yMid) =
            (l.map fun C ↦ decodeZMod k (C.eval interpretation yMid)).sum := by
      intro l
      rw [Circuit.eval_balanced]
      refine List.balancedFold_induction
        (p := fun l (res : Fin w → Bool) ↦
          decodeZMod k res = (l.map fun C ↦ decodeZMod k (C.eval interpretation yMid)).sum)
        (?_) (fun _ ↦ ?_) (fun l₁ l₂ r₁ r₂ _ _ ih₁ ih₂ ↦ ?_) l
      · have hz : (Circuit.pi fun t : Fin w ↦
            Circuit.oneGate (σ := signature) (.const (encodeZMod k 0 t)) Fin.elim0).eval
            interpretation yMid = encodeZMod k 0 := funext fun t ↦ by simp [interpretation]
        rw [hz, decode_encodeZMod]; simp
      · simp
      · have hadd : (truthTableCircuit (w + w) w fun xy ↦
            encodeZMod k (decodeZMod k (xy ∘ Fin.castAdd w) +
              decodeZMod k (xy ∘ Fin.natAdd w))).eval interpretation (Fin.append r₁ r₂) =
            encodeZMod k (decodeZMod k r₁ + decodeZMod k r₂) := by
          rw [eval_truthTableCircuit]
          have h1 : Fin.append r₁ r₂ ∘ Fin.castAdd w = r₁ := funext (Fin.append_left r₁ r₂)
          have h2 : Fin.append r₁ r₂ ∘ Fin.natAdd w = r₂ := funext (Fin.append_right r₁ r₂)
          rw [h1, h2]
        rw [hadd, decode_encodeZMod, ih₁, ih₂, List.map_append, List.sum_append]
    have hsum_val :
        decodeZMod k ((sumTreeCircuit k m).eval interpretation yMid) =
          (M_int.det.natAbs : ZMod k) := by
      unfold sumTreeCircuit
      dsimp only []
      rw [balancedFold_sum, List.map_ofFn, List.sum_ofFn]
      have hbit (r : Fin B) :
          decodeZMod k (((truthTableCircuit 1 w fun b ↦
            if b 0 then encodeZMod k ((2 : ZMod k) ^ r.val) else encodeZMod k 0).comp
            (Circuit.wiring signature fun _ : Fin 1 ↦ Fin.natAdd (1 + w) r.succ)).eval
            interpretation yMid) =
          if (M_int.det.natAbs / 2 ^ r.val) % 2 = 1 then (2 : ZMod k) ^ r.val else 0 := by
        have hq_r := hyMid_query r.succ
        simp only [Fin.val_succ, DetIntInstance.verdict_mk_succ] at hq_r
        rw [Circuit.eval_comp, eval_truthTableCircuit, Circuit.eval_wiring]
        dsimp only [Function.comp_apply]
        simp only [hq_r]
        by_cases hodd : (M_int.det.natAbs / 2 ^ r.val) % 2 = 1 <;>
          simp [hodd, decode_encodeZMod]
      have hdet_lt : M_int.det.natAbs < 2 ^ B := det_int_natAbs_lt M_int hM_int_lt
      rw [← sum_two_pow_encodeBits hdet_lt, Nat.cast_sum]
      refine Finset.sum_congr rfl fun r _ ↦ ?_
      dsimp only [Function.comp_apply]
      rw [hbit r]
      by_cases hodd : (M_int.det.natAbs / 2 ^ r.val) % 2 = 1 <;> simp [hodd]
    dsimp only [finalVerdictFn]
    have hv : ((postArgsCircuit k m).eval interpretation yMid) (Fin.castAdd (1 + (w + w)) 0) =
        (allValidCircuit k m).eval interpretation x 0 := by
      unfold postArgsCircuit
      rw [Circuit.eval_append, Fin.append_left, Circuit.eval_wiring]; exact hyMid_valid
    have hn : (((postArgsCircuit k m).eval interpretation yMid) ∘ Fin.natAdd 1)
        (Fin.castAdd (w + w) 0) = decide (M_int.det < 0) := by
      unfold postArgsCircuit; dsimp only [Function.comp_apply]
      rw [Circuit.eval_append, Fin.append_right, Circuit.eval_append, Fin.append_left,
        Circuit.eval_wiring]
      simpa only [Function.comp_apply, Fin.val_zero,
        DetIntInstance.verdict_mk_zero] using hyMid_query 0
    have hs : decodeZMod k (((((postArgsCircuit k m).eval interpretation yMid) ∘ Fin.natAdd 1) ∘
        Fin.natAdd 1) ∘ Fin.castAdd w) = (M_int.det.natAbs : ZMod k) := by
      have h1 : ((((postArgsCircuit k m).eval interpretation yMid) ∘ Fin.natAdd 1) ∘
          Fin.natAdd 1) ∘ Fin.castAdd w = (sumTreeCircuit k m).eval interpretation yMid := by
        unfold postArgsCircuit; funext t; dsimp only [Function.comp_apply]
        rw [Circuit.eval_append, Fin.append_right, Circuit.eval_append, Fin.append_right,
          Circuit.eval_append, Fin.append_left]
      rw [h1, hsum_val]
    have ht : decodeZMod k (((((postArgsCircuit k m).eval interpretation yMid) ∘ Fin.natAdd 1) ∘
        Fin.natAdd 1) ∘ Fin.natAdd w) = decodeZMod k (x ∘ targetSlice k m) := by
      have h1 : ((((postArgsCircuit k m).eval interpretation yMid) ∘ Fin.natAdd 1) ∘
          Fin.natAdd 1) ∘ Fin.natAdd w = x ∘ targetSlice k m := by
        rw [← hyMid_tgt]; unfold postArgsCircuit; funext t; dsimp only [Function.comp_apply]
        rw [Circuit.eval_append, Fin.append_right, Circuit.eval_append, Fin.append_right,
          Circuit.eval_append, Fin.append_right, Circuit.eval_wiring]; rfl
      rw [h1]
    rw [hv, hn, hs, ht]; congr 2
    by_cases hneg : M_int.det < 0
    · have hdet_eq : M_int.det = -(M_int.det.natAbs : ℤ) := Int.eq_neg_natAbs_of_nonpos hneg.le
      rw [decide_eq_true hneg]; simp only [↓reduceIte]
      have hcast : (-(M_int.det.natAbs : ZMod k)) = (M_int.det : ZMod k) := by
        conv_rhs => rw [hdet_eq]
        rw [Int.cast_neg, Int.cast_natCast]
      rw [hcast]
    · have hdet_eq : M_int.det = (M_int.det.natAbs : ℤ) :=
        (Int.natAbs_of_nonneg (not_lt.mp hneg)).symm
      rw [decide_eq_false hneg]; simp only [Bool.false_eq_true, ↓reduceIte]
      have hcast : (M_int.det.natAbs : ZMod k) = (M_int.det : ZMod k) := by
        conv_rhs => rw [hdet_eq]
        rw [Int.cast_natCast]
      rw [hcast]
  rw [hfull, Bool.eq_iff_iff, Bool.and_eq_true, Language.slice_eq_true_iff, eval_allValidCircuit,
    decide_eq_true_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hhead, htgt, hent⟩, hdet_eq⟩
    let target : ZMod k := (decodeBits (x ∘ targetSlice k m) : ZMod k)
    let M_zmod : Matrix (Fin m) (Fin m) (ZMod k) :=
      fun i j ↦ (decodeBits (x ∘ entrySlice k m (finProdFinEquiv (i, j))) : ZMod k)
    have hM_cast : M_int.map (Int.castRingHom (ZMod k)) = M_zmod := by
      ext i j; rw [Matrix.map_apply]; dsimp only [M_int, M_zmod, clampedNat]
      rw [ite_eq_left (hent (finProdFinEquiv (i, j)))]; simp
    have hM_det : M_zmod.det = target := by
      have h1 := (Int.castRingHom (ZMod k)).map_det M_int
      rw [RingHom.mapMatrix_apply, hM_cast] at h1; rw [← h1]
      simpa [Int.castRingHom, decodeZMod] using hdet_eq
    refine ⟨⟨m, target, M_zmod⟩, ?_, hM_det⟩
    let x' : Fin ((m + 1) + w + m * m * w) → Bool := x
    let entryBitFn (q : Fin (m * m)) (t : Fin w) : Bool :=
      encodeBits w (M_zmod (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2).val t
    have hx_decomp :
        x' =
        Fin.addCases
          (Fin.addCases
            (fun i : Fin (m + 1) ↦ decide (i.val < m))
            (encodeBits w target.val))
          (fun p : Fin (m * m * w) ↦
            entryBitFn ⟨p.val / w, Nat.div_lt_of_lt_mul (by have hp := p.isLt; nlinarith)⟩
              ⟨p.val % w, Nat.mod_lt _ hw_pos⟩) := by
      funext a; refine Fin.addCases ?_ ?_ a
      · intro i; refine Fin.addCases ?_ ?_ i
        · intro i₀; rw [Fin.addCases_left, Fin.addCases_left]; exact hhead i₀
        · intro t₀; rw [Fin.addCases_left, Fin.addCases_right]
          have hval : target.val = decodeBits (x ∘ targetSlice k m) := ZMod.val_natCast_of_lt htgt
          rw [hval, encodeBits_decodeBits]; rfl
      · intro p; rw [Fin.addCases_right]
        let q : Fin (m * m) :=
          ⟨p.val / w, Nat.div_lt_of_lt_mul (by have hp := p.isLt; nlinarith)⟩
        let t : Fin w := ⟨p.val % w, Nat.mod_lt _ hw_pos⟩
        change x' (Fin.natAdd ((m + 1) + w) p) = entryBitFn q t; dsimp only [entryBitFn]
        have hm_val : (M_zmod (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2).val =
            decodeBits (x ∘ entrySlice k m q) := by
          simp only [M_zmod, Prod.mk.eta, Equiv.apply_symm_apply]
          exact ZMod.val_natCast_of_lt (hent q)
        rw [hm_val, encodeBits_decodeBits]; dsimp only [Function.comp_apply, entrySlice, x']
        congr 1; ext; simp only [Fin.val_natAdd]
        have hdm := Nat.div_add_mod p.val w; dsimp only [q, t] at hdm ⊢; nlinarith
    symm; change List.ofFn x' = _
    rw [hx_decomp, ofFn_addCases, ofFn_addCases, ofFn_decide_lt,
      ofFn_mul_eq_flatten hw_pos entryBitFn]; rfl
  · rintro ⟨I, hI_enc, hI_det⟩
    have hlen_eq : DetZModInstance.encodedLen k I.m = Q := by
      simpa [DetZModInstance.length_encode] using congrArg List.length hI_enc
    have hIm : I.m = m := by
      have hQ_def : Q = (m + 1) + w + m * m * w := DetZModInstance.encodedLen_eq k m
      rw [DetZModInstance.encodedLen_eq] at hlen_eq
      change (I.m + 1) + w + I.m * I.m * w = Q at hlen_eq
      by_contra hne; rcases lt_or_gt_of_ne hne with hlt | hgt
      · have : I.m * I.m * w < m * m * w := Nat.mul_lt_mul_of_pos_right (by nlinarith) hw_pos; omega
      · have : m * m * w < I.m * I.m * w := Nat.mul_lt_mul_of_pos_right (by nlinarith) hw_pos; omega
    rcases I with ⟨Im, Itgt, Imat⟩; dsimp only at hIm hI_enc hI_det; subst Im
    have hget (pos : Fin Q) : (⟨m, Itgt, Imat⟩ : DetZModInstance k).encode[pos.val]'(by
        rw [DetZModInstance.length_encode]; exact pos.isLt) = x pos := by
      have h1 := congrArg (fun l : List Bool ↦ l[pos.val]?) hI_enc
      rw [List.getElem?_eq_getElem (by rw [DetZModInstance.length_encode]; exact pos.isLt),
        List.getElem?_eq_getElem (by simp only [List.length_ofFn]; exact pos.isLt),
        List.getElem_ofFn] at h1
      exact Option.some.inj h1
    have hhead (i : Fin (m + 1)) :
        x (Fin.castAdd (m * m * w) (Fin.castAdd w i)) = decide (i.val < m) := by
      rw [← hget (Fin.castAdd (m * m * w) (Fin.castAdd w i))]
      simp only [DetZModInstance.encode_eq, Fin.val_castAdd]
      rw [List.getElem_append_left (by
          simp only [List.length_append, List.length_replicate, List.length_singleton,
            List.length_ofFn]; omega),
        List.getElem_append_left (by
          simp only [List.length_append, List.length_replicate, List.length_singleton]; omega)]
      by_cases hm' : i.val < m
      · rw [List.getElem_append_left (by simp only [List.length_replicate]; exact hm'),
          List.getElem_replicate]
        simp [hm']
      · have heq : i.val = m := by omega
        simp [heq]
    have htgt_bits : x ∘ targetSlice k m = encodeBits w Itgt.val := by
      funext t; rw [Function.comp_apply, ← hget (targetSlice k m t)]
      unfold targetSlice
      simp only [DetZModInstance.encode_eq, Fin.val_castAdd, Fin.val_natAdd]
      rw [List.getElem_append_left (by
          simp only [List.length_append, List.length_replicate, List.length_singleton,
            List.length_ofFn]; omega),
        List.getElem_append_right (by simp)]
      simp only [List.length_append, List.length_replicate, List.length_singleton,
        Nat.add_sub_cancel_left, List.getElem_ofFn, Fin.eta]; rfl
    have htgt_val : decodeBits (x ∘ targetSlice k m) = Itgt.val := by
      have hlt : Itgt.val < 2 ^ w := (ZMod.val_lt Itgt).trans (Nat.lt_size_self k)
      rw [htgt_bits, decodeBits_encodeBits hlt]
    have hent_bits (p : Fin (m * m)) :
        x ∘ entrySlice k m p =
          encodeBits w (Imat (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2).val := by
      funext t; rw [Function.comp_apply, ← hget (entrySlice k m p t)]
      unfold entrySlice
      simp only [DetZModInstance.encode_eq, Fin.val_natAdd]
      rw [List.getElem_append_right (by
        simp only [List.length_append, List.length_replicate, List.length_singleton,
          List.length_ofFn]; omega)]
      simp only [List.length_append, List.length_replicate, List.length_singleton,
        List.length_ofFn, Nat.add_sub_cancel_left]
      have hflat_p :
          ∀ {K : ℕ} (F : Fin K → Fin w → Bool) (q : Fin K) (s : Fin w),
            ((List.ofFn fun i : Fin K ↦ List.ofFn (F i)).flatten)[q.val * w + s.val]'(by
              rw [List.length_flatten, List.map_ofFn]
              simp only [Function.comp_def, List.length_ofFn]
              rw [List.ofFn_const, List.sum_replicate, smul_eq_mul]
              have hq := q.isLt; have hs := s.isLt; nlinarith) = F q s := by
        intro K; induction K with
        | zero => intro _ q; exact Fin.elim0 q
        | succ K ih =>
          intro F q s; refine Fin.cases ?_ (fun q' ↦ ?_) q
          · simp only [List.ofFn_succ, List.flatten_cons, Fin.val_zero, zero_mul, zero_add]
            rw [List.getElem_append_left (by simp), List.getElem_ofFn]
          · simp only [List.ofFn_succ, List.flatten_cons, Fin.val_succ, add_mul, one_mul]
            rw [List.getElem_append_right (by simp only [List.length_ofFn]; omega)]
            have heq_idx : q'.val * w + w + s.val - w = q'.val * w + s.val := by omega
            simp only [List.length_ofFn, heq_idx]; exact ih (F ∘ Fin.succ) q' s
      exact hflat_p _ p t
    have hent_val (p : Fin (m * m)) :
        decodeBits (x ∘ entrySlice k m p) =
          (Imat (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2).val := by
      have hlt : (Imat (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2).val < 2 ^ w :=
        (ZMod.val_lt _).trans (Nat.lt_size_self k)
      rw [hent_bits p, decodeBits_encodeBits hlt]
    refine ⟨⟨hhead, htgt_val ▸ ZMod.val_lt Itgt, fun p ↦ hent_val p ▸ ZMod.val_lt _⟩, ?_⟩
    have hM_cast : M_int.map (Int.castRingHom (ZMod k)) = Imat := by
      ext i j; have hv := hent_val (finProdFinEquiv (i, j))
      simp only [Equiv.symm_apply_apply] at hv
      have hlt : decodeBits (x ∘ entrySlice k m (finProdFinEquiv (i, j))) < k :=
        hv ▸ ZMod.val_lt (Imat i j)
      rw [Matrix.map_apply]; dsimp only [M_int, clampedNat]; rw [ite_eq_left hlt]; simp [hv]
    have hdet_cast : (M_int.det : ZMod k) = Imat.det := by
      have h1 := (Int.castRingHom (ZMod k)).map_det M_int
      rw [RingHom.mapMatrix_apply, hM_cast] at h1; simpa [Int.castRingHom] using h1
    rw [hdet_cast, hI_det]; unfold decodeZMod
    change _ = (decodeBits (x ∘ targetSlice k m) : ZMod k); rw [htgt_val, ZMod.natCast_zmod_val]

/-- **The modular determinant language belongs to $\mathrm{DET}$**: for `k ≥ 2`, computing
$\det_{\mathbb{Z}_k}(M) = r$ reduces in $\mathrm{NC}^1$ to querying the `O(m^2 + m log k)` bits
of the integer determinant $\det_{\mathbb{Z}}(\tilde{M})$ of the `[0, k)`-lifted matrix
$\tilde{M}$ and summing `± ∑ b_i 2^i mod k` along a balanced binary tree in `ZMod k`. -/
theorem detZModLanguage_mem_DET {k : ℕ} (hk : 2 ≤ k) : detZModLanguage k ∈ DET := by
  let w := zmodBitWidth k
  have hcircuit (q : ℕ) :
      ∃ C : Circuit oracleSignature q 1,
        C.size ≤ (20 * 2 ^ (2 * w + 2) + 20) * (q + 2) ^ 3 ∧
        C.FanInAtMost ((20 * 2 ^ (2 * w + 2) + 20) * (q + 2) ^ 3) ∧
        C.depthWith nc1OracleDepthWeight ≤ (48 * w + 30) * (Nat.log 2 q + 1) ∧
        C.Computes (oracleInterpretation detIntLanguage)
          (single ((detZModLanguage k).slice q)) := by
    classical
    by_cases hq_match : ∃ m ≤ q, DetZModInstance.encodedLen k m = q
    · obtain ⟨m, _, rfl⟩ := hq_match
      exact ⟨detZModFullCircuit k hk m, size_detZModFullCircuit_le hk m,
        fanIn_detZModFullCircuit hk m, depth_detZModFullCircuit_le hk m,
        computes_detZModFullCircuit hk m⟩
    · refine ⟨Circuit.oneGate (σ := oracleSignature) (OracleOp.base (.const false)) Fin.elim0,
        ?_, (Circuit.fanInAtMost_oneGate _ _ _).2 (Nat.zero_le _), ?_, fun x ↦ funext fun i ↦ ?_⟩
      · have hq3 : 1 ≤ (q + 2) ^ 3 := Nat.one_le_pow 3 (q + 2) (by omega)
        have hcoef : 1 ≤ 20 * 2 ^ (2 * w + 2) + 20 := by omega
        simp only [Circuit.size_oneGate]
        exact (Nat.mul_one 1).symm.trans_le (Nat.mul_le_mul hcoef hq3)
      · simp only [Circuit.depthWith_oneGate, nc1OracleDepthWeight_base]
        have : 1 ≤ Nat.log 2 q + 1 := Nat.le_add_left 1 _; nlinarith
      · obtain rfl : i = 0 := Subsingleton.elim i 0; dsimp only [single]
        simp only [Circuit.eval_oneGate, oracleInterpretation_base, interpretation]
        symm; rw [Bool.eq_false_iff, ne_eq, Language.slice_eq_true_iff]
        rintro ⟨I, hI, -⟩; apply hq_match
        have hlen : DetZModInstance.encodedLen k I.m = q := by
          simpa [DetZModInstance.length_encode] using congrArg List.length hI
        refine ⟨I.m, ?_, hlen⟩; rw [DetZModInstance.encodedLen_eq] at hlen; omega
  choose C hsize hfan hdepth hcomp using hcircuit
  exact ⟨C, 48 * w + 30, fun q ↦ (20 * 2 ^ (2 * w + 2) + 20) * (q + 2) ^ 3, by fun_prop,
    fun q ↦ ⟨hsize q, hfan q, hdepth q, hcomp q⟩⟩

/-- **$\mathrm{DET}_k \subseteq \mathrm{DET}$** for every modulus `k ≥ 2`. -/
theorem DETk_subset_DET {k : ℕ} (hk : 2 ≤ k) : DETk k ⊆ DET :=
  fun _ hL ↦ NC1Oracle.trans hL (detZModLanguage_mem_DET hk)

/-- Encoded-problem form of $\mathrm{DET}_k \subseteq \mathrm{DET}$ for every `k ≥ 2`. -/
theorem DETkOn_subset_DETOn {k : ℕ} (hk : 2 ≤ k) {α : Type*} (enc : α ↪ List Bool) :
    DETkOn k enc ⊆ DETOn enc := by
  rintro A ⟨L, hL, hA⟩
  exact ⟨L, DETk_subset_DET hk hL, hA⟩

end DetZModInDET

/-! ### Private sanity check -/

section Sanity

private example : detZModLanguage 2 ∈ DET ∧ detZModLanguage 6 ∈ DET :=
  ⟨detZModLanguage_mem_DET (by decide), detZModLanguage_mem_DET (by decide)⟩

end Sanity

end Cslib.Complexity
