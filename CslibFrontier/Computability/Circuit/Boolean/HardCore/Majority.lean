module

public import CslibFrontier.Computability.Circuit.Boolean.HardCore.Set
public import CslibFrontier.Computability.Circuit.Boolean.Unbounded
public import CslibFrontier.Foundations.Data.BitString.Threshold
import Cslib.Computability.Circuit.Depth
import CslibFrontier.Computability.Circuit.Complexity
import CslibFrontier.Computability.Circuit.CompositionDepth
import CslibFrontier.Computability.Circuit.MapOp
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


/-!
# Non-Existence of Hard-Core Sets for the Majority Function

This module proves that the `n`-bit Boolean majority function (`Cslib.majority n`) admits no
`ε`-hardcore set against constant-depth, constant-size Boolean circuits whenever `ε < 1 / n`
(`n ≥ 2`).

For odd `n`, a uniformly random coordinate projection agrees with majority on at least a
`1 / 2 + 1 / (2n)` fraction of every input; composing three levels of `3`-bit majority (`maj3Iter3`,
realized by a depth-`6`, size-`52` unbounded-fan-in circuit and a size-`52` De Morgan circuit)
amplifies this agreement above `1 / 2 + 1 / n` for all `n ≥ 7`, while `2 ≤ n ≤ 6` are handled by
explicit small circuits. Averaging over coordinate tuples yields a fixed deterministic circuit on
any nonempty subset `S ⊆ {0, 1}^n`.

## Main definitions

* `maj3`: `3`-bit Boolean majority `(a && b) || ((a || b) && c)`.
* `maj3Iter3`: `3`-level iterated `3`-bit majority on `27` inputs.
* `maj3Prob`: real polynomial `3 p ^ 2 - 2 p ^ 3` tracking acceptance probability under `maj3`.
* `maj3Iter3DeMorgan`, `maj3Iter3Unbounded`: explicit constant-size (`52`), constant-depth (`≤ 6`)
  circuits computing `maj3Iter3`.

## Main results

* `single_coord_projection_agree_odd`: a random single-coordinate projection agrees with
  `Cslib.majority n` with probability at least `1 / 2 + 1 / (2n)` for odd `n ≥ 1`.
* `exists_small_AC0_agree_majority`: for every `n ≥ 2` and nonempty `S ⊆ {0, 1}^n`, there exist
  equivalent unbounded-fan-in (depth `≤ 6`, size `≤ 52`) and De Morgan (size `≤ 52`) circuits
  agreeing with `Cslib.majority n` on at least `(1 / 2 + 1 / n) * #S` inputs in `S`.
* `majority_no_hardcore_AC0`: non-existence of `ε`-hardcore sets for `Cslib.majority n` against
  depth-`6`, size-`52` unbounded-fan-in circuits for any `ε < 1 / n`.
* `majority_not_isHardCoreSet`: `¬ Cslib.Circuits.Boolean.IsHardCoreSet (Cslib.majority n) 52 δ ε H`
  for all `n ≥ 2`, `0 < δ`, `ε < 1 / n`, and `H : Finset (BitString n)`.
-/

public section

namespace CslibFrontier.Computability.Circuit.Boolean.HardCore

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Finset
open scoped BigOperators

/-! ### Part 1: Real Polynomial Analysis of `MAJ₃` and 3-Level Iterated `MAJ₃` -/

/-- 3-bit majority function `(a ∧ b) ∨ ((a ∨ b) ∧ c)`. -/
@[expose] def maj3 (a b c : Bool) : Bool :=
  (a && b) || ((a || b) && c)

/-- 3-level iterated 3-bit majority on `Fin 3 → Fin 3 → Fin 3 → Bool` (`27` inputs). -/
@[expose] def maj3Iter3 (v : Fin 3 → Fin 3 → Fin 3 → Bool) : Bool :=
  maj3
    (maj3 (maj3 (v 0 0 0) (v 0 0 1) (v 0 0 2))
          (maj3 (v 0 1 0) (v 0 1 1) (v 0 1 2))
          (maj3 (v 0 2 0) (v 0 2 1) (v 0 2 2)))
    (maj3 (maj3 (v 1 0 0) (v 1 0 1) (v 1 0 2))
          (maj3 (v 1 1 0) (v 1 1 1) (v 1 1 2))
          (maj3 (v 1 2 0) (v 1 2 1) (v 1 2 2)))
    (maj3 (maj3 (v 2 0 0) (v 2 0 1) (v 2 0 2))
          (maj3 (v 2 1 0) (v 2 1 1) (v 2 1 2))
          (maj3 (v 2 2 0) (v 2 2 1) (v 2 2 2)))

/-- Probability that `maj3` of 3 i.i.d. Bernoulli(`p`) bits equals `true`: `3 p² - 2 p³`. -/
@[expose] def maj3Prob (p : ℝ) : ℝ :=
  3 * p ^ 2 - 2 * p ^ 3

theorem maj3Prob_one_sub (p : ℝ) : maj3Prob (1 - p) = 1 - maj3Prob p := by
  unfold maj3Prob; ring

theorem maj3Prob_half : maj3Prob (1 / 2) = 1 / 2 := by
  unfold maj3Prob; norm_num

theorem maj3Prob_half_add (d : ℝ) :
    maj3Prob (1 / 2 + d) = 1 / 2 + d * (3 / 2 - 2 * d ^ 2) := by
  unfold maj3Prob; ring

theorem maj3Prob_mono {p q : ℝ} (hp : 0 ≤ p) (hq : q ≤ 1) (hpq : p ≤ q) :
    maj3Prob p ≤ maj3Prob q := by
  unfold maj3Prob
  have hdiff :
      (3 * q ^ 2 - 2 * q ^ 3) - (3 * p ^ 2 - 2 * p ^ 3) =
        (q - p) * (p * (3 - 2 * p - q) + q * (3 - 2 * q - p)) := by ring
  have h1 : 0 ≤ 3 - 2 * p - q := by linarith
  have h2 : 0 ≤ 3 - 2 * q - p := by linarith
  have hq0 : 0 ≤ q := le_trans hp hpq
  have hprod : 0 ≤ (q - p) * (p * (3 - 2 * p - q) + q * (3 - 2 * q - p)) :=
    mul_nonneg (sub_nonneg.mpr hpq) (add_nonneg (mul_nonneg hp h1) (mul_nonneg hq0 h2))
  linarith

theorem maj3Prob_mem_Icc {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ maj3Prob p ∧ maj3Prob p ≤ 1 := by
  constructor
  · have h0 : maj3Prob 0 = 0 := by unfold maj3Prob; norm_num
    rw [← h0]; exact maj3Prob_mono le_rfl hp1 hp0
  · have h1 : maj3Prob 1 = 1 := by unfold maj3Prob; norm_num
    rw [← h1]; exact maj3Prob_mono hp0 le_rfl hp1

/-- Key amplification bound for 3-level iterated `MAJ₃`: for all `0 ≤ d ≤ 1/8`,
`maj3Prob^[3](1/2 + d) ≥ 1/2 + (14/5) * d`. -/
theorem maj3Prob_iter3_ge {d : ℝ} (hd0 : 0 ≤ d) (hd8 : d ≤ 1 / 8) :
    1 / 2 + (14 / 5 : ℝ) * d ≤ maj3Prob (maj3Prob (maj3Prob (1 / 2 + d))) := by
  set d1 : ℝ := d * (3 / 2 - 2 * d ^ 2)
  have h1 : maj3Prob (1 / 2 + d) = 1 / 2 + d1 := maj3Prob_half_add d
  have hd1_lo : (47 / 32 : ℝ) * d ≤ d1 := by
    have hsq : d ^ 2 ≤ (1 / 8 : ℝ) ^ 2 := by nlinarith
    have hcoeff : (47 / 32 : ℝ) ≤ 3 / 2 - 2 * d ^ 2 := by linarith
    calc (47 / 32 : ℝ) * d = d * (47 / 32) := by ring
      _ ≤ d * (3 / 2 - 2 * d ^ 2) := mul_le_mul_of_nonneg_left hcoeff hd0
  have hd1_hi : d1 ≤ 3 / 16 := by
    have hsq : 0 ≤ 2 * d ^ 2 := by positivity
    have hle : d1 ≤ d * (3 / 2) := mul_le_mul_of_nonneg_left (by linarith) hd0
    linarith
  have hd1_nonneg : 0 ≤ d1 := by linarith
  set d2 : ℝ := d1 * (3 / 2 - 2 * d1 ^ 2)
  have h2 : maj3Prob (1 / 2 + d1) = 1 / 2 + d2 := maj3Prob_half_add d1
  have hd2_lo : (183 / 128 : ℝ) * d1 ≤ d2 := by
    have hsq : d1 ^ 2 ≤ (3 / 16 : ℝ) ^ 2 := by nlinarith
    have hcoeff : (183 / 128 : ℝ) ≤ 3 / 2 - 2 * d1 ^ 2 := by linarith
    calc (183 / 128 : ℝ) * d1 = d1 * (183 / 128) := by ring
      _ ≤ d1 * (3 / 2 - 2 * d1 ^ 2) := mul_le_mul_of_nonneg_left hcoeff hd1_nonneg
  have hd2_hi : d2 ≤ 9 / 32 := by
    have hsq : 0 ≤ 2 * d1 ^ 2 := by positivity
    have hle : d2 ≤ d1 * (3 / 2) := mul_le_mul_of_nonneg_left (by linarith) hd1_nonneg
    linarith
  have hd2_nonneg : 0 ≤ d2 := by linarith
  set d3 : ℝ := d2 * (3 / 2 - 2 * d2 ^ 2)
  have h3 : maj3Prob (1 / 2 + d2) = 1 / 2 + d3 := maj3Prob_half_add d2
  have hd3_lo : (687 / 512 : ℝ) * d2 ≤ d3 := by
    have hsq : d2 ^ 2 ≤ (9 / 32 : ℝ) ^ 2 := by nlinarith
    have hcoeff : (687 / 512 : ℝ) ≤ 3 / 2 - 2 * d2 ^ 2 := by linarith
    calc (687 / 512 : ℝ) * d2 = d2 * (687 / 512) := by ring
      _ ≤ d2 * (3 / 2 - 2 * d2 ^ 2) := mul_le_mul_of_nonneg_left hcoeff hd2_nonneg
  rw [h1, h2, h3]
  linarith

/-! ### Part 2: Exact Expectation of `maj3` and `maj3Iter3` Over i.i.d. Coordinate Samples -/

private theorem maj3_indicator (a b c : Bool) :
    (if maj3 a b c = true then (1 : ℝ) else 0) =
      (if a then 1 else 0) * (if b then 1 else 0) +
      (if a then 1 else 0) * (if c then 1 else 0) +
      (if b then 1 else 0) * (if c then 1 else 0) -
      2 * (if a then 1 else 0) * (if b then 1 else 0) * (if c then 1 else 0) := by
  cases a <;> cases b <;> cases c <;> norm_num [maj3]

private theorem maj3_avg_eq {α : Type*} [Fintype α] [Nonempty α] (g : α → Bool) :
    (∑ s : Fin 3 → α, if maj3 (g (s 0)) (g (s 1)) (g (s 2)) = true then (1 : ℝ) else 0) /
        (Fintype.card α : ℝ) ^ 3 =
      maj3Prob ((∑ a : α, if g a = true then (1 : ℝ) else 0) / (Fintype.card α : ℝ)) := by
  let N : ℝ := Fintype.card α
  have hN : N ≠ 0 := Nat.cast_ne_zero.mpr (Fintype.card_pos (α := α)).ne'
  let W : ℝ := ∑ a : α, if g a = true then (1 : ℝ) else 0
  let e3 : (α × α × α) ≃ (Fin 3 → α) :=
    { toFun := fun t => ![t.1, t.2.1, t.2.2]
      invFun := fun s => (s 0, s 1, s 2)
      left_inv := fun ⟨_, _, _⟩ => rfl
      right_inv := fun s => by ext i; fin_cases i <;> rfl }
  have hsum :
      (∑ s : Fin 3 → α, if maj3 (g (s 0)) (g (s 1)) (g (s 2)) = true then (1 : ℝ) else 0) =
        3 * W ^ 2 * N - 2 * W ^ 3 := by
    rw [← e3.sum_comp, Fintype.sum_prod_type]
    have hval : ∀ (a b c : α),
        (if maj3 (g (e3 (a, b, c) 0)) (g (e3 (a, b, c) 1)) (g (e3 (a, b, c) 2)) = true
          then (1 : ℝ) else 0) =
        if maj3 (g a) (g b) (g c) = true then 1 else 0 := fun _ _ _ => rfl
    simp_rw [Fintype.sum_prod_type, hval, maj3_indicator]
    have hconst : (∑ _a : α, (1 : ℝ)) = N := by
      simp [N]
    have h1 :
        (∑ a : α, ∑ b : α, ∑ c : α,
          ((if g a then (1 : ℝ) else 0) * (if g b then 1 else 0) +
           (if g a then 1 else 0) * (if g c then 1 else 0) +
           (if g b then 1 else 0) * (if g c then 1 else 0) -
           2 * (if g a then 1 else 0) * (if g b then 1 else 0) * (if g c then 1 else 0))) =
        (∑ a : α, ∑ b : α, ∑ _c : α, (if g a then (1 : ℝ) else 0) * (if g b then 1 else 0)) +
        (∑ a : α, ∑ _b : α, ∑ c : α, (if g a then (1 : ℝ) else 0) * (if g c then 1 else 0)) +
        (∑ _a : α, ∑ b : α, ∑ c : α, (if g b then (1 : ℝ) else 0) * (if g c then 1 else 0)) -
        2 * (∑ a : α, ∑ b : α, ∑ c : α,
          (if g a then (1 : ℝ) else 0) * (if g b then 1 else 0) * (if g c then 1 else 0)) := by
      simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
    rw [h1]
    have ht1 : (∑ a : α, ∑ b : α, ∑ _c : α,
        (if g a then (1 : ℝ) else 0) * (if g b then 1 else 0)) = W ^ 2 * N := by
      simp_rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
      simp_rw [← Finset.sum_mul]
      change N * (W * W) = W ^ 2 * N
      ring
    have ht2 : (∑ a : α, ∑ _b : α, ∑ c : α,
        (if g a then (1 : ℝ) else 0) * (if g c then 1 else 0)) = W ^ 2 * N := by
      simp_rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      simp_rw [← Finset.sum_mul]
      change W * (N * W) = W ^ 2 * N
      ring
    have ht3 : (∑ _a : α, ∑ b : α, ∑ c : α,
        (if g b then (1 : ℝ) else 0) * (if g c then 1 else 0)) = W ^ 2 * N := by
      simp_rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
      simp_rw [← Finset.sum_mul]
      change N * (W * W) = W ^ 2 * N
      ring
    have ht4 : (∑ a : α, ∑ b : α, ∑ c : α,
        (if g a then (1 : ℝ) else 0) * (if g b then 1 else 0) * (if g c then 1 else 0)) =
        W ^ 3 := by
      simp_rw [mul_assoc, ← Finset.mul_sum]
      simp_rw [← Finset.sum_mul]
      change W * (W * W) = W ^ 3
      ring
    rw [ht1, ht2, ht3, ht4]
    ring
  rw [hsum]
  unfold maj3Prob
  change (3 * W ^ 2 * N - 2 * W ^ 3) / N ^ 3 = 3 * (W / N) ^ 2 - 2 * (W / N) ^ 3
  field_simp [hN]

/-- Exact probability that `maj3Iter3` on 27 i.i.d. uniform coordinates of `x : Fin n → Bool`
outputs `true` equals `maj3Prob^[3] (weight x / n)`. -/
theorem maj3Iter3_avg_eq {n : ℕ} (hn : 0 < n) (x : Fin n → Bool) :
    (∑ t : Fin 3 → Fin 3 → Fin 3 → Fin n,
        if maj3Iter3 (fun a b c => x (t a b c)) = true then (1 : ℝ) else 0) /
        ((n : ℝ) ^ 27) =
      maj3Prob (maj3Prob (maj3Prob ((Cslib.BitString.weight x : ℝ) / (n : ℝ)))) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let g1 : (Fin 3 → Fin n) → Bool := fun s => maj3 (x (s 0)) (x (s 1)) (x (s 2))
  let g2 : (Fin 3 → Fin 3 → Fin n) → Bool := fun s => maj3 (g1 (s 0)) (g1 (s 1)) (g1 (s 2))
  have h1 := maj3_avg_eq x
  have h2 := maj3_avg_eq g1
  have h3 := maj3_avg_eq g2
  have hw : (∑ a : Fin n, if x a = true then (1 : ℝ) else 0) = (Cslib.BitString.weight x : ℝ) := by
    simp [Cslib.BitString.weight, Finset.sum_boole]
  have hc1 : (Fintype.card (Fin n) : ℝ) = (n : ℝ) := by simp
  have hc2 : (Fintype.card (Fin 3 → Fin n) : ℝ) = (n : ℝ) ^ 3 := by simp
  have hc3 : (Fintype.card (Fin 3 → Fin 3 → Fin n) : ℝ) = (n : ℝ) ^ 9 := by
    simp only [Fintype.card_fun, Fintype.card_fin]
    push_cast; ring
  rw [hw, hc1] at h1
  rw [hc2] at h2
  rw [hc3] at h3
  have hpow2 : ((n : ℝ) ^ 3) ^ 3 = (n : ℝ) ^ 9 := by ring
  rw [h1, hpow2] at h2
  rw [h2] at h3
  have hpow : ((n : ℝ) ^ 9) ^ 3 = (n : ℝ) ^ 27 := by ring
  rw [hpow] at h3
  exact h3

/-- Complementary probability that `maj3Iter3` outputs `false` on 27 i.i.d. uniform coordinates. -/
theorem maj3Iter3_avg_false_eq {n : ℕ} (hn : 0 < n) (x : Fin n → Bool) :
    (∑ t : Fin 3 → Fin 3 → Fin 3 → Fin n,
        if maj3Iter3 (fun a b c => x (t a b c)) = false then (1 : ℝ) else 0) /
        ((n : ℝ) ^ 27) =
      maj3Prob (maj3Prob (maj3Prob (1 - (Cslib.BitString.weight x : ℝ) / (n : ℝ)))) := by
  have hcard : (Fintype.card (Fin 3 → Fin 3 → Fin 3 → Fin n) : ℝ) = (n : ℝ) ^ 27 := by
    simp only [Fintype.card_fun, Fintype.card_fin]
    push_cast; ring
  have hpos : (n : ℝ) ^ 27 ≠ 0 := by positivity
  have hcompl :
      (∑ t : Fin 3 → Fin 3 → Fin 3 → Fin n,
          if maj3Iter3 (fun a b c => x (t a b c)) = false then (1 : ℝ) else 0) =
        (n : ℝ) ^ 27 -
          (∑ t : Fin 3 → Fin 3 → Fin 3 → Fin n,
            if maj3Iter3 (fun a b c => x (t a b c)) = true then (1 : ℝ) else 0) := by
    have hadd :
        (∑ t : Fin 3 → Fin 3 → Fin 3 → Fin n,
            if maj3Iter3 (fun a b c => x (t a b c)) = false then (1 : ℝ) else 0) +
          (∑ t : Fin 3 → Fin 3 → Fin 3 → Fin n,
            if maj3Iter3 (fun a b c => x (t a b c)) = true then (1 : ℝ) else 0) =
          (n : ℝ) ^ 27 := by
      rw [← Finset.sum_add_distrib]
      have h1 : ∀ t : Fin 3 → Fin 3 → Fin 3 → Fin n,
          (if maj3Iter3 (fun a b c => x (t a b c)) = false then (1 : ℝ) else 0) +
            (if maj3Iter3 (fun a b c => x (t a b c)) = true then (1 : ℝ) else 0) = 1 := fun t => by
        cases maj3Iter3 (fun a b c => x (t a b c)) <;> simp
      simp_rw [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hcard]
    linarith
  rw [hcompl, sub_div, div_self hpos, maj3Iter3_avg_eq hn x, maj3Prob_one_sub,
    maj3Prob_one_sub, maj3Prob_one_sub]

/-! ### Part 3: Explicit Constant-Size / Constant-Depth Boolean Circuits -/

/-- `1`-gate De Morgan circuit computing constant `true`. -/
def constTrueDeMorgan (n : ℕ) : Circuit Boolean.signature n 1 where
  size := 1
  program := (Program.empty : Program Boolean.signature n 0).gate ⟨Boolean.Op.const true, Fin.elim0⟩
  outputs := fun _ => Wire.gate 0

theorem constTrueDeMorgan_eval (n : ℕ) (x : Fin n → Bool) :
    (constTrueDeMorgan n).eval Boolean.interpretation x 0 = true := by
  unfold constTrueDeMorgan; rfl

theorem constTrueDeMorgan_depth_le (n : ℕ) : (constTrueDeMorgan n).depth ≤ 1 := by
  exact Circuit.depth_le_size _

/-- `4`-gate De Morgan circuit computing `maj3 (x 0) (x 1) (x 2)`. -/
def maj3DeMorgan : Circuit Boolean.signature 3 1 where
  size := 4
  program :=
    ((((Program.empty : Program Boolean.signature 3 0).gate
      ⟨Boolean.Op.and, ![Wire.input 0, Wire.input 1]⟩).gate
      ⟨Boolean.Op.or, ![Wire.input 0, Wire.input 1]⟩).gate
      ⟨Boolean.Op.and, ![Wire.gate 1, Wire.input 2]⟩).gate
      ⟨Boolean.Op.or, ![Wire.gate 0, Wire.gate 2]⟩
  outputs := fun _ => Wire.gate 3

theorem maj3DeMorgan_eval (x : Fin 3 → Bool) :
    maj3DeMorgan.eval Boolean.interpretation x 0 = maj3 (x 0) (x 1) (x 2) := by
  have hall : ∀ a b c : Bool,
      maj3DeMorgan.eval Boolean.interpretation ![a, b, c] 0 = maj3 a b c := by
    unfold maj3DeMorgan; decide
  have hx : x = ![x 0, x 1, x 2] := by ext i; fin_cases i <;> rfl
  rw [hx]; exact hall (x 0) (x 1) (x 2)

/-- `4`-gate, depth-`2` unbounded-fan-in circuit computing `maj3 (x 0) (x 1) (x 2)`. -/
def maj3Unbounded : Circuit Unbounded.signature 3 1 where
  size := 4
  program :=
    ((((Program.empty : Program Unbounded.signature 3 0).gate
      ⟨Unbounded.Op.and 2, ![Wire.input 0, Wire.input 1]⟩).gate
      ⟨Unbounded.Op.and 2, ![Wire.input 0, Wire.input 2]⟩).gate
      ⟨Unbounded.Op.and 2, ![Wire.input 1, Wire.input 2]⟩).gate
      ⟨Unbounded.Op.or 3, ![Wire.gate 0, Wire.gate 1, Wire.gate 2]⟩
  outputs := fun _ => Wire.gate 3

theorem maj3Unbounded_eval (x : Fin 3 → Bool) :
    maj3Unbounded.eval Unbounded.interpretation x 0 = maj3 (x 0) (x 1) (x 2) := by
  have hall : ∀ a b c : Bool,
      maj3Unbounded.eval Unbounded.interpretation ![a, b, c] 0 = maj3 a b c := by
    unfold maj3Unbounded; decide
  have hx : x = ![x 0, x 1, x 2] := by ext i; fin_cases i <;> rfl
  rw [hx]; exact hall (x 0) (x 1) (x 2)

theorem maj3Unbounded_depth : maj3Unbounded.depth = 2 := by
  unfold maj3Unbounded; decide

/-- Helper: compose a `3`-input majority circuit over `3` copies of a sub-circuit on `m` inputs
(gives size `3 * c.size + maj.size`, depth `≤ maj.depth + c.depth`). -/
def liftMaj3 {σ : Signature} {m : ℕ} (maj : Circuit σ 3 1) (c : Circuit σ m 1) :
    Circuit σ (m + (m + m)) 1 :=
  let c0 := c.comp (Circuit.wiring σ (fun i => Fin.castAdd (m + m) i))
  let c1 := c.comp (Circuit.wiring σ (fun i => Fin.natAdd m (Fin.castAdd m i)))
  let c2 := c.comp (Circuit.wiring σ (fun i => Fin.natAdd m (Fin.natAdd m i)))
  let triple : Circuit σ (m + (m + m)) 3 :=
    (c0.append (c1.append c2)).comapOutputs (fun j => Fin.cast (by omega) j)
  maj.comp triple

theorem size_liftMaj3 {σ : Signature} {m : ℕ} (maj : Circuit σ 3 1) (c : Circuit σ m 1) :
    (liftMaj3 maj c).size = 3 * c.size + maj.size := by
  unfold liftMaj3
  dsimp only [Circuit.comapOutputs]
  simp only [Circuit.size_comp, Circuit.size_append, Circuit.size_wiring, zero_add]
  ring

theorem depth_liftMaj3_le {σ : Signature} {m : ℕ} (maj : Circuit σ 3 1) (c : Circuit σ m 1) :
    (liftMaj3 maj c).depth ≤ maj.depth + c.depth := by
  unfold liftMaj3
  refine (Circuit.depth_comp_le _ _).trans ?_
  refine Nat.add_le_add_left ?_ _
  have hcomap : ∀ {a o₁ o₂ : ℕ} (d : Circuit σ a o₁) (f : Fin o₂ → Fin o₁),
      (d.comapOutputs f).depth ≤ d.depth := by
    intro a o₁ o₂ d f
    rw [Circuit.depth_le_iff]
    intro j
    exact Circuit.outputDepths_le_depth d (f j)
  refine (hcomap _ _).trans ?_
  refine (Circuit.depth_append_le _ _).trans ?_
  have hc0 : (c.comp (Circuit.wiring σ (fun i : Fin m => Fin.castAdd (m + m) i))).depth ≤ c.depth :=
    (Circuit.depth_comp_le _ _).trans (by simp [Circuit.depth_wiring])
  have hc1 : (c.comp (Circuit.wiring σ (fun i : Fin m => Fin.natAdd m (Fin.castAdd m i)))).depth ≤
      c.depth := (Circuit.depth_comp_le _ _).trans (by simp [Circuit.depth_wiring])
  have hc2 : (c.comp (Circuit.wiring σ (fun i : Fin m => Fin.natAdd m (Fin.natAdd m i)))).depth ≤
      c.depth := (Circuit.depth_comp_le _ _).trans (by simp [Circuit.depth_wiring])
  have h12 := (Circuit.depth_append_le _ _).trans (max_le hc1 hc2)
  exact max_le hc0 h12

/-- Canonical indexing `Fin 3 → Fin 3 → Fin 3 ≃ Fin (3 + (3 + 3) + ((3 + (3 + 3)) + (3 + (3 + 3))))`
matching the nested `liftMaj3` input layout (`27` inputs). -/
abbrev Fin27 := Fin ((3 + (3 + 3)) + ((3 + (3 + 3)) + (3 + (3 + 3))))

/-- Flattening of a `3 × 3 × 3` coordinate selector into the `27` inputs of `maj3Iter3`. -/
def idx27 {n : ℕ} (t : Fin 3 → Fin 3 → Fin 3 → Fin n) : Fin27 → Fin n :=
  let row (a b : Fin 3) : Fin 3 → Fin n := t a b
  let block (a : Fin 3) : Fin (3 + (3 + 3)) → Fin n :=
    Fin.append (row a 0) (Fin.append (row a 1) (row a 2))
  Fin.append (block 0) (Fin.append (block 1) (block 2))

/-- Size-`52` De Morgan circuit computing `maj3Iter3` on `27` inputs. -/
def maj3Iter3DeMorgan : Circuit Boolean.signature 27 1 :=
  liftMaj3 maj3DeMorgan (liftMaj3 maj3DeMorgan maj3DeMorgan)

/-- Size-`52`, depth-`≤ 6` unbounded-fan-in circuit computing `maj3Iter3` on `27` inputs. -/
def maj3Iter3Unbounded : Circuit Unbounded.signature 27 1 :=
  liftMaj3 maj3Unbounded (liftMaj3 maj3Unbounded maj3Unbounded)

theorem size_maj3Iter3DeMorgan : maj3Iter3DeMorgan.size = 52 := by
  unfold maj3Iter3DeMorgan
  rw [size_liftMaj3, size_liftMaj3]
  rfl

theorem size_maj3Iter3Unbounded : maj3Iter3Unbounded.size = 52 := by
  unfold maj3Iter3Unbounded
  rw [size_liftMaj3, size_liftMaj3]
  rfl

theorem depth_maj3Iter3Unbounded_le : maj3Iter3Unbounded.depth ≤ 6 := by
  unfold maj3Iter3Unbounded
  have h1 := depth_liftMaj3_le maj3Unbounded (liftMaj3 maj3Unbounded maj3Unbounded)
  have h2 := depth_liftMaj3_le maj3Unbounded maj3Unbounded
  rw [maj3Unbounded_depth] at h1 h2
  omega

private theorem eval_liftMaj3 {σ : Signature} {I : Interpretation σ Bool} {m : ℕ}
    (maj : Circuit σ 3 1) (hmaj : ∀ y, maj.eval I y 0 = maj3 (y 0) (y 1) (y 2))
    (c : Circuit σ m 1) (u₀ u₁ u₂ : Fin m → Bool) :
    (liftMaj3 maj c).eval I (Fin.append u₀ (Fin.append u₁ u₂)) 0 =
      maj3 (c.eval I u₀ 0) (c.eval I u₁ 0) (c.eval I u₂ 0) := by
  unfold liftMaj3
  rw [Circuit.eval_comp, hmaj]
  simp only [Circuit.eval_comapOutputs, Function.comp_apply, Circuit.eval_append,
    Circuit.eval_comp, Circuit.eval_wiring]
  have h0 : Fin.append u₀ (Fin.append u₁ u₂) ∘ Fin.castAdd (m + m) = u₀ :=
    Fin.append_comp_castAdd _ _
  have h1 : Fin.append u₀ (Fin.append u₁ u₂) ∘ (fun i => Fin.natAdd m (Fin.castAdd m i)) = u₁ := by
    ext i; exact (Fin.append_right u₀ _ _).trans (Fin.append_left u₁ u₂ i)
  have h2 : Fin.append u₀ (Fin.append u₁ u₂) ∘ (fun i => Fin.natAdd m (Fin.natAdd m i)) = u₂ := by
    ext i; exact (Fin.append_right u₀ _ _).trans (Fin.append_right u₁ u₂ i)
  rw [h0, h1, h2]
  rfl

private theorem comp_idx27 {n : ℕ} (t : Fin 3 → Fin 3 → Fin 3 → Fin n) (x : Fin n → Bool) :
    x ∘ idx27 t =
      Fin.append
        (Fin.append (fun c => x (t 0 0 c))
          (Fin.append (fun c => x (t 0 1 c)) (fun c => x (t 0 2 c))))
        (Fin.append
          (Fin.append (fun c => x (t 1 0 c))
            (Fin.append (fun c => x (t 1 1 c)) (fun c => x (t 1 2 c))))
          (Fin.append (fun c => x (t 2 0 c))
            (Fin.append (fun c => x (t 2 1 c)) (fun c => x (t 2 2 c))))) := by
  have hrow : ∀ a : Fin 3, ∀ j : Fin (3 + (3 + 3)),
      x (Fin.append (t a 0) (Fin.append (t a 1) (t a 2)) j) =
        Fin.append (fun c => x (t a 0 c))
          (Fin.append (fun c => x (t a 1 c)) (fun c => x (t a 2 c))) j := fun a j => by
    refine Fin.addCases (fun k => by simp [Fin.append_left]) (fun k => ?_) j
    simp only [Fin.append_right]
    refine Fin.addCases (fun l => by simp [Fin.append_left]) (fun l => ?_) k
    rw [Fin.append_right, Fin.append_right]
  ext i
  unfold idx27
  simp only [Function.comp_apply]
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.append_left]; exact hrow 0 j
  · simp only [Fin.append_right]
    refine Fin.addCases (fun j' => ?_) (fun j' => ?_) j
    · simp only [Fin.append_left]; exact hrow 1 j'
    · simp only [Fin.append_right]; exact hrow 2 j'

theorem maj3Iter3DeMorgan_eval_comp {n : ℕ} (t : Fin 3 → Fin 3 → Fin 3 → Fin n)
    (x : Fin n → Bool) :
    (maj3Iter3DeMorgan.comp (Circuit.wiring Boolean.signature (idx27 t))).eval
      Boolean.interpretation x 0 = maj3Iter3 (fun a b c => x (t a b c)) := by
  rw [Circuit.eval_comp, Circuit.eval_wiring, comp_idx27]
  unfold maj3Iter3DeMorgan
  rw [eval_liftMaj3 maj3DeMorgan maj3DeMorgan_eval,
    eval_liftMaj3 maj3DeMorgan maj3DeMorgan_eval,
    eval_liftMaj3 maj3DeMorgan maj3DeMorgan_eval,
    eval_liftMaj3 maj3DeMorgan maj3DeMorgan_eval]
  simp only [maj3DeMorgan_eval, maj3Iter3]

theorem maj3Iter3Unbounded_eval_comp {n : ℕ} (t : Fin 3 → Fin 3 → Fin 3 → Fin n)
    (x : Fin n → Bool) :
    (maj3Iter3Unbounded.comp (Circuit.wiring Unbounded.signature (idx27 t))).eval
      Unbounded.interpretation x 0 = maj3Iter3 (fun a b c => x (t a b c)) := by
  rw [Circuit.eval_comp, Circuit.eval_wiring, comp_idx27]
  unfold maj3Iter3Unbounded
  rw [eval_liftMaj3 maj3Unbounded maj3Unbounded_eval,
    eval_liftMaj3 maj3Unbounded maj3Unbounded_eval,
    eval_liftMaj3 maj3Unbounded maj3Unbounded_eval,
    eval_liftMaj3 maj3Unbounded maj3Unbounded_eval]
  simp only [maj3Unbounded_eval, maj3Iter3]

/-! ### Exact Small-`n` Majority Circuits (`n ∈ {2, 3, 4, 6}`) -/

private def maj2DeMorgan : Circuit Boolean.signature 2 1 where
  size := 1
  program :=
    (Program.empty : Program Boolean.signature 2 0).gate
      ⟨Boolean.Op.or, ![Wire.input 0, Wire.input 1]⟩
  outputs := fun _ => Wire.gate 0

private def maj4DeMorgan : Circuit Boolean.signature 4 1 where
  size := 7
  program :=
    (((((((Program.empty : Program Boolean.signature 4 0).gate
      ⟨Boolean.Op.and, ![Wire.input 2, Wire.input 3]⟩).gate
      ⟨Boolean.Op.or, ![Wire.input 2, Wire.input 3]⟩).gate
      ⟨Boolean.Op.and, ![Wire.input 0, Wire.input 1]⟩).gate
      ⟨Boolean.Op.or, ![Wire.input 0, Wire.input 1]⟩).gate
      ⟨Boolean.Op.and, ![Wire.gate 3, Wire.gate 1]⟩).gate
      ⟨Boolean.Op.or, ![Wire.gate 2, Wire.gate 4]⟩).gate
      ⟨Boolean.Op.or, ![Wire.gate 0, Wire.gate 5]⟩
  outputs := fun _ => Wire.gate 6

private def and3DeMorgan : Circuit Boolean.signature 3 1 where
  size := 2
  program :=
    ((Program.empty : Program Boolean.signature 3 0).gate
      ⟨Boolean.Op.and, ![Wire.input 0, Wire.input 1]⟩).gate
      ⟨Boolean.Op.and, ![Wire.gate 0, Wire.input 2]⟩
  outputs := fun _ => Wire.gate 1

private def or3DeMorgan : Circuit Boolean.signature 3 1 where
  size := 2
  program :=
    ((Program.empty : Program Boolean.signature 3 0).gate
      ⟨Boolean.Op.or, ![Wire.input 0, Wire.input 1]⟩).gate
      ⟨Boolean.Op.or, ![Wire.gate 0, Wire.input 2]⟩
  outputs := fun _ => Wire.gate 1

private def maj6TopDeMorgan : Circuit Boolean.signature (1 + (1 + (1 + (1 + (1 + 1))))) 1 where
  size := 5
  program :=
    (((((Program.empty : Program Boolean.signature (1 + (1 + (1 + (1 + (1 + 1))))) 0).gate
      ⟨Boolean.Op.or, ![Wire.input 0, Wire.input 1]⟩).gate
      ⟨Boolean.Op.and, ![Wire.input 2, Wire.input 3]⟩).gate
      ⟨Boolean.Op.and, ![Wire.input 4, Wire.input 5]⟩).gate
      ⟨Boolean.Op.or, ![Wire.gate 1, Wire.gate 2]⟩).gate
      ⟨Boolean.Op.or, ![Wire.gate 0, Wire.gate 3]⟩
  outputs := fun _ => Wire.gate 4

private def maj6DeMorgan : Circuit Boolean.signature 6 1 :=
  let first3 : Circuit Boolean.signature 6 3 :=
    Circuit.wiring Boolean.signature (fun i : Fin 3 => ⟨i.val, by omega⟩)
  let last3 : Circuit Boolean.signature 6 3 :=
    Circuit.wiring Boolean.signature (fun i : Fin 3 => ⟨i.val + 3, by omega⟩)
  let c0 := and3DeMorgan.comp first3
  let c1 := and3DeMorgan.comp last3
  let c2 := maj3DeMorgan.comp first3
  let c3 := or3DeMorgan.comp last3
  let c4 := or3DeMorgan.comp first3
  let c5 := maj3DeMorgan.comp last3
  maj6TopDeMorgan.comp (c0.append (c1.append (c2.append (c3.append (c4.append c5)))))

private theorem maj2DeMorgan_computes :
    maj2DeMorgan.Computes Boolean.interpretation (single (Cslib.majority 2)) := by
  rw [Circuit.computes_single_iff]
  intro x
  have h1 : maj2DeMorgan.eval Boolean.interpretation x 0 = (x 0 || x 1) := by
    have hall : ∀ a b : Bool, maj2DeMorgan.eval Boolean.interpretation ![a, b] 0 = (a || b) := by
      unfold maj2DeMorgan; decide
    have hx : x = ![x 0, x 1] := by ext i; fin_cases i <;> rfl
    rw [hx]; exact hall (x 0) (x 1)
  rw [h1, Bool.eq_iff_iff, Cslib.majority_eq_true_iff]
  have hw : Cslib.BitString.weight x = (if x 0 then 1 else 0) + (if x 1 then 1 else 0) := by
    simp only [Cslib.BitString.weight, Finset.card_filter, Fin.sum_univ_two]
  rw [hw]
  cases x 0 <;> cases x 1 <;> simp

private theorem maj3DeMorgan_computes :
    maj3DeMorgan.Computes Boolean.interpretation (single (Cslib.majority 3)) := by
  rw [Circuit.computes_single_iff]
  intro x
  rw [maj3DeMorgan_eval, Bool.eq_iff_iff, Cslib.majority_eq_true_iff]
  have hw : Cslib.BitString.weight x =
      (if x 0 then 1 else 0) + (if x 1 then 1 else 0) + (if x 2 then 1 else 0) := by
    simp only [Cslib.BitString.weight, Finset.card_filter, Fin.sum_univ_three]
  rw [hw]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> simp [maj3]

private theorem maj4DeMorgan_computes :
    maj4DeMorgan.Computes Boolean.interpretation (single (Cslib.majority 4)) := by
  rw [Circuit.computes_single_iff]
  intro x
  have h1 : maj4DeMorgan.eval Boolean.interpretation x 0 =
      ((x 2 && x 3) || ((x 0 && x 1) || ((x 0 || x 1) && (x 2 || x 3)))) := by
    have hall : ∀ a b c d : Bool,
        maj4DeMorgan.eval Boolean.interpretation ![a, b, c, d] 0 =
          ((c && d) || ((a && b) || ((a || b) && (c || d)))) := by
      unfold maj4DeMorgan; decide
    have hx : x = ![x 0, x 1, x 2, x 3] := by ext i; fin_cases i <;> rfl
    rw [hx]; exact hall (x 0) (x 1) (x 2) (x 3)
  rw [h1, Bool.eq_iff_iff, Cslib.majority_eq_true_iff]
  have hw : Cslib.BitString.weight x =
      (if x 0 then 1 else 0) + (if x 1 then 1 else 0) +
      (if x 2 then 1 else 0) + (if x 3 then 1 else 0) := by
    simp only [Cslib.BitString.weight, Finset.card_filter, Fin.sum_univ_four]
  rw [hw]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> simp

private theorem and3DeMorgan_eval (x : Fin 3 → Bool) :
    and3DeMorgan.eval Boolean.interpretation x 0 = (x 0 && x 1 && x 2) := by
  have hall : ∀ a b c : Bool,
      and3DeMorgan.eval Boolean.interpretation ![a, b, c] 0 = (a && b && c) := by
    unfold and3DeMorgan; decide
  have hx : x = ![x 0, x 1, x 2] := by ext i; fin_cases i <;> rfl
  rw [hx]; exact hall (x 0) (x 1) (x 2)

private theorem or3DeMorgan_eval (x : Fin 3 → Bool) :
    or3DeMorgan.eval Boolean.interpretation x 0 = (x 0 || x 1 || x 2) := by
  have hall : ∀ a b c : Bool,
      or3DeMorgan.eval Boolean.interpretation ![a, b, c] 0 = (a || b || c) := by
    unfold or3DeMorgan; decide
  have hx : x = ![x 0, x 1, x 2] := by ext i; fin_cases i <;> rfl
  rw [hx]; exact hall (x 0) (x 1) (x 2)

private theorem maj6TopDeMorgan_eval (y : Fin (1 + (1 + (1 + (1 + (1 + 1))))) → Bool) :
    maj6TopDeMorgan.eval Boolean.interpretation y 0 =
      ((y 0 || y 1) || ((y 2 && y 3) || (y 4 && y 5))) := by
  have hall : ∀ a b c d e f : Bool,
      maj6TopDeMorgan.eval Boolean.interpretation ![a, b, c, d, e, f] 0 =
        ((a || b) || ((c && d) || (e && f))) := by
    unfold maj6TopDeMorgan; decide
  have hy : y = ![y 0, y 1, y 2, y 3, y 4, y 5] := by ext i; fin_cases i <;> rfl
  rw [hy]; exact hall (y 0) (y 1) (y 2) (y 3) (y 4) (y 5)

private theorem maj6DeMorgan_computes :
    maj6DeMorgan.Computes Boolean.interpretation (single (Cslib.majority 6)) := by
  rw [Circuit.computes_single_iff]
  intro x
  have hev : maj6DeMorgan.eval Boolean.interpretation x 0 =
      (((x 0 && x 1 && x 2) || (x 3 && x 4 && x 5)) ||
       ((maj3 (x 0) (x 1) (x 2) && (x 3 || x 4 || x 5)) ||
        ((x 0 || x 1 || x 2) && maj3 (x 3) (x 4) (x 5)))) := by
    unfold maj6DeMorgan
    rw [Circuit.eval_comp, maj6TopDeMorgan_eval]
    simp only [Circuit.eval_append, Circuit.eval_comp, Circuit.eval_wiring]
    have h0 : (and3DeMorgan.eval Boolean.interpretation fun i : Fin 3 => x ⟨i.val, by omega⟩) 0 =
        (x 0 && x 1 && x 2) := and3DeMorgan_eval _
    have h1 : (and3DeMorgan.eval Boolean.interpretation fun i : Fin 3 => x ⟨i.val +
      3, by omega⟩) 0 =
        (x 3 && x 4 && x 5) := and3DeMorgan_eval _
    have h2 : (maj3DeMorgan.eval Boolean.interpretation fun i : Fin 3 => x ⟨i.val, by omega⟩) 0 =
        maj3 (x 0) (x 1) (x 2) := maj3DeMorgan_eval _
    have h3 : (or3DeMorgan.eval Boolean.interpretation fun i : Fin 3 => x ⟨i.val + 3, by omega⟩) 0 =
        (x 3 || x 4 || x 5) := or3DeMorgan_eval _
    have h4 : (or3DeMorgan.eval Boolean.interpretation fun i : Fin 3 => x ⟨i.val, by omega⟩) 0 =
        (x 0 || x 1 || x 2) := or3DeMorgan_eval _
    have h5 : (maj3DeMorgan.eval Boolean.interpretation fun i : Fin 3 => x ⟨i.val +
      3, by omega⟩) 0 =
        maj3 (x 3) (x 4) (x 5) := maj3DeMorgan_eval _
    change ((_ || _) || ((_ && _) || (_ && _))) = _
    rw [← h0, ← h1, ← h2, ← h3, ← h4, ← h5]
    rfl
  rw [hev, Bool.eq_iff_iff, Cslib.majority_eq_true_iff]
  have hw : Cslib.BitString.weight x =
      ((if x 0 then 1 else 0) + (if x 1 then 1 else 0) + (if x 2 then 1 else 0)) +
      ((if x 3 then 1 else 0) + (if x 4 then 1 else 0) + (if x 5 then 1 else 0)) := by
    simp only [Cslib.BitString.weight, Finset.card_filter, Fin.sum_univ_six]; omega
  rw [hw]
  have htrip : ∀ a b c : Bool,
      let w := (if a then 1 else 0) + (if b then 1 else 0) + (if c then 1 else 0)
      ((a && b && c) = true ↔ 3 ≤ w) ∧
      (maj3 a b c = true ↔ 2 ≤ w) ∧
      ((a || b || c) = true ↔ 1 ≤ w) := fun a b c => by
    cases a <;> cases b <;> cases c <;> simp [maj3]
  obtain ⟨ha3, ha2, ha1⟩ := htrip (x 0) (x 1) (x 2)
  obtain ⟨hb3, hb2, hb1⟩ := htrip (x 3) (x 4) (x 5)
  simp only [Bool.or_eq_true, Bool.and_eq_true, ha3, ha2, ha1, hb3, hb2, hb1]
  omega

private theorem maj2DeMorgan_depth_le : maj2DeMorgan.depth ≤ 6 := by
  unfold maj2DeMorgan; decide
private theorem maj3DeMorgan_depth_le : maj3DeMorgan.depth ≤ 6 := by
  unfold maj3DeMorgan; decide
private theorem maj4DeMorgan_depth_le : maj4DeMorgan.depth ≤ 6 := by
  unfold maj4DeMorgan; decide
private theorem maj6DeMorgan_depth_le : maj6DeMorgan.depth ≤ 6 := by
  have hd_and3 : and3DeMorgan.depth ≤ 3 :=
    (Circuit.depth_le_size _).trans (by decide)
  have hd_or3 : or3DeMorgan.depth ≤ 3 :=
    (Circuit.depth_le_size _).trans (by decide)
  have hd_maj3 : maj3DeMorgan.depth ≤ 3 := by unfold maj3DeMorgan; decide
  have hd_top : maj6TopDeMorgan.depth ≤ 3 := by unfold maj6TopDeMorgan; decide
  have hbr : ∀ (c : Circuit Boolean.signature 3 1) (f : Fin 3 → Fin 6),
      c.depth ≤ 3 → (c.comp (Circuit.wiring Boolean.signature f)).depth ≤ 3 := fun c f hc =>
    (Circuit.depth_comp_le _ _).trans (by simp only [Circuit.depth_wiring, add_zero]; exact hc)
  unfold maj6DeMorgan
  refine (Circuit.depth_comp_le _ _).trans ((Nat.add_le_add hd_top (?_ : _ ≤ 3)).trans (by decide))
  refine (Circuit.depth_append_le _ _).trans (max_le (hbr _ _ hd_and3) ?_)
  refine (Circuit.depth_append_le _ _).trans (max_le (hbr _ _ hd_and3) ?_)
  refine (Circuit.depth_append_le _ _).trans (max_le (hbr _ _ hd_maj3) ?_)
  refine (Circuit.depth_append_le _ _).trans (max_le (hbr _ _ hd_or3) ?_)
  exact (Circuit.depth_append_le _ _).trans (max_le (hbr _ _ hd_or3) (hbr _ _ hd_maj3))

private theorem maj6DeMorgan_size_le : maj6DeMorgan.size ≤ 52 := by
  unfold maj6DeMorgan
  simp only [Circuit.size_comp, Circuit.size_append, Circuit.size_wiring]
  decide

/-! ### Part 4: Coordinate-Projection Bound and Non-Existence of Hard-Core Sets -/

/-- Single-coordinate-projection remark:
For every odd `n ≥ 1` and every `S : Finset (Fin n → Bool)`, some single coordinate
projection `x ↦ x i` (size `0`, depth `0`) agrees with `Cslib.majority n` on at least a
`1/2 + 1/(2n)` fraction of `S`. For even `n ≥ 2`, the corresponding bound is `1/2`. -/
theorem single_coord_projection_agree_odd {n : ℕ} (hodd : n % 2 = 1)
    (S : Finset (Fin n → Bool)) :
    ∃ i : Fin n,
      (1 / 2 + 1 / (2 * (n : ℝ))) * (#S : ℝ) ≤
        (#(S.filter fun x => x i = Cslib.majority n x) : ℝ) := by
  have hn : 0 < n := by omega
  have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hpoint : ∀ x : Fin n → Bool,
      (1 / 2 + 1 / (2 * (n : ℝ))) * (n : ℝ) ≤
        ∑ i : Fin n, if x i = Cslib.majority n x then (1 : ℝ) else 0 := by
    intro x
    have hcard : (1 / 2 + 1 / (2 * (n : ℝ))) * (n : ℝ) = ((n : ℝ) + 1) / 2 := by
      field_simp [hnr.ne']
    rw [hcard]
    cases hmaj : Cslib.majority n x
    · have hlt : Cslib.BitString.weight x < (n + 1) / 2 := by
        have hnot : ¬ (n + 1) / 2 ≤ Cslib.BitString.weight x :=
          mt Cslib.majority_eq_true_iff.mpr (by simp [hmaj])
        omega
      have hsum_f : (∑ i : Fin n, if x i = false then (1 : ℝ) else 0) =
          (n : ℝ) - (Cslib.BitString.weight x : ℝ) := by
        have hadd : (∑ i : Fin n, if x i = false then (1 : ℝ) else 0) +
            (∑ i : Fin n, if x i = true then (1 : ℝ) else 0) = (n : ℝ) := by
          rw [← Finset.sum_add_distrib]
          have h1 : ∀ i : Fin n,
              (if x i = false then (1 : ℝ) else 0) + (if x i = true then (1 : ℝ) else 0) = 1 :=
            fun i => by cases x i <;> simp
          simp_rw [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        have hw : (∑ i : Fin n, if x i = true then (1 : ℝ) else 0) =
            (Cslib.BitString.weight x : ℝ) := by
          simp [Cslib.BitString.weight, Finset.sum_boole]
        linarith
      rw [hsum_f]
      have hnat : 2 * Cslib.BitString.weight x + 1 ≤ n := by omega
      have hreal : (2 : ℝ) * (Cslib.BitString.weight x : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hnat
      linarith
    · have hge : (n + 1) / 2 ≤ Cslib.BitString.weight x :=
        Cslib.majority_eq_true_iff.mp hmaj
      have hw : (∑ i : Fin n, if x i = true then (1 : ℝ) else 0) =
          (Cslib.BitString.weight x : ℝ) := by
        simp [Cslib.BitString.weight, Finset.sum_boole]
      rw [hw]
      have hnat : n + 1 ≤ 2 * Cslib.BitString.weight x := by omega
      have hreal : (n : ℝ) + 1 ≤ 2 * (Cslib.BitString.weight x : ℝ) := by exact_mod_cast hnat
      linarith
  have htot :
      (n : ℝ) * ((1 / 2 + 1 / (2 * (n : ℝ))) * (#S : ℝ)) ≤
        ∑ i : Fin n, (#(S.filter fun x => x i = Cslib.majority n x) : ℝ) := by
    have hswap :
        (∑ i : Fin n, (#(S.filter fun x => x i = Cslib.majority n x) : ℝ)) =
          ∑ x ∈ S, ∑ i : Fin n, if x i = Cslib.majority n x then (1 : ℝ) else 0 := by
      simp_rw [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      exact Finset.sum_comm
    rw [hswap]
    calc (n : ℝ) * ((1 / 2 + 1 / (2 * (n : ℝ))) * (#S : ℝ))
        = ∑ _x ∈ S, (1 / 2 + 1 / (2 * (n : ℝ))) * (n : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ x ∈ S, ∑ i : Fin n, if x i = Cslib.majority n x then (1 : ℝ) else 0 :=
          Finset.sum_le_sum fun x _ => hpoint x
  by_contra h
  push Not at h
  have hlt : (∑ i : Fin n, (#(S.filter fun x => x i = Cslib.majority n x) : ℝ)) <
      ∑ _i : Fin n, (1 / 2 + 1 / (2 * (n : ℝ))) * (#S : ℝ) :=
    Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) (fun i _ => h i)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlt
  linarith

/-- Core averaging theorem: for every `n ≥ 2` and every nonempty `S : Finset (Fin n → Bool)`,
there exists a Boolean function `g : (Fin n → Bool) → Bool` computed BOTH by an
`Unbounded.signature` circuit of depth `≤ 6` and size `≤ 52` AND by a De Morgan
`Boolean.signature` circuit of size `≤ 52`, such that
`(1 / 2 + 1 / n) * #S ≤ #{x ∈ S | g x = Cslib.majority n x}`. -/
theorem exists_small_AC0_agree_majority {n : ℕ} (hn : 2 ≤ n)
    (S : Finset (Fin n → Bool)) (hS : S.Nonempty) :
    ∃ (C_unb : Circuit Unbounded.signature n 1) (C_dm : Circuit Boolean.signature n 1),
      C_unb.depth ≤ 6 ∧ C_unb.size ≤ 52 ∧ C_dm.size ≤ 52 ∧
      (∀ x, C_unb.eval Unbounded.interpretation x 0 = C_dm.eval Boolean.interpretation x 0) ∧
      (1 / 2 + 1 / (n : ℝ)) * (#S : ℝ) ≤
        (#(S.filter fun x => C_unb.eval Unbounded.interpretation x 0 =
          Cslib.majority n x) : ℝ) := by
  have hn0 : 0 < n := by omega
  have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hS_pos : (0 : ℝ) < (#S : ℝ) := by exact_mod_cast hS.card_pos
  -- Small exact cases `n ∈ {2, 3, 4, 6}`:
  have hexact : ∀ (C_dm : Circuit Boolean.signature n 1),
      C_dm.depth ≤ 6 → C_dm.size ≤ 52 →
      C_dm.Computes Boolean.interpretation (single (Cslib.majority n)) →
      ∃ (C_unb : Circuit Unbounded.signature n 1) (C_dm' : Circuit Boolean.signature n 1),
        C_unb.depth ≤ 6 ∧ C_unb.size ≤ 52 ∧ C_dm'.size ≤ 52 ∧
        (∀ x, C_unb.eval Unbounded.interpretation x 0 = C_dm'.eval Boolean.interpretation x 0) ∧
        (1 / 2 + 1 / (n : ℝ)) * (#S : ℝ) ≤
          (#(S.filter fun x =>
            C_unb.eval Unbounded.interpretation x 0 = Cslib.majority n x) : ℝ) := by
    intro C_dm hdep hsz hcomp
    refine ⟨C_dm.mapOp Unbounded.deMorganToUnbounded, C_dm,
      by rwa [Circuit.depth_mapOp], by simpa using hsz, hsz, ?_, ?_⟩
    · intro x
      have h := Circuit.eval_mapOp (φ := Unbounded.deMorganToUnbounded)
        (I := Boolean.interpretation) (J := Unbounded.interpretation) C_dm x
      exact congrFun h 0
    · have hfilt : (S.filter fun x =>
          (C_dm.mapOp Unbounded.deMorganToUnbounded).eval Unbounded.interpretation x 0 =
            Cslib.majority n x) = S := by
        refine Finset.filter_true_of_mem fun x _ => ?_
        have h := congrFun (Circuit.eval_mapOp (φ := Unbounded.deMorganToUnbounded)
          (I := Boolean.interpretation) (J := Unbounded.interpretation) C_dm x) 0
        rw [h]
        exact (Circuit.computes_single_iff.mp hcomp) x
      rw [hfilt]
      have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hle1 : (1 / 2 : ℝ) + 1 / (n : ℝ) ≤ 1 := by
        have : 1 / (n : ℝ) ≤ 1 / 2 := by
          rw [div_le_div_iff₀ hnr (by norm_num : (0 : ℝ) < 2)]
          linarith
        linarith
      nlinarith
  by_cases h2 : n = 2
  · subst h2; exact hexact maj2DeMorgan maj2DeMorgan_depth_le (by decide) maj2DeMorgan_computes
  by_cases h3 : n = 3
  · subst h3; exact hexact maj3DeMorgan maj3DeMorgan_depth_le (by decide) maj3DeMorgan_computes
  by_cases h4 : n = 4
  · subst h4; exact hexact maj4DeMorgan maj4DeMorgan_depth_le (by decide) maj4DeMorgan_computes
  by_cases h6 : n = 6
  · subst h6
    exact hexact maj6DeMorgan maj6DeMorgan_depth_le maj6DeMorgan_size_le maj6DeMorgan_computes
  -- Remaining cases: either `n` is odd with `5 ≤ n`, or `n` is even with `8 ≤ n`.
  -- Helper: agreement probability of `maj3Iter3` on a single input `x`.
  let agreeMaj (x : Fin n → Bool) : ℝ :=
    (∑ t : Fin 3 → Fin 3 → Fin 3 → Fin n,
      if maj3Iter3 (fun a b c => x (t a b c)) = Cslib.majority n x then (1 : ℝ) else 0) /
    (n : ℝ) ^ 27
  have hagree_true : ∀ x : Fin n → Bool, Cslib.majority n x = true →
      agreeMaj x = maj3Prob (maj3Prob (maj3Prob ((Cslib.BitString.weight x : ℝ) / (n : ℝ)))) := by
    intro x hmaj
    simp only [agreeMaj, hmaj]
    exact maj3Iter3_avg_eq hn0 x
  have hagree_false : ∀ x : Fin n → Bool, Cslib.majority n x = false →
      agreeMaj x =
        maj3Prob (maj3Prob (maj3Prob (1 - (Cslib.BitString.weight x : ℝ) / (n : ℝ)))) := by
    intro x hmaj
    simp only [agreeMaj, hmaj]
    exact maj3Iter3_avg_false_eq hn0 x
  -- Helper to extract a concrete `t` from an average bound on `agreeMaj`.
  have hextract_maj :
      (1 / 2 + 1 / (n : ℝ)) * (#S : ℝ) ≤ ∑ x ∈ S, agreeMaj x →
      ∃ (C_unb : Circuit Unbounded.signature n 1) (C_dm : Circuit Boolean.signature n 1),
        C_unb.depth ≤ 6 ∧ C_unb.size ≤ 52 ∧ C_dm.size ≤ 52 ∧
        (∀ x, C_unb.eval Unbounded.interpretation x 0 = C_dm.eval Boolean.interpretation x 0) ∧
        (1 / 2 + 1 / (n : ℝ)) * (#S : ℝ) ≤
          (#(S.filter fun x =>
            C_unb.eval Unbounded.interpretation x 0 = Cslib.majority n x) : ℝ) := by
    intro havg
    have hpow_pos : (0 : ℝ) < (n : ℝ) ^ 27 := by positivity
    have htot :
        (n : ℝ) ^ 27 * ((1 / 2 + 1 / (n : ℝ)) * (#S : ℝ)) ≤
          ∑ t : Fin 3 → Fin 3 → Fin 3 → Fin n,
            (#(S.filter fun x =>
              maj3Iter3 (fun a b c => x (t a b c)) = Cslib.majority n x) : ℝ) := by
      have hswap :
          (∑ t : Fin 3 → Fin 3 → Fin 3 → Fin n,
            (#(S.filter fun x =>
              maj3Iter3 (fun a b c => x (t a b c)) = Cslib.majority n x) : ℝ)) =
            ∑ x ∈ S, ∑ t : Fin 3 → Fin 3 → Fin 3 → Fin n,
              if maj3Iter3 (fun a b c => x (t a b c)) = Cslib.majority n x then (1 : ℝ) else 0 := by
        simp_rw [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
        exact Finset.sum_comm
      rw [hswap]
      have hmul :
          (n : ℝ) ^ 27 * ∑ x ∈ S, agreeMaj x =
            ∑ x ∈ S, ∑ t : Fin 3 → Fin 3 → Fin 3 → Fin n,
              if maj3Iter3 (fun a b c => x (t a b c)) = Cslib.majority n x then (1 : ℝ) else 0 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        dsimp only [agreeMaj]
        field_simp [hpow_pos.ne']
      rw [← hmul]
      exact mul_le_mul_of_nonneg_left havg hpow_pos.le
    have hcardT : (Fintype.card (Fin 3 → Fin 3 → Fin 3 → Fin n) : ℝ) = (n : ℝ) ^ 27 := by
      simp only [Fintype.card_fun, Fintype.card_fin]; push_cast; ring
    have hexT : ∃ t : Fin 3 → Fin 3 → Fin 3 → Fin n,
        (1 / 2 + 1 / (n : ℝ)) * (#S : ℝ) ≤
          (#(S.filter fun x =>
            maj3Iter3 (fun a b c => x (t a b c)) = Cslib.majority n x) : ℝ) := by
      by_contra hnot
      push Not at hnot
      have : Nonempty (Fin 3 → Fin 3 → Fin 3 → Fin n) := ⟨fun _ _ _ => ⟨0, hn0⟩⟩
      have hlt :
          (∑ t : Fin 3 → Fin 3 → Fin 3 → Fin n,
            (#(S.filter fun x =>
              maj3Iter3 (fun a b c => x (t a b c)) = Cslib.majority n x) : ℝ)) <
          ∑ _t : Fin 3 → Fin 3 → Fin 3 → Fin n, (1 / 2 + 1 / (n : ℝ)) * (#S : ℝ) :=
        Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun t _ => hnot t
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardT] at hlt
      linarith
    obtain ⟨t, ht⟩ := hexT
    let C_unb := maj3Iter3Unbounded.comp (Circuit.wiring Unbounded.signature (idx27 t))
    let C_dm := maj3Iter3DeMorgan.comp (Circuit.wiring Boolean.signature (idx27 t))
    refine ⟨C_unb, C_dm, ?_, ?_, ?_, ?_, ?_⟩
    · refine (Circuit.depth_comp_le _ _).trans ?_
      rw [Circuit.depth_wiring, add_zero]
      exact depth_maj3Iter3Unbounded_le
    · rw [Circuit.size_comp, Circuit.size_wiring, zero_add, size_maj3Iter3Unbounded]
    · rw [Circuit.size_comp, Circuit.size_wiring, zero_add, size_maj3Iter3DeMorgan]
    · intro x
      rw [maj3Iter3Unbounded_eval_comp, maj3Iter3DeMorgan_eval_comp]
    · simpa [C_unb, maj3Iter3Unbounded_eval_comp] using ht
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · -- Even case: `n = 2 * m` with `8 ≤ 2 * m` (so `m ≥ 4`).
    have hm4 : 4 ≤ m := by omega
    have hn8 : 8 ≤ 2 * m := by omega
    have hnr8 : (8 : ℝ) ≤ (2 * m : ℕ) := by exact_mod_cast hn8
    let α : ℝ := 2 / ((2 * m : ℕ) : ℝ)
    have hα0 : 0 ≤ α := by positivity
    have hα1 : α ≤ 1 / 4 := by
      dsimp only [α]
      rw [div_le_div_iff₀ hnr (by norm_num : (0 : ℝ) < 4)]
      linarith
    -- Pointwise convex-mixture bound: `α * 1[maj x = true] + (1 - α) * agreeMaj x ≥ 1/2 + 1/n`.
    have hmix : ∀ x : Fin (2 * m) → Bool,
        1 / 2 + 1 / ((2 * m : ℕ) : ℝ) ≤
          α * (if Cslib.majority (2 * m) x = true then (1 : ℝ) else 0) +
            (1 - α) * agreeMaj x := by
      intro x
      have hw_le : (Cslib.BitString.weight x : ℝ) / ((2 * m : ℕ) : ℝ) ≤ 1 := by
        rw [div_le_one hnr]
        exact_mod_cast (Finset.card_le_univ _).trans_eq (Fintype.card_fin (2 * m))
      have hw_nonneg : 0 ≤ (Cslib.BitString.weight x : ℝ) / ((2 * m : ℕ) : ℝ) := by positivity
      cases hmaj : Cslib.majority (2 * m) x
      · -- Case `majority (2 * m) x = false`: `weight x ≤ m - 1`.
        rw [hagree_false x hmaj]
        simp only [Bool.false_eq_true, ↓reduceIte, mul_zero, zero_add]
        have hlt : Cslib.BitString.weight x < m := by
          have hnot : ¬ (2 * m + 1) / 2 ≤ Cslib.BitString.weight x :=
            mt Cslib.majority_eq_true_iff.mpr (by simp [hmaj])
          omega
        have h1m : 1 / 2 + 1 / ((2 * m : ℕ) : ℝ) ≤
            1 - (Cslib.BitString.weight x : ℝ) / ((2 * m : ℕ) : ℝ) := by
          have hnat : Cslib.BitString.weight x + 1 ≤ m := by omega
          have hreal : (Cslib.BitString.weight x : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hnat
          have h2m : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
          rw [h2m]
          have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
          rw [le_sub_iff_add_le]
          have : (1 / 2 + 1 / (2 * (m : ℝ))) + (Cslib.BitString.weight x : ℝ) / (2 * (m : ℝ)) =
              ((m : ℝ) + 1 + (Cslib.BitString.weight x : ℝ)) / (2 * (m : ℝ)) := by
            field_simp [hmpos.ne']
          rw [this, div_le_one (by positivity)]
          linarith
        have hmono3 :
            maj3Prob (maj3Prob (maj3Prob (1 / 2 + 1 / ((2 * m : ℕ) : ℝ)))) ≤
              maj3Prob (maj3Prob (maj3Prob (1 -
                (Cslib.BitString.weight x : ℝ) / ((2 * m : ℕ) : ℝ)))) := by
          have hp0 : (0 : ℝ) ≤ 1 / 2 + 1 / ((2 * m : ℕ) : ℝ) := by positivity
          have hq1 : 1 - (Cslib.BitString.weight x : ℝ) / ((2 * m : ℕ) : ℝ) ≤ 1 := by linarith
          have m1 := maj3Prob_mono hp0 hq1 h1m
          have b1 := maj3Prob_mem_Icc hp0 (h1m.trans hq1)
          have b1' := maj3Prob_mem_Icc (hp0.trans h1m) hq1
          have m2 := maj3Prob_mono b1.1 b1'.2 m1
          have b2 := maj3Prob_mem_Icc b1.1 b1.2
          have b2' := maj3Prob_mem_Icc b1'.1 b1'.2
          exact maj3Prob_mono b2.1 b2'.2 m2
        have hamp := maj3Prob_iter3_ge (d := 1 / ((2 * m : ℕ) : ℝ)) (by positivity)
          (by rw [div_le_div_iff₀ hnr (by norm_num : (0 : ℝ) < 8)]; linarith)
        have hge : 1 / 2 + (14 / 5 : ℝ) * (1 / ((2 * m : ℕ) : ℝ)) ≤
            maj3Prob (maj3Prob (maj3Prob (1 -
              (Cslib.BitString.weight x : ℝ) / ((2 * m : ℕ) : ℝ)))) :=
          hamp.trans hmono3
        have h1α : (3 / 4 : ℝ) ≤ 1 - α := by linarith
        have hmul := mul_le_mul_of_nonneg_left hge (by linarith : (0 : ℝ) ≤ 1 - α)
        have hd_pos : (0 : ℝ) < 1 / ((2 * m : ℕ) : ℝ) := by positivity
        have hα_eq : α = 2 * (1 / ((2 * m : ℕ) : ℝ)) := by dsimp only [α]; ring
        nlinarith
      · -- `majority (2 * m) x = true`, so `weight x ≥ m`, hence `weight x / n ≥ 1/2`.
        rw [hagree_true x hmaj]
        simp only [↓reduceIte, mul_one]
        have hge_m : m ≤ Cslib.BitString.weight x := by
          have := Cslib.majority_eq_true_iff.mp hmaj
          omega
        have hhalf : (1 / 2 : ℝ) ≤ (Cslib.BitString.weight x : ℝ) / ((2 * m : ℕ) : ℝ) := by
          have hreal : (m : ℝ) ≤ (Cslib.BitString.weight x : ℝ) := by exact_mod_cast hge_m
          have h2m : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
          rw [h2m, le_div_iff₀ (by positivity)]
          linarith
        have hmono3 :
            (1 / 2 : ℝ) ≤
              maj3Prob (maj3Prob (maj3Prob ((Cslib.BitString.weight x : ℝ) / ((2 * m : ℕ) : ℝ))))
                := by
          have m1 : 1 / 2 ≤ maj3Prob ((Cslib.BitString.weight x : ℝ) / ((2 * m : ℕ) : ℝ)) := by
            rw [← maj3Prob_half]; exact maj3Prob_mono (by norm_num) hw_le hhalf
          have b1 := maj3Prob_mem_Icc hw_nonneg hw_le
          have m2 : 1 / 2 ≤
            maj3Prob (maj3Prob ((Cslib.BitString.weight x : ℝ) / ((2 * m : ℕ) : ℝ))) := by
            rw [← maj3Prob_half]; exact maj3Prob_mono (by norm_num) b1.2 m1
          have b2 := maj3Prob_mem_Icc b1.1 b1.2
          rw [← maj3Prob_half]; exact maj3Prob_mono (by norm_num) b2.2 m2
        have hα_eq : α = 2 * (1 / ((2 * m : ℕ) : ℝ)) := by dsimp only [α]; ring
        nlinarith
    -- Sum `hmix` over `S`: either `constTrue` or `maj3Iter3` achieves `≥ (1/2 + 1/n) * #S`!
    have hsum_mix :
        (1 / 2 + 1 / ((2 * m : ℕ) : ℝ)) * (#S : ℝ) ≤
          α * (#(S.filter fun x => Cslib.majority (2 * m) x = true) : ℝ) +
            (1 - α) * ∑ x ∈ S, agreeMaj x := by
      have hcard_t :
          (#(S.filter fun x => Cslib.majority (2 * m) x = true) : ℝ) =
            ∑ x ∈ S, if Cslib.majority (2 * m) x = true then (1 : ℝ) else 0 := by
        rw [Finset.card_filter, Nat.cast_sum]
        simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      rw [hcard_t, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      calc (1 / 2 + 1 / ((2 * m : ℕ) : ℝ)) * (#S : ℝ)
          = ∑ _x ∈ S, (1 / 2 + 1 / ((2 * m : ℕ) : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ _ := Finset.sum_le_sum fun x _ => hmix x
    by_cases hconst :
        (1 / 2 + 1 / ((2 * m : ℕ) : ℝ)) * (#S : ℝ) ≤
          (#(S.filter fun x => Cslib.majority (2 * m) x = true) : ℝ)
    · refine ⟨(constTrueDeMorgan (2 * m)).mapOp Unbounded.deMorganToUnbounded,
        constTrueDeMorgan (2 * m), ?_, ?_, ?_, ?_, ?_⟩
      · rw [Circuit.depth_mapOp]; exact (constTrueDeMorgan_depth_le _).trans (by decide)
      · simp [constTrueDeMorgan]
      · simp [constTrueDeMorgan]
      · intro x
        exact congrFun (Circuit.eval_mapOp (φ := Unbounded.deMorganToUnbounded)
          (I := Boolean.interpretation) (J := Unbounded.interpretation)
          (constTrueDeMorgan (2 * m)) x) 0
      · have heq : ∀ x : Fin (2 * m) → Bool,
            ((constTrueDeMorgan (2 * m)).mapOp Unbounded.deMorganToUnbounded).eval
              Unbounded.interpretation x 0 = true := fun x => by
          have h := congrFun (Circuit.eval_mapOp (φ := Unbounded.deMorganToUnbounded)
            (I := Boolean.interpretation) (J := Unbounded.interpretation)
            (constTrueDeMorgan (2 * m)) x) 0
          rw [h]; exact constTrueDeMorgan_eval _ x
        have hfilt : (S.filter fun x =>
            ((constTrueDeMorgan (2 * m)).mapOp Unbounded.deMorganToUnbounded).eval
              Unbounded.interpretation x 0 = Cslib.majority (2 * m) x) =
            S.filter fun x => Cslib.majority (2 * m) x = true := by
          refine Finset.filter_congr fun x _ => ?_
          rw [heq x, eq_comm]
        rwa [hfilt]
    · push Not at hconst
      have hmaj_avg : (1 / 2 + 1 / ((2 * m : ℕ) : ℝ)) * (#S : ℝ) ≤ ∑ x ∈ S, agreeMaj x := by
        nlinarith
      exact hextract_maj hmaj_avg
  · -- Odd case: `n = 2 * m + 1` with `5 ≤ 2 * m + 1` (so `m ≥ 2`).
    have hm2 : 2 ≤ m := by omega
    have hn5 : 5 ≤ 2 * m + 1 := by omega
    have hnr5 : (5 : ℝ) ≤ (2 * m + 1 : ℕ) := by exact_mod_cast hn5
    have hpt : ∀ x : Fin (2 * m + 1) → Bool,
        1 / 2 + 1 / ((2 * m + 1 : ℕ) : ℝ) ≤ agreeMaj x := by
      intro x
      have hw_le : (Cslib.BitString.weight x : ℝ) / ((2 * m + 1 : ℕ) : ℝ) ≤ 1 := by
        rw [div_le_one hnr]
        exact_mod_cast (Finset.card_le_univ _).trans_eq (Fintype.card_fin (2 * m + 1))
      have hw_nonneg : 0 ≤ (Cslib.BitString.weight x : ℝ) / ((2 * m + 1 : ℕ) : ℝ) := by positivity
      have hd_le : 1 / (2 * ((2 * m + 1 : ℕ) : ℝ)) ≤ 1 / 8 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 8)]
        linarith
      have hamp := maj3Prob_iter3_ge (d := 1 / (2 * ((2 * m + 1 : ℕ) : ℝ))) (by positivity) hd_le
      have hge1 : 1 / 2 + 1 / ((2 * m + 1 : ℕ) : ℝ) ≤
          maj3Prob (maj3Prob (maj3Prob (1 / 2 + 1 / (2 * ((2 * m + 1 : ℕ) : ℝ))))) := by
        have hstep : (14 / 5 : ℝ) * (1 / (2 * ((2 * m + 1 : ℕ) : ℝ))) =
            (7 / 5 : ℝ) * (1 / ((2 * m + 1 : ℕ) : ℝ)) := by ring
        have hd_pos : (0 : ℝ) < 1 / ((2 * m + 1 : ℕ) : ℝ) := by positivity
        linarith
      cases hmaj : Cslib.majority (2 * m + 1) x
      · rw [hagree_false x hmaj]
        have hlt : Cslib.BitString.weight x ≤ m := by
          have hnot : ¬ (2 * m + 1 + 1) / 2 ≤ Cslib.BitString.weight x :=
            mt Cslib.majority_eq_true_iff.mpr (by simp [hmaj])
          omega
        have hp_ge : 1 / 2 + 1 / (2 * ((2 * m + 1 : ℕ) : ℝ)) ≤
            1 - (Cslib.BitString.weight x : ℝ) / ((2 * m + 1 : ℕ) : ℝ) := by
          have hreal : (Cslib.BitString.weight x : ℝ) ≤ (m : ℝ) := by exact_mod_cast hlt
          have h2m1 : ((2 * m + 1 : ℕ) : ℝ) = 2 * (m : ℝ) + 1 := by push_cast; ring
          rw [h2m1, le_sub_iff_add_le]
          have hpos : (0 : ℝ) < 2 * (m : ℝ) + 1 := by positivity
          have : 1 / 2 + 1 / (2 * (2 * (m : ℝ) + 1)) +
              (Cslib.BitString.weight x : ℝ) / (2 * (m : ℝ) + 1) =
              (2 * (m : ℝ) + 2 + 2 * (Cslib.BitString.weight x : ℝ)) /
                (2 * (2 * (m : ℝ) + 1)) := by
            field_simp [hpos.ne']; ring
          rw [this, div_le_one (by positivity)]
          linarith
        have hmono3 :
            maj3Prob (maj3Prob (maj3Prob (1 / 2 + 1 / (2 * ((2 * m + 1 : ℕ) : ℝ))))) ≤
              maj3Prob (maj3Prob (maj3Prob (1 - (Cslib.BitString.weight x : ℝ) /
                ((2 * m + 1 : ℕ) : ℝ)))) := by
          have hp0 : (0 : ℝ) ≤ 1 / 2 + 1 / (2 * ((2 * m + 1 : ℕ) : ℝ)) := by positivity
          have hq1 : 1 - (Cslib.BitString.weight x : ℝ) / ((2 * m + 1 : ℕ) : ℝ) ≤ 1 := by linarith
          have m1 := maj3Prob_mono hp0 hq1 hp_ge
          have b1 := maj3Prob_mem_Icc hp0 (hp_ge.trans hq1)
          have b1' := maj3Prob_mem_Icc (hp0.trans hp_ge) hq1
          have m2 := maj3Prob_mono b1.1 b1'.2 m1
          have b2 := maj3Prob_mem_Icc b1.1 b1.2
          have b2' := maj3Prob_mem_Icc b1'.1 b1'.2
          exact maj3Prob_mono b2.1 b2'.2 m2
        exact hge1.trans hmono3
      · rw [hagree_true x hmaj]
        have hge : m + 1 ≤ Cslib.BitString.weight x := by
          have := Cslib.majority_eq_true_iff.mp hmaj; omega
        have hp_ge : 1 / 2 + 1 / (2 * ((2 * m + 1 : ℕ) : ℝ)) ≤
            (Cslib.BitString.weight x : ℝ) / ((2 * m + 1 : ℕ) : ℝ) := by
          have hreal : (m : ℝ) + 1 ≤ (Cslib.BitString.weight x : ℝ) := by exact_mod_cast hge
          have h2m1 : ((2 * m + 1 : ℕ) : ℝ) = 2 * (m : ℝ) + 1 := by push_cast; ring
          rw [h2m1]
          have hpos : (0 : ℝ) < 2 * (m : ℝ) + 1 := by positivity
          have : 1 / 2 + 1 / (2 * (2 * (m : ℝ) + 1)) =
              ((m : ℝ) + 1) / (2 * (m : ℝ) + 1) := by
            field_simp [hpos.ne']; ring
          rw [this]
          exact div_le_div_of_nonneg_right hreal hpos.le
        have hmono3 :
            maj3Prob (maj3Prob (maj3Prob (1 / 2 + 1 / (2 * ((2 * m + 1 : ℕ) : ℝ))))) ≤
              maj3Prob (maj3Prob (maj3Prob ((Cslib.BitString.weight x : ℝ) /
                ((2 * m + 1 : ℕ) : ℝ)))) := by
          have hp0 : (0 : ℝ) ≤ 1 / 2 + 1 / (2 * ((2 * m + 1 : ℕ) : ℝ)) := by positivity
          have m1 := maj3Prob_mono hp0 hw_le hp_ge
          have b1 := maj3Prob_mem_Icc hp0 (hp_ge.trans hw_le)
          have b1' := maj3Prob_mem_Icc (hp0.trans hp_ge) hw_le
          have m2 := maj3Prob_mono b1.1 b1'.2 m1
          have b2 := maj3Prob_mem_Icc b1.1 b1.2
          have b2' := maj3Prob_mem_Icc b1'.1 b1'.2
          exact maj3Prob_mono b2.1 b2'.2 m2
        exact hge1.trans hmono3
    refine hextract_maj ?_
    calc (1 / 2 + 1 / ((2 * m + 1 : ℕ) : ℝ)) * (#S : ℝ)
        = ∑ _x ∈ S, (1 / 2 + 1 / ((2 * m + 1 : ℕ) : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ x ∈ S, agreeMaj x := Finset.sum_le_sum fun x _ => hpt x

/-- No nonempty subset `S ⊆ {0, 1}^n` (`n ≥ 2`) is `ε`-hardcore for `Cslib.majority n` against
constant-depth unbounded-fan-in circuits for any `ε < 1 / n`: there is a circuit of depth `≤ 6`
and size `≤ 52` agreeing with `Cslib.majority n` on strictly more than `(1 / 2 + ε) * #S`
inputs in `S`. -/
theorem majority_no_hardcore_AC0 {n : ℕ} (hn : 2 ≤ n)
    (S : Finset (Fin n → Bool)) (hS : S.Nonempty) {ε : ℝ} (hε : ε < 1 / (n : ℝ)) :
    ∃ C : Circuit Unbounded.signature n 1,
      C.depth ≤ 6 ∧ C.size ≤ 52 ∧
      (1 / 2 + ε) * (#S : ℝ) <
        (#(S.filter fun x => C.eval Unbounded.interpretation x 0 = Cslib.majority n x) : ℝ) := by
  obtain ⟨C_unb, _, hdep, hsz, _, _, hagree⟩ := exists_small_AC0_agree_majority hn S hS
  have hS_pos : (0 : ℝ) < (#S : ℝ) := by exact_mod_cast hS.card_pos
  exact ⟨C_unb, hdep, hsz, lt_of_lt_of_le (by nlinarith) hagree⟩

/-- For every `n ≥ 2`, positive density `δ > 0`, advantage threshold `ε < 1 / n`, and
`H : Finset (BitString n)`, `H` is not an `(s = 52, δ, ε)`-hardcore set for
`Cslib.majority n`. -/
theorem majority_not_isHardCoreSet {n : ℕ} (hn : 2 ≤ n) {δ ε : ℝ}
    (hδ : 0 < δ) (hε : ε < 1 / (n : ℝ)) (H : Finset (BitString n)) :
    ¬ Cslib.Circuits.Boolean.IsHardCoreSet (Cslib.majority n) 52 δ ε H := by
  intro hHC
  have hH_pos : (0 : ℝ) < (#H : ℝ) := by
    have h2 : (0 : ℝ) < δ * (2 : ℝ) ^ n := by positivity
    exact lt_of_lt_of_le h2 hHC.mul_two_pow_le_card
  have hH_ne : H.Nonempty := Finset.card_pos.mp (by exact_mod_cast hH_pos)
  obtain ⟨C_unb, C_dm, _, _, hsz_dm, heq_eval, hagree⟩ :=
    exists_small_AC0_agree_majority hn H hH_ne
  let g : BooleanFunction n := fun x => C_dm.eval Boolean.interpretation x 0
  have hg_comp : C_dm.Computes Boolean.interpretation (single g) :=
    Circuit.computes_single_iff.mpr fun _ => rfl
  have hg_le : complexity Boolean.interpretation (single g) ≤ 52 :=
    (complexity_le_of_computes C_dm hg_comp).trans hsz_dm
  have hupper := hHC.card_agree_le g hg_le
  have hfilt : (H.filter fun x => C_unb.eval Unbounded.interpretation x 0 = Cslib.majority n x) =
      H.filter fun x => g x = Cslib.majority n x := by
    ext x; simp [g, heq_eval x]
  rw [hfilt] at hagree
  nlinarith

end CslibFrontier.Computability.Circuit.Boolean.HardCore
