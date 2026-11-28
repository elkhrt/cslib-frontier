module

public import Cslib.Computability.Circuit.Boolean.Basic
public import CslibFrontier.Computability.Circuit.Boolean.CarrySave
public import CslibFrontier.Computability.Circuit.Boolean.Comparison
public import CslibFrontier.Computability.Circuit.Boolean.WordConstant
public import Mathlib.InformationTheory.Hamming
import CslibFrontier.Computability.Circuit.Boolean.Simps
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Linear-Size Hamming Weight, Threshold, and Hamming-Ball Circuits

Constructs strictly linear-size De Morgan Boolean circuits on `2 ^ d` input bits:

* `rippleAddCircuit w`: ripple-carry unsigned adder with carry-in, of exact size `20 * w`.
* `addExactCircuit w`: exact unsigned adder of two `w`-bit words into `w + 1` bits, of size
  `20 * w + 1`.
* `linearWeightCircuit d`: binary-tree Hamming weight circuit on `2 ^ d` bits outputting the
  `(d + 1)`-bit binary representation of `BitString.weight x`, satisfying the exact recurrence
  `size + 20 * d + 41 = 41 * 2 ^ d` (hence `size ≤ 41 * 2 ^ d`).
* `linearWeightGeCircuit d k` and `linearWeightLeCircuit d r`: threshold circuits of size
  `≤ 49 * 2 ^ d`.
* `linearHammingBallCircuit d center r`: Hamming-ball membership circuit deciding
  `hammingDist x center ≤ r`, of size `≤ 50 * 2 ^ d`.

## Main definitions

* `CslibFrontier.Circuits.Boolean.rippleAddCircuit`
* `CslibFrontier.Circuits.Boolean.addExactCircuit`
* `CslibFrontier.Circuits.Boolean.linearWeightCircuit`
* `CslibFrontier.Circuits.Boolean.linearWeightGeCircuit`
* `CslibFrontier.Circuits.Boolean.linearWeightLeCircuit`
* `CslibFrontier.Circuits.Boolean.linearHammingBallCircuit`

## Main results

* `CslibFrontier.Circuits.Boolean.val_eval_linearWeightCircuit`
* `CslibFrontier.Circuits.Boolean.size_linearWeightCircuit_le`
* `CslibFrontier.Circuits.Boolean.eval_linearWeightGeCircuit`,
  `CslibFrontier.Circuits.Boolean.size_linearWeightGeCircuit_le`
* `CslibFrontier.Circuits.Boolean.eval_linearHammingBallCircuit`,
  `CslibFrontier.Circuits.Boolean.size_linearHammingBallCircuit_le`
-/

public section

namespace CslibFrontier.Circuits.Boolean

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open scoped BigOperators Finset

/-- One-bit full-adder cell mapping `(a, b, cin)` to `(sum, cout)` in 20 De Morgan gates. -/
private def fullAdderCell : Circuit signature 3 2 :=
  ((Formula.xor (Formula.xor (.input 0) (.input 1)) (.input 2)).toCircuit).append
    (maj3Formula (0 : Fin 3) 1 2).toCircuit

private theorem size_fullAdderCell : fullAdderCell.size = 20 := by
  simp [fullAdderCell, Formula.size_xor, maj3Formula]

private theorem eval_fullAdderCell (a b cin : Bool) :
    fullAdderCell.eval interpretation ![a, b, cin] = ![(a ^^ b) ^^ cin, maj3 a b cin] := by
  funext i
  refine Fin.addCases (m := 1) (n := 1) (fun j => ?_) (fun j => ?_) i
  · simp only [fullAdderCell, Circuit.eval_append, Fin.append_left]
    fin_cases j
    simp
  · simp only [fullAdderCell, Circuit.eval_append, Fin.append_right]
    fin_cases j
    simp [maj3Formula, maj3]

/-- Wiring selecting `(a 0, b 0, cin)` from `Fin ((w + 1) + (w + 1) + 1)`. -/
private def faIn (w : ℕ) : Fin 3 → Fin ((w + 1) + (w + 1) + 1) :=
  ![Fin.castAdd 1 (Fin.castAdd (w + 1) 0),
    Fin.castAdd 1 (Fin.natAdd (w + 1) 0),
    Fin.last ((w + 1) + (w + 1))]

/-- Wiring selecting `(Fin.tail a, Fin.tail b)` from `Fin ((w + 1) + (w + 1) + 1)`. -/
private def tailIn (w : ℕ) : Fin (w + w) → Fin ((w + 1) + (w + 1) + 1) :=
  Fin.append
    (fun i => Fin.castAdd 1 (Fin.castAdd (w + 1) i.succ))
    (fun i => Fin.castAdd 1 (Fin.natAdd (w + 1) i.succ))

/-- Wiring selecting `(Fin.tail a, Fin.tail b, c1)` from `Fin (2 + (w + w))`. -/
private def nextAddIn (w : ℕ) : Fin (w + w + 1) → Fin (2 + (w + w)) :=
  Fin.append (fun i => Fin.natAdd 2 i) (fun _ => Fin.castAdd (w + w) 1)

/-- Linear-size ripple-carry adder on two `w`-bit unsigned words plus a 1-bit carry-in, outputting
the `(w + 1)`-bit unsigned sum in `20 * w` gates. -/
def rippleAddCircuit : (w : ℕ) → Circuit signature (w + w + 1) (w + 1)
  | 0 => Circuit.id signature 1
  | w + 1 =>
    let stage1 : Circuit signature ((w + 1) + (w + 1) + 1) (2 + (w + w)) :=
      (fullAdderCell.comp (Circuit.wiring signature (faIn w))).append
        (Circuit.wiring signature (tailIn w))
    let stage2 : Circuit signature (2 + (w + w)) (1 + (w + 1)) :=
      (Circuit.wiring signature fun _ : Fin 1 => Fin.castAdd (w + w) (0 : Fin 2)).append
        ((rippleAddCircuit w).comp (Circuit.wiring signature (nextAddIn w)))
    let pack : Fin (w + 2) → Fin (1 + (w + 1)) :=
      Fin.cases (Fin.castAdd (w + 1) 0) (fun i => Fin.natAdd 1 i)
    (Circuit.wiring signature pack).comp (stage2.comp stage1)

/-- `rippleAddCircuit w` has exact size `20 * w`. -/
@[simp] theorem size_rippleAddCircuit (w : ℕ) : (rippleAddCircuit w).size = 20 * w := by
  induction w with
  | zero => rfl
  | succ w ih =>
    simp only [rippleAddCircuit, Circuit.size_comp, Circuit.size_append, Circuit.size_wiring,
      size_fullAdderCell, ih]
    ring

/-- `rippleAddCircuit w` computes exact unsigned addition `val a + val b + cin.toNat`. -/
theorem val_eval_rippleAddCircuit {w : ℕ} (a b : BitString w) (cin : Bool) :
    (BitString.equivFin (w + 1)
      ((rippleAddCircuit w).eval interpretation
        (Fin.append (Fin.append a b) (fun _ => cin))) : ℕ) =
      (BitString.equivFin w a : ℕ) + (BitString.equivFin w b : ℕ) + cin.toNat := by
  induction w generalizing cin with
  | zero =>
    have h0 : (BitString.equivFin 0 a : ℕ) = 0 := Nat.lt_one_iff.mp (BitString.equivFin 0 a).isLt
    have h1 : (BitString.equivFin 0 b : ℕ) = 0 := Nat.lt_one_iff.mp (BitString.equivFin 0 b).isLt
    conv_rhs => rw [h0, h1]
    rw [rippleAddCircuit, BitString.val_equivFin_eq_sum]
    have hcin : Fin.append (Fin.append a b) (fun _ : Fin 1 => cin) (0 : Fin (0 + 0 + 1)) = cin :=
      Fin.append_right (Fin.append a b) (fun _ : Fin 1 => cin) 0
    simp [hcin]
  | succ w ih =>
    set u := Fin.append (Fin.append a b) (fun _ : Fin 1 => cin)
    have hfa : u ∘ faIn w = ![a 0, b 0, cin] := by
      funext i
      fin_cases i
      · simp [u, faIn, -Fin.natAdd_eq_addNat]
      · simp [u, faIn, -Fin.natAdd_eq_addNat]
      · exact Fin.append_right (Fin.append a b) (fun _ : Fin 1 => cin) 0
    have htail : u ∘ tailIn w = Fin.append (Fin.tail a) (Fin.tail b) := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp [u, tailIn, Fin.tail, -Fin.natAdd_eq_addNat]
      · simp [u, tailIn, Fin.tail, -Fin.natAdd_eq_addNat]
    have hs1 : ((fullAdderCell.comp (Circuit.wiring signature (faIn w))).append
        (Circuit.wiring signature (tailIn w))).eval interpretation u =
        Fin.append ![(a 0 ^^ b 0) ^^ cin, maj3 (a 0) (b 0) cin]
          (Fin.append (Fin.tail a) (Fin.tail b)) := by
      rw [Circuit.eval_append, Circuit.eval_comp, Circuit.eval_wiring, Circuit.eval_wiring,
        hfa, htail, eval_fullAdderCell]
    set m := Fin.append ![(a 0 ^^ b 0) ^^ cin, maj3 (a 0) (b 0) cin]
      (Fin.append (Fin.tail a) (Fin.tail b))
    have hnext : m ∘ nextAddIn w =
        Fin.append (Fin.append (Fin.tail a) (Fin.tail b)) (fun _ => maj3 (a 0) (b 0) cin) := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp [m, nextAddIn, -Fin.natAdd_eq_addNat]
      · fin_cases j; simp [m, nextAddIn, -Fin.natAdd_eq_addNat]
    have heval : (rippleAddCircuit (w + 1)).eval interpretation u =
        Fin.cons ((a 0 ^^ b 0) ^^ cin)
          ((rippleAddCircuit w).eval interpretation
            (Fin.append (Fin.append (Fin.tail a) (Fin.tail b))
              (fun _ => maj3 (a 0) (b 0) cin))) := by
      funext i
      rw [rippleAddCircuit, Circuit.eval_comp, Circuit.eval_wiring, Function.comp_apply,
        Circuit.eval_comp, hs1, Circuit.eval_append]
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [m, -Fin.natAdd_eq_addNat]
      · simp only [Fin.cases_succ, Fin.append_right, Fin.cons_succ, Circuit.eval_comp,
          Circuit.eval_wiring]
        rw [hnext]
    rw [heval, BitString.val_equivFin_cons, ih (Fin.tail a) (Fin.tail b) (maj3 (a 0) (b 0) cin)]
    have ha : (BitString.equivFin (w + 1) a : ℕ) =
        (a 0).toNat + 2 * (BitString.equivFin w (Fin.tail a) : ℕ) := by
      conv_lhs => rw [← Fin.cons_self_tail a]
      exact BitString.val_equivFin_cons (a 0) (Fin.tail a)
    have hb : (BitString.equivFin (w + 1) b : ℕ) =
        (b 0).toNat + 2 * (BitString.equivFin w (Fin.tail b) : ℕ) := by
      conv_lhs => rw [← Fin.cons_self_tail b]
      exact BitString.val_equivFin_cons (b 0) (Fin.tail b)
    have hbit := toNat_xor_add_two_mul_toNat_maj3 (a 0) (b 0) cin
    omega

/-- Exact unsigned addition of two `w`-bit words into a `(w + 1)`-bit word in `20 * w + 1` gates. -/
def addExactCircuit (w : ℕ) : Circuit signature (w + w) (w + 1) :=
  (rippleAddCircuit w).comp
    ((Circuit.id signature (w + w)).append (Circuit.oneGate (.const false) Fin.elim0))

/-- `addExactCircuit w` has size `20 * w + 1`. -/
@[simp] theorem size_addExactCircuit (w : ℕ) : (addExactCircuit w).size = 20 * w + 1 := by
  simp [addExactCircuit, Nat.add_comm]

/-- `addExactCircuit w` computes `val a + val b` exactly. -/
theorem val_eval_addExactCircuit {w : ℕ} (a b : BitString w) :
    (BitString.equivFin (w + 1)
      ((addExactCircuit w).eval interpretation (Fin.append a b)) : ℕ) =
      (BitString.equivFin w a : ℕ) + (BitString.equivFin w b : ℕ) := by
  have hone : (Circuit.oneGate (σ := signature) (.const false) Fin.elim0).eval interpretation
      (Fin.append a b) = fun _ => false := funext fun _ => rfl
  have hid : (Circuit.id signature (w + w)).eval interpretation (Fin.append a b) =
      Fin.append a b := by simp
  rw [addExactCircuit, Circuit.eval_comp, Circuit.eval_append, hid, hone]
  simpa using val_eval_rippleAddCircuit a b false

/-- Linear-size binary-tree Hamming weight circuit on `2 ^ d` input bits, outputting the
`(d + 1)`-bit unsigned binary representation of `BitString.weight x`. -/
def linearWeightCircuit : (d : ℕ) → Circuit signature (2 ^ d) (d + 1)
  | 0 => Circuit.id signature 1
  | d + 1 =>
    let splitL : Fin (2 ^ d) → Fin (2 ^ (d + 1)) := fun i => ⟨i.val, by
      have := i.isLt; rw [pow_succ]; omega⟩
    let splitR : Fin (2 ^ d) → Fin (2 ^ (d + 1)) := fun i => ⟨2 ^ d + i.val, by
      have := i.isLt; rw [pow_succ]; omega⟩
    (addExactCircuit (d + 1)).comp
      (((linearWeightCircuit d).comp (Circuit.wiring signature splitL)).append
        ((linearWeightCircuit d).comp (Circuit.wiring signature splitR)))

/-- Exact closed-form recurrence bound: `(linearWeightCircuit d).size ≤ 41 * 2 ^ d`. -/
theorem size_linearWeightCircuit_le (d : ℕ) : (linearWeightCircuit d).size ≤ 41 * 2 ^ d := by
  suffices h : (linearWeightCircuit d).size + 20 * d + 41 = 41 * 2 ^ d by omega
  induction d with
  | zero => simp [linearWeightCircuit]
  | succ d ih =>
    simp only [linearWeightCircuit, Circuit.size_comp, Circuit.size_append, Circuit.size_wiring,
      size_addExactCircuit]
    rw [pow_succ]
    omega

/-- `linearWeightCircuit d` computes the exact Hamming weight `BitString.weight x`. -/
theorem val_eval_linearWeightCircuit {d : ℕ} (x : BitString (2 ^ d)) :
    (BitString.equivFin (d + 1) ((linearWeightCircuit d).eval interpretation x) : ℕ) =
      BitString.weight x := by
  induction d with
  | zero =>
    rw [linearWeightCircuit, BitString.val_equivFin_eq_sum, BitString.weight_eq_sum_toNat]
    simp
  | succ d ih =>
    let splitL : Fin (2 ^ d) → Fin (2 ^ (d + 1)) := fun i => ⟨i.val, by
      have := i.isLt; rw [pow_succ]; omega⟩
    let splitR : Fin (2 ^ d) → Fin (2 ^ (d + 1)) := fun i => ⟨2 ^ d + i.val, by
      have := i.isLt; rw [pow_succ]; omega⟩
    rw [linearWeightCircuit, Circuit.eval_comp, Circuit.eval_append, Circuit.eval_comp,
      Circuit.eval_comp, Circuit.eval_wiring, Circuit.eval_wiring]
    rw [val_eval_addExactCircuit, ih (x ∘ splitL), ih (x ∘ splitR)]
    rw [BitString.weight_eq_sum_toNat, BitString.weight_eq_sum_toNat, BitString.weight_eq_sum_toNat]
    have hsplit : ∑ i : Fin (2 ^ (d + 1)), (x i).toNat =
        (∑ i : Fin (2 ^ d), (x (splitL i)).toNat) + (∑ i : Fin (2 ^ d), (x (splitR i)).toNat) := by
      have hcast : ∑ i : Fin (2 ^ (d + 1)), (x i).toNat =
          ∑ j : Fin (2 ^ d + 2 ^ d),
            (x ⟨j.val, by rw [pow_succ, mul_two]; exact j.isLt⟩).toNat :=
        Fintype.sum_equiv (finCongr (by rw [pow_succ, mul_two])) _ _ fun _ => rfl
      rw [hcast, Fin.sum_univ_add]
      rfl
    exact hsplit.symm

private theorem five_mul_add_eight_le_eight_two_pow (d : ℕ) : 5 * d + 8 ≤ 8 * 2 ^ d := by
  induction d with
  | zero => norm_num
  | succ d ih =>
    have h1 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    rw [pow_succ]
    omega

/-- Linear-size threshold circuit on `2 ^ d` bits deciding `k ≤ BitString.weight x`. -/
def linearWeightGeCircuit (d k : ℕ) : Circuit signature (2 ^ d) 1 :=
  if hk : k < 2 ^ (d + 1) then
    (leCircuit (d + 1)).comp
      ((wordConstCircuit (2 ^ d) ((BitString.equivFin (d + 1)).symm ⟨k, hk⟩)).append
        (linearWeightCircuit d))
  else Circuit.oneGate (.const false) Fin.elim0

/-- `linearWeightGeCircuit d k` decides `k ≤ BitString.weight x`. -/
theorem eval_linearWeightGeCircuit (d k : ℕ) (x : BitString (2 ^ d)) :
    (linearWeightGeCircuit d k).eval interpretation x 0 = decide (k ≤ BitString.weight x) := by
  unfold linearWeightGeCircuit
  split_ifs with hk
  · simp only [Circuit.eval_comp, Circuit.eval_append, eval_wordConstCircuit, eval_leCircuit,
      Equiv.apply_symm_apply, Fin.le_iff_val_le_val, val_eval_linearWeightCircuit]
  · have hlt : BitString.weight x < k := by
      have hle := BitString.weight_le_length x
      have hpow : 2 ^ d < 2 ^ (d + 1) := Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self d)
      omega
    simp [interpretation, hlt.not_ge]

/-- `linearWeightGeCircuit d k` has linear size at most `49 * 2 ^ d`. -/
theorem size_linearWeightGeCircuit_le (d k : ℕ) :
    (linearWeightGeCircuit d k).size ≤ 49 * 2 ^ d := by
  unfold linearWeightGeCircuit
  split_ifs with hk
  · simp only [Circuit.size_comp, Circuit.size_append, size_wordConstCircuit, size_leCircuit]
    have hw := size_linearWeightCircuit_le d
    have h5d := five_mul_add_eight_le_eight_two_pow d
    omega
  · simp only [Circuit.size_oneGate]
    have : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    omega

/-- Linear-size threshold circuit on `2 ^ d` bits deciding `BitString.weight x ≤ r`. -/
def linearWeightLeCircuit (d r : ℕ) : Circuit signature (2 ^ d) 1 :=
  if hr : r < 2 ^ (d + 1) then
    (leCircuit (d + 1)).comp
      ((linearWeightCircuit d).append
        (wordConstCircuit (2 ^ d) ((BitString.equivFin (d + 1)).symm ⟨r, hr⟩)))
  else Circuit.oneGate (.const true) Fin.elim0

/-- `linearWeightLeCircuit d r` decides `BitString.weight x ≤ r`. -/
theorem eval_linearWeightLeCircuit (d r : ℕ) (x : BitString (2 ^ d)) :
    (linearWeightLeCircuit d r).eval interpretation x 0 = decide (BitString.weight x ≤ r) := by
  unfold linearWeightLeCircuit
  split_ifs with hr
  · simp only [Circuit.eval_comp, Circuit.eval_append, eval_wordConstCircuit, eval_leCircuit,
      Equiv.apply_symm_apply, Fin.le_iff_val_le_val, val_eval_linearWeightCircuit]
  · have hle : BitString.weight x ≤ r := by
      have hw := BitString.weight_le_length x
      have hpow : 2 ^ d < 2 ^ (d + 1) := Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self d)
      omega
    simp [interpretation, hle]

/-- `linearWeightLeCircuit d r` has linear size at most `49 * 2 ^ d`. -/
theorem size_linearWeightLeCircuit_le (d r : ℕ) :
    (linearWeightLeCircuit d r).size ≤ 49 * 2 ^ d := by
  unfold linearWeightLeCircuit
  split_ifs with hr
  · simp only [Circuit.size_comp, Circuit.size_append, size_wordConstCircuit, size_leCircuit]
    have hw := size_linearWeightCircuit_le d
    have h5d := five_mul_add_eight_le_eight_two_pow d
    omega
  · simp only [Circuit.size_oneGate]
    have : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    omega

/-- Bitwise XOR with a fixed constant `center : BitString k`, using at most `k` NOT gates. -/
private def xorConstCircuit {k : ℕ} (center : BitString k) : Circuit signature k k :=
  Circuit.pi fun i =>
    if center i then Circuit.oneGate .not (fun _ => i)
    else Circuit.wiring signature (fun _ => i)

private theorem eval_xorConstCircuit {k : ℕ} (center x : BitString k) :
    (xorConstCircuit center).eval interpretation x = fun i => x i != center i := by
  funext i
  simp only [xorConstCircuit, Circuit.eval_pi]
  cases center i <;> simp [interpretation]

private theorem size_xorConstCircuit_le {k : ℕ} (center : BitString k) :
    (xorConstCircuit center).size ≤ k := by
  simp only [xorConstCircuit, Circuit.size_pi]
  calc ∑ j : Fin k,
        (if center j = true then Circuit.oneGate (σ := signature) .not (fun _ => j)
          else Circuit.wiring signature (fun _ => j)).size
      ≤ ∑ _j : Fin k, 1 := Finset.sum_le_sum fun j _ => by split_ifs <;> simp
    _ = k := by simp

/-- Linear-size Hamming-ball circuit on `2 ^ d` bits deciding `hammingDist x center ≤ r`. -/
def linearHammingBallCircuit (d : ℕ) (center : BitString (2 ^ d)) (r : ℕ) :
    Circuit signature (2 ^ d) 1 :=
  (linearWeightLeCircuit d r).comp (xorConstCircuit center)

/-- `linearHammingBallCircuit d center r` decides `hammingDist x center ≤ r`. -/
theorem eval_linearHammingBallCircuit (d : ℕ) (center : BitString (2 ^ d)) (r : ℕ)
    (x : BitString (2 ^ d)) :
    (linearHammingBallCircuit d center r).eval interpretation x 0 =
      decide (hammingDist x center ≤ r) := by
  rw [linearHammingBallCircuit, Circuit.eval_comp, eval_linearWeightLeCircuit, eval_xorConstCircuit]
  have hw : BitString.weight (fun i => x i != center i) = hammingDist x center := by
    simp only [BitString.weight, hammingDist, bne_iff_ne]
  rw [hw]

/-- `linearHammingBallCircuit d center r` has strictly linear size at most `50 * 2 ^ d`. -/
theorem size_linearHammingBallCircuit_le (d : ℕ) (center : BitString (2 ^ d)) (r : ℕ) :
    (linearHammingBallCircuit d center r).size ≤ 50 * 2 ^ d := by
  rw [linearHammingBallCircuit, Circuit.size_comp]
  have h1 := size_linearWeightLeCircuit_le d r
  have h2 := size_xorConstCircuit_le center
  omega

end CslibFrontier.Circuits.Boolean
