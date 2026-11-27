/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Classical
public import CslibFrontier.Computability.Circuit.Quantum.Reversible.Circuit
public import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin
public import CslibFrontier.Computability.Complexity.Classes.Promise.Basic
public import CslibFrontier.Computability.Complexity.Classes.QMA
public import CslibFrontier.Probability.Hellinger

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# The Complexity Class `StoqMA`

Formalizes stoquastic Merlin–Arthur (`StoqMA`) verification circuits and promise/decision
complexity classes ([Bravyi, Bessen, Terhal]):

* `CslibFrontier.Complexity.ReversibleCircuit`: classical reversible verification circuits over
  `{NOT, CNOT, Toffoli}` on `n_w` witness qubits, `n_0` ancilla `|0⟩` qubits, and `n_+` ancilla
  `|+⟩` qubits, measured in the computational (`Z`) or Hadamard (`X`, `|+⟩⟨+|`) basis on qubit `0`.
* `CslibFrontier.Complexity.ReversibleCircuit.reducedMatrix`: the symmetric entrywise non-negative
  substochastic witness matrix `M_C` governing
  `C.stoqAcceptProb w = (1/2)‖w‖² + (1/2) Re ⟨w, M_C w⟩`.
* `CslibFrontier.Complexity.ReversibleCircuit.stoqAcceptProb_le_absQubits` and
  `CslibFrontier.Complexity.ReversibleCircuit.stoqAcceptProb_ge_half_of_isNonnegState`: replacing
  any quantum witness `w` by its entrywise modulus `absQubits w` preserves `‖w‖` and never
  decreases `stoqAcceptProb`, and every non-negative unit witness achieves `stoqAcceptProb ≥ 1 / 2`.
* `CslibFrontier.Complexity.UniformReversibleVerifier`,
  `CslibFrontier.Complexity.PromiseStoqMA`, `CslibFrontier.Complexity.PromiseStoqMAClass`,
  `CslibFrontier.Complexity.PromiseStoqMA1`, and `CslibFrontier.Complexity.StoqMA`: polynomial-time
  uniform `StoqMA` complexity classes and the witness-positivity equivalence
  `CslibFrontier.Complexity.mem_PromiseStoqMA_iff_nonneg`.
-/

public section

namespace CslibFrontier.Complexity

open Finset Cslib Cslib.Quantum Cslib.Complexity Turing.MultiTapeTM

/-! ### Non-negative states, modulus states, and single-qubit Hadamard `|+⟩` measurement -/

/-- An `m`-qubit state `ψ` is **non-negative** when every computational-basis amplitude is real and
non-negative. -/
def IsNonnegState {m : ℕ} (ψ : Qubits m) : Prop :=
  ∀ i : Fin m → Bool, (ψ.ofLp i).im = 0 ∧ 0 ≤ (ψ.ofLp i).re

/-- Entrywise modulus state `|ψ⟩ = ∑_i |ψ_i| |i⟩` of an `m`-qubit vector `ψ`. -/
noncomputable def absQubits {m : ℕ} (ψ : Qubits m) : Qubits m :=
  WithLp.toLp 2 fun i ↦ (‖ψ.ofLp i‖ : ℂ)

@[simp]
theorem absQubits_ofLp {m : ℕ} (ψ : Qubits m) (i : Fin m → Bool) :
    (absQubits ψ).ofLp i = (‖ψ.ofLp i‖ : ℂ) := by
  rfl

@[simp]
theorem norm_absQubits {m : ℕ} (ψ : Qubits m) : ‖absQubits ψ‖ = ‖ψ‖ := by
  have hsq : ‖absQubits ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [absQubits_ofLp, Complex.norm_real, Real.norm_eq_abs, abs_norm]
  nlinarith [norm_nonneg (absQubits ψ), norm_nonneg ψ]

theorem isNonnegState_absQubits {m : ℕ} (ψ : Qubits m) : IsNonnegState (absQubits ψ) :=
  fun i ↦ ⟨Complex.ofReal_im _, by simp [norm_nonneg]⟩

theorem isNonnegState_ket {m : ℕ} (x : Fin m → Bool) : IsNonnegState (ket x) := fun i ↦ by
  rw [ket_apply]
  split_ifs <;> simp

theorem ofLp_eq_re_of_isNonnegState {m : ℕ} {ψ : Qubits m} (hψ : IsNonnegState ψ)
    (i : Fin m → Bool) : ψ.ofLp i = ((ψ.ofLp i).re : ℂ) := by
  apply Complex.ext
  · simp
  · simp [(hψ i).1]

theorem norm_ofLp_of_isNonnegState {m : ℕ} {ψ : Qubits m} (hψ : IsNonnegState ψ)
    (i : Fin m → Bool) : ‖ψ.ofLp i‖ = (ψ.ofLp i).re := by
  conv_lhs => rw [ofLp_eq_re_of_isNonnegState hψ i]
  rw [Complex.norm_real, Real.norm_of_nonneg (hψ i).2]

theorem absQubits_eq_self_of_isNonnegState {m : ℕ} {ψ : Qubits m} (hψ : IsNonnegState ψ) :
    absQubits ψ = ψ := by
  ext i
  rw [absQubits_ofLp, norm_ofLp_of_isNonnegState hψ i, ← ofLp_eq_re_of_isNonnegState hψ i]

/-- Uniform superposition `(1 / √|S|) ∑_{i ∈ S} |i⟩` over a finite subset `S ⊆ {0, 1}^m`. -/
noncomputable def subsetState {m : ℕ} (S : Finset (Fin m → Bool)) : Qubits m :=
  WithLp.toLp 2 fun i ↦ if i ∈ S then (((Real.sqrt S.card)⁻¹ : ℝ) : ℂ) else 0

theorem isNonnegState_subsetState {m : ℕ} (S : Finset (Fin m → Bool)) :
    IsNonnegState (subsetState S) := fun i ↦ by
  unfold subsetState
  rw [WithLp.ofLp_toLp]
  split_ifs
  · exact ⟨Complex.ofReal_im _, by rw [Complex.ofReal_re]; positivity⟩
  · simp

theorem norm_subsetState {m : ℕ} {S : Finset (Fin m → Bool)} (hS : S.Nonempty) :
    ‖subsetState S‖ = 1 := by
  have hcard : (0 : ℝ) < S.card := Nat.cast_pos.mpr hS.card_pos
  have hsq : ‖subsetState S‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ i : Fin m → Bool, ‖(subsetState S).ofLp i‖ ^ 2
        = ∑ i : Fin m → Bool, if i ∈ S then ((Real.sqrt S.card)⁻¹) ^ 2 else 0 := by
            refine sum_congr rfl fun i _ ↦ ?_
            change ‖if i ∈ S then (((Real.sqrt S.card)⁻¹ : ℝ) : ℂ) else 0‖ ^ 2 = _
            split_ifs
            · rw [Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
            · simp
      _ = S.card * ((Real.sqrt S.card)⁻¹) ^ 2 := by
            rw [← sum_filter, filter_mem_eq_inter, univ_inter, sum_const, nsmul_eq_mul]
      _ = 1 := by rw [inv_pow, Real.sq_sqrt hcard.le, mul_inv_cancel₀ hcard.ne']
  nlinarith [norm_nonneg (subsetState S)]

/-- Flip bit `0` of an `m`-bit string (`m > 0`), corresponding to `X ⊗ I_{m - 1}`. -/
def flipBit0 {m : ℕ} (hm : 0 < m) (y : Fin m → Bool) : Fin m → Bool :=
  Function.update y ⟨0, hm⟩ (!y ⟨0, hm⟩)

@[simp]
theorem flipBit0_flipBit0 {m : ℕ} (hm : 0 < m) (y : Fin m → Bool) :
    flipBit0 hm (flipBit0 hm y) = y := by
  funext i
  by_cases hi : i = ⟨0, hm⟩ <;> simp [flipBit0, hi]

/-- Split `Fin m → Bool` (`0 < m`) into output bit `0` and the remaining `m - 1` bits. -/
def splitBit0Equiv {m : ℕ} (hm : 0 < m) :
    (Bool × (Fin (m - 1) → Bool)) ≃ (Fin m → Bool) where
  toFun bu i := if _ : (i : ℕ) = 0 then bu.1 else bu.2 ⟨(i : ℕ) - 1, by have := i.2; omega⟩
  invFun y := (y ⟨0, hm⟩, fun j ↦ y ⟨(j : ℕ) + 1, by have := j.2; omega⟩)
  left_inv := fun ⟨b, u⟩ ↦ by ext <;> simp
  right_inv y := by
    funext i
    by_cases h0 : (i : ℕ) = 0
    · have hi : i = ⟨0, hm⟩ := Fin.ext h0; subst hi; simp
    · simp only [h0, ↓reduceDIte]; congr 1; ext; dsimp; omega

@[simp]
theorem flipBit0_splitBit0Equiv {m : ℕ} (hm : 0 < m) (b : Bool) (u : Fin (m - 1) → Bool) :
    flipBit0 hm (splitBit0Equiv hm (b, u)) = splitBit0Equiv hm (!b, u) := by
  funext i
  by_cases h0 : (i : ℕ) = 0
  · have hi : i = ⟨0, hm⟩ := Fin.ext h0; subst hi; simp [flipBit0, splitBit0Equiv]
  · have hne : i ≠ ⟨0, hm⟩ := fun h ↦ h0 (congrArg Fin.val h)
    simp [flipBit0, hne, splitBit0Equiv, h0]

/-- Probability `‖(|+⟩⟨+|_1 ⊗ I_{m - 1}) |ψ⟩‖_2^2` that measuring qubit `0` in the Hadamard basis
`{|+⟩, |-⟩}` yields `|+⟩`. -/
noncomputable def hadamardPlusProb {m : ℕ} (hm : 0 < m) (ψ : Qubits m) : ℝ :=
  (1 / 2 : ℝ) * ∑ u : Fin (m - 1) → Bool,
    ‖ψ.ofLp (splitBit0Equiv hm (false, u)) + ψ.ofLp (splitBit0Equiv hm (true, u))‖ ^ 2

theorem hadamardPlusProb_nonneg {m : ℕ} (hm : 0 < m) (ψ : Qubits m) :
    0 ≤ hadamardPlusProb hm ψ := by
  unfold hadamardPlusProb; positivity

theorem hadamardPlusProb_eq_half_norm_sq_add_flip {m : ℕ} (hm : 0 < m) (ψ : Qubits m) :
    hadamardPlusProb hm ψ =
      (1 / 2 : ℝ) * ‖ψ‖ ^ 2 +
        (1 / 2 : ℝ) * ∑ y : Fin m → Bool, (star (ψ.ofLp y) * ψ.ofLp (flipBit0 hm y)).re := by
  have hnorm : ‖ψ‖ ^ 2 = ∑ u : Fin (m - 1) → Bool,
      (‖ψ.ofLp (splitBit0Equiv hm (false, u))‖ ^ 2 +
        ‖ψ.ofLp (splitBit0Equiv hm (true, u))‖ ^ 2) := by
    rw [EuclideanSpace.norm_sq_eq, ← Equiv.sum_comp (splitBit0Equiv hm), Fintype.sum_prod_type,
      Fintype.sum_bool, sum_add_distrib]
    ac_rfl
  have hflip : (∑ y : Fin m → Bool, (star (ψ.ofLp y) * ψ.ofLp (flipBit0 hm y)).re) =
      ∑ u : Fin (m - 1) → Bool,
        2 * (star (ψ.ofLp (splitBit0Equiv hm (false, u))) *
          ψ.ofLp (splitBit0Equiv hm (true, u))).re := by
    rw [← Equiv.sum_comp (splitBit0Equiv hm), Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, flipBit0_splitBit0Equiv, Bool.not_false, Bool.not_true]
    rw [← sum_add_distrib]
    refine sum_congr rfl fun u _ ↦ ?_
    set a := ψ.ofLp (splitBit0Equiv hm (false, u))
    set b := ψ.ofLp (splitBit0Equiv hm (true, u))
    have hconj : (star b * a).re = (star a * b).re := by
      have : star (star a * b) = star b * a := by simp [mul_comm]
      rw [← this]
      exact (Complex.conj_re _).symm
    linarith
  rw [hadamardPlusProb, hnorm, hflip, ← mul_add, ← sum_add_distrib]
  congr 1
  refine sum_congr rfl fun u _ ↦ ?_
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, RCLike.star_def, Complex.conj_re, Complex.conj_im]
  ring

theorem hadamardPlusProb_le_norm_sq {m : ℕ} (hm : 0 < m) (ψ : Qubits m) :
    hadamardPlusProb hm ψ ≤ ‖ψ‖ ^ 2 := by
  rw [hadamardPlusProb, EuclideanSpace.norm_sq_eq, ← Equiv.sum_comp (splitBit0Equiv hm),
    Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  rw [← sum_add_distrib, mul_sum]
  refine sum_le_sum fun u _ ↦ ?_
  set a := ψ.ofLp (splitBit0Equiv hm (false, u))
  set b := ψ.ofLp (splitBit0Equiv hm (true, u))
  have hpar : ‖a + b‖ ^ 2 + ‖a - b‖ ^ 2 = 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im]
    ring
  have hnn : 0 ≤ ‖a - b‖ ^ 2 := sq_nonneg _
  linarith

/-! ### Reversible verification circuits and stoquastic witness matrix -/

/-- A classical reversible verification circuit over `{NOT, CNOT, Toffoli}` acting on
`witnessQubits` witness wires, `zeroQubits` ancilla `|0⟩` wires, and `plusQubits` ancilla `|+⟩`
wires. -/
@[ext]
structure ReversibleCircuit where
  /-- Number `n_w` of witness qubits. -/
  witnessQubits : ℕ
  /-- Number `n_0` of `|0⟩` ancilla qubits. -/
  zeroQubits : ℕ
  /-- Number `n_+` of `|+⟩` ancilla qubits. -/
  plusQubits : ℕ
  /-- Classical reversible gate sequence (`NOT`, `CNOT`, `Toffoli`). -/
  gates : List GateCode
  /-- At least one qubit is present so output qubit `0` exists. -/
  totalQubits_pos : 0 < witnessQubits + zeroQubits + plusQubits
  /-- Every gate is a well-formed classical reversible gate on the total register. -/
  isClassical : GateCode.IsClassical (witnessQubits + zeroQubits + plusQubits) gates

namespace ReversibleCircuit

/-- Total number `n = n_w + n_0 + n_+` of qubits in `C`. -/
abbrev totalQubits (C : ReversibleCircuit) : ℕ :=
  C.witnessQubits + C.zeroQubits + C.plusQubits

/-- Equivalence splitting the `n`-qubit register into `(witness, zeroAncilla, plusAncilla)`. -/
def registerEquiv (C : ReversibleCircuit) :
    ((Fin C.witnessQubits → Bool) × (Fin C.zeroQubits → Bool) × (Fin C.plusQubits → Bool)) ≃
      (Fin C.totalQubits → Bool) where
  toFun p i :=
    if h1 : (i : ℕ) < C.witnessQubits then
      p.1 ⟨i, h1⟩
    else if h2 : (i : ℕ) < C.witnessQubits + C.zeroQubits then
      p.2.1 ⟨(i : ℕ) - C.witnessQubits, by omega⟩
    else
      p.2.2 ⟨(i : ℕ) - (C.witnessQubits + C.zeroQubits), by
        have hi : (i : ℕ) < C.witnessQubits + C.zeroQubits + C.plusQubits := i.2; omega⟩
  invFun y :=
    (fun i ↦ y ⟨i, by have hi := i.2; dsimp [totalQubits]; omega⟩,
     fun j ↦ y ⟨C.witnessQubits + j, by have hj := j.2; dsimp [totalQubits]; omega⟩,
     fun k ↦ y ⟨C.witnessQubits + C.zeroQubits + k, by
       have hk := k.2; dsimp [totalQubits]; omega⟩)
  left_inv := fun ⟨s, z, r⟩ ↦ by
    refine Prod.ext (funext fun i ↦ ?_) (Prod.ext (funext fun j ↦ ?_) (funext fun k ↦ ?_))
    · simp [i.2]
    · dsimp; split_ifs with h1 h2
      · omega
      · congr 1; ext; dsimp; omega
      · omega
    · dsimp; split_ifs with h1 h2
      · omega
      · omega
      · congr 1; ext; dsimp; omega
  right_inv y := by
    funext i; dsimp; split_ifs with h1 h2
    · rfl
    · congr 1; ext; dsimp; omega
    · congr 1; ext; dsimp; omega

/-- Classical permutation `π_C` computed by `C` on `{0, 1}^n`. -/
def perm (C : ReversibleCircuit) : Equiv.Perm (Fin C.totalQubits → Bool) where
  toFun := GateCode.classicalRun C.gates
  invFun := GateCode.classicalUnrun C.gates
  left_inv := GateCode.classicalUnrun_classicalRun C.isClassical
  right_inv := GateCode.classicalRun_classicalUnrun C.isClassical

/-- Initial `n`-qubit state `|w⟩ ⊗ |0⟩^{⊗ n_0} ⊗ |+⟩^{⊗ n_+}` of `C` on witness `w`. -/
noncomputable def initialState (C : ReversibleCircuit)
    (w : Qubits C.witnessQubits) : Qubits C.totalQubits :=
  WithLp.toLp 2 fun y ↦
    let szr := C.registerEquiv.symm y
    if szr.2.1 = fun _ ↦ false then
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ C.plusQubits * w.ofLp szr.1
    else 0

theorem initialState_ofLp_registerEquiv (C : ReversibleCircuit)
    (w : Qubits C.witnessQubits)
    (s : Fin C.witnessQubits → Bool) (z : Fin C.zeroQubits → Bool)
    (r : Fin C.plusQubits → Bool) :
    (C.initialState w).ofLp (C.registerEquiv (s, z, r)) =
      if z = fun _ ↦ false then
        (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ C.plusQubits * w.ofLp s
      else 0 := by
  change (if (C.registerEquiv.symm (C.registerEquiv (s, z, r))).2.1 = fun _ ↦ false
    then _ else 0) = _
  rw [Equiv.symm_apply_apply]

@[simp]
theorem norm_initialState (C : ReversibleCircuit) (w : Qubits C.witnessQubits) :
    ‖C.initialState w‖ = ‖w‖ := by
  have hsq : ‖C.initialState w‖ ^ 2 = ‖w‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, ← Equiv.sum_comp C.registerEquiv, Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type, initialState_ofLp_registerEquiv]
    have hhalf : ‖(((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ C.plusQubits‖ ^ 2 =
        ((1 / 2 : ℝ) ^ C.plusQubits) := by
      rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)),
        ← pow_mul, mul_comm, pow_mul, inv_pow, Real.sq_sqrt (by norm_num), one_div]
    calc ∑ s : Fin C.witnessQubits → Bool, ∑ z : Fin C.zeroQubits → Bool,
          ∑ r : Fin C.plusQubits → Bool,
            ‖if z = fun _ ↦ false then
              (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ C.plusQubits * w.ofLp s else 0‖ ^ 2
        = ∑ s : Fin C.witnessQubits → Bool,
            ∑ r : Fin C.plusQubits → Bool,
              ((1 / 2 : ℝ) ^ C.plusQubits * ‖w.ofLp s‖ ^ 2) := by
            refine sum_congr rfl fun s _ ↦ ?_
            rw [sum_eq_single (fun _ : Fin C.zeroQubits ↦ false)
              (fun z _ hz ↦ by simp [hz]) (fun h ↦ absurd (mem_univ _) h)]
            refine sum_congr rfl fun r _ ↦ ?_
            rw [ite_eq_left rfl, norm_mul, mul_pow, hhalf]
      _ = ∑ s : Fin C.witnessQubits → Bool, ‖w.ofLp s‖ ^ 2 := by
            refine sum_congr rfl fun s _ ↦ ?_
            rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
              nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
            have hcancel : (2 : ℝ) ^ C.plusQubits * (1 / 2 : ℝ) ^ C.plusQubits = 1 := by
              rw [← mul_pow]; norm_num
            calc (2 : ℝ) ^ C.plusQubits * ((1 / 2 : ℝ) ^ C.plusQubits * ‖w.ofLp s‖ ^ 2)
                = ((2 : ℝ) ^ C.plusQubits * (1 / 2 : ℝ) ^ C.plusQubits) * ‖w.ofLp s‖ ^ 2 := by
                    ring
              _ = ‖w.ofLp s‖ ^ 2 := by rw [hcancel, one_mul]
      _ = ‖w‖ ^ 2 := (EuclideanSpace.norm_sq_eq w).symm
  nlinarith [norm_nonneg (C.initialState w), norm_nonneg w]

/-- State `|R⟩ = C (|w⟩ ⊗ |0⟩^{⊗ n_0} ⊗ |+⟩^{⊗ n_+})` immediately before measurement. -/
noncomputable def finalState (C : ReversibleCircuit)
    (w : Qubits C.witnessQubits) : Qubits C.totalQubits :=
  Circuit.eval (Circuit.ofCodes C.totalQubits C.gates) (C.initialState w)

theorem finalState_ofLp (C : ReversibleCircuit) (w : Qubits C.witnessQubits)
    (y : Fin C.totalQubits → Bool) :
    (C.finalState w).ofLp y = (C.initialState w).ofLp (GateCode.classicalUnrun C.gates y) :=
  Circuit.eval_ofCodes_apply C.isClassical (C.initialState w) y

@[simp]
theorem norm_finalState (C : ReversibleCircuit) (w : Qubits C.witnessQubits) :
    ‖C.finalState w‖ = ‖w‖ := by
  rw [finalState, Circuit.norm_eval, norm_initialState]

/-- Computational-basis (`|0⟩⟨0|_1`) acceptance probability of `C` on witness `w`. -/
noncomputable def compAcceptProb (C : ReversibleCircuit) (w : Qubits C.witnessQubits) : ℝ :=
  measureProb (C.finalState w) (univ.filter fun y : Fin C.totalQubits → Bool ↦
    y ⟨0, C.totalQubits_pos⟩ = false)

/-- Hadamard-basis (`|+⟩⟨+|_1`) stoquastic acceptance probability of `C` on witness `w`. -/
noncomputable def stoqAcceptProb (C : ReversibleCircuit) (w : Qubits C.witnessQubits) : ℝ :=
  hadamardPlusProb C.totalQubits_pos (C.finalState w)

theorem stoqAcceptProb_nonneg (C : ReversibleCircuit) (w : Qubits C.witnessQubits) :
    0 ≤ C.stoqAcceptProb w :=
  hadamardPlusProb_nonneg C.totalQubits_pos (C.finalState w)

theorem stoqAcceptProb_le_norm_sq (C : ReversibleCircuit) (w : Qubits C.witnessQubits) :
    C.stoqAcceptProb w ≤ ‖w‖ ^ 2 :=
  (hadamardPlusProb_le_norm_sq C.totalQubits_pos (C.finalState w)).trans_eq
    (by rw [norm_finalState])

/-- Classical involution `σ_C = C⁻¹ ∘ X_0 ∘ C` on `{0, 1}^n`. -/
def reflectedPerm (C : ReversibleCircuit) (x : Fin C.totalQubits → Bool) :
    Fin C.totalQubits → Bool :=
  GateCode.classicalUnrun C.gates (flipBit0 C.totalQubits_pos (GateCode.classicalRun C.gates x))

theorem reflectedPerm_involutive (C : ReversibleCircuit) :
    Function.Involutive C.reflectedPerm := fun x ↦ by
  unfold reflectedPerm
  rw [GateCode.classicalRun_classicalUnrun C.isClassical, flipBit0_flipBit0,
    GateCode.classicalUnrun_classicalRun C.isClassical]

/-- Symmetric non-negative substochastic reduced witness matrix
`M_C = ⟨0^{n_0}|⟨+^{n_+}| C† (X_0 ⊗ I) C |0^{n_0}⟩|+^{n_+}⟩`. -/
noncomputable def reducedMatrix (C : ReversibleCircuit) :
    Matrix (Fin C.witnessQubits → Bool) (Fin C.witnessQubits → Bool) ℝ :=
  fun s s' ↦
    ((univ.filter fun r : Fin C.plusQubits → Bool ↦
      let y := C.registerEquiv.symm (C.reflectedPerm (C.registerEquiv (s, (fun _ ↦ false), r)))
      y.1 = s' ∧ y.2.1 = fun _ ↦ false).card : ℝ) / 2 ^ C.plusQubits

theorem reducedMatrix_nonneg (C : ReversibleCircuit)
    (s s' : Fin C.witnessQubits → Bool) : 0 ≤ C.reducedMatrix s s' := by
  unfold reducedMatrix; positivity

theorem isSymm_reducedMatrix (C : ReversibleCircuit) : C.reducedMatrix.IsSymm := by
  ext s' s
  simp only [Matrix.transpose_apply, reducedMatrix]
  congr 2
  refine card_nbij'
    (fun r ↦ (C.registerEquiv.symm
      (C.reflectedPerm (C.registerEquiv (s, (fun _ ↦ false), r)))).2.2)
    (fun r' ↦ (C.registerEquiv.symm
      (C.reflectedPerm (C.registerEquiv (s', (fun _ ↦ false), r')))).2.2)
    (fun r hr ↦ ?_) (fun r' hr' ↦ ?_) (fun r hr ↦ ?_) (fun r' hr' ↦ ?_)
  · simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at hr ⊢
    set u := C.registerEquiv.symm (C.reflectedPerm (C.registerEquiv (s, (fun _ ↦ false), r)))
    have hu : C.registerEquiv (s', (fun _ ↦ false), u.2.2) =
        C.reflectedPerm (C.registerEquiv (s, (fun _ ↦ false), r)) := by
      conv_lhs => rw [← hr.1, ← hr.2]
      exact C.registerEquiv.apply_symm_apply _
    rw [hu, C.reflectedPerm_involutive, Equiv.symm_apply_apply]
    exact ⟨rfl, rfl⟩
  · simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at hr' ⊢
    set u := C.registerEquiv.symm (C.reflectedPerm (C.registerEquiv (s', (fun _ ↦ false), r')))
    have hu : C.registerEquiv (s, (fun _ ↦ false), u.2.2) =
        C.reflectedPerm (C.registerEquiv (s', (fun _ ↦ false), r')) := by
      conv_lhs => rw [← hr'.1, ← hr'.2]
      exact C.registerEquiv.apply_symm_apply _
    rw [hu, C.reflectedPerm_involutive, Equiv.symm_apply_apply]
    exact ⟨rfl, rfl⟩
  · simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at hr
    set u := C.registerEquiv.symm (C.reflectedPerm (C.registerEquiv (s, (fun _ ↦ false), r)))
    have hu : C.registerEquiv (s', (fun _ ↦ false), u.2.2) =
        C.reflectedPerm (C.registerEquiv (s, (fun _ ↦ false), r)) := by
      conv_lhs => rw [← hr.1, ← hr.2]
      exact C.registerEquiv.apply_symm_apply _
    dsimp only
    rw [hu, C.reflectedPerm_involutive, Equiv.symm_apply_apply]
  · simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at hr'
    set u := C.registerEquiv.symm (C.reflectedPerm (C.registerEquiv (s', (fun _ ↦ false), r')))
    have hu : C.registerEquiv (s, (fun _ ↦ false), u.2.2) =
        C.reflectedPerm (C.registerEquiv (s', (fun _ ↦ false), r')) := by
      conv_lhs => rw [← hr'.1, ← hr'.2]
      exact C.registerEquiv.apply_symm_apply _
    dsimp only
    rw [hu, C.reflectedPerm_involutive, Equiv.symm_apply_apply]

theorem reducedMatrix_rowSum_le_one (C : ReversibleCircuit)
    (s : Fin C.witnessQubits → Bool) : ∑ s', C.reducedMatrix s s' ≤ 1 := by
  unfold reducedMatrix
  rw [← sum_div, div_le_one (by positivity)]
  norm_cast
  calc ∑ s' : Fin C.witnessQubits → Bool,
        (univ.filter fun r : Fin C.plusQubits → Bool ↦
          let y := C.registerEquiv.symm (C.reflectedPerm (C.registerEquiv (s, (fun _ ↦ false), r)))
          y.1 = s' ∧ y.2.1 = fun _ ↦ false).card
      = (univ.biUnion fun s' : Fin C.witnessQubits → Bool ↦
          univ.filter fun r : Fin C.plusQubits → Bool ↦
            let y := C.registerEquiv.symm
              (C.reflectedPerm (C.registerEquiv (s, (fun _ ↦ false), r)))
            y.1 = s' ∧ y.2.1 = fun _ ↦ false).card := by
          refine (card_biUnion fun s₁ _ s₂ _ hne ↦ ?_).symm
          dsimp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro r hr1 hr2
          simp only [mem_filter, mem_univ, true_and] at hr1 hr2
          exact hne (hr1.1.symm.trans hr2.1)
    _ ≤ (univ : Finset (Fin C.plusQubits → Bool)).card := card_le_card (subset_univ _)
    _ = 2 ^ C.plusQubits := by simp

/-- Explicit real quadratic-form expansion of `stoqAcceptProb` in terms of `reducedMatrix`. -/
theorem stoqAcceptProb_eq_sum_reducedMatrix (C : ReversibleCircuit) (w : Qubits C.witnessQubits) :
    C.stoqAcceptProb w =
      (1 / 2 : ℝ) * ‖w‖ ^ 2 +
        (1 / 2 : ℝ) * ∑ s : Fin C.witnessQubits → Bool, ∑ s' : Fin C.witnessQubits → Bool,
          C.reducedMatrix s s' * (star (w.ofLp s) * w.ofLp s').re := by
  rw [stoqAcceptProb, hadamardPlusProb_eq_half_norm_sq_add_flip, norm_finalState]
  congr 2
  let e := C.registerEquiv.trans C.perm
  rw [← Equiv.sum_comp e, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  have hsq : (((Real.sqrt 2)⁻¹ : ℝ) ^ C.plusQubits) ^ 2 = (1 / (2 ^ C.plusQubits : ℝ)) := by
    rw [← pow_mul, mul_comm, pow_mul, inv_pow, Real.sq_sqrt (by norm_num), inv_pow, one_div]
  refine sum_congr rfl fun s _ ↦ ?_
  have hleft (z : Fin C.zeroQubits → Bool) (r : Fin C.plusQubits → Bool) :
      (C.finalState w).ofLp (e (s, z, r)) =
        if z = fun _ ↦ false then
          (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ C.plusQubits * w.ofLp s
        else 0 := by
    rw [finalState_ofLp]
    change (C.initialState w).ofLp
      (GateCode.classicalUnrun C.gates
        (GateCode.classicalRun C.gates (C.registerEquiv (s, z, r)))) = _
    rw [GateCode.classicalUnrun_classicalRun C.isClassical, initialState_ofLp_registerEquiv]
  have hright (r : Fin C.plusQubits → Bool) :
      (C.finalState w).ofLp (flipBit0 C.totalQubits_pos (e (s, (fun _ ↦ false), r))) =
        let y := C.registerEquiv.symm (C.reflectedPerm (C.registerEquiv (s, (fun _ ↦ false), r)))
        if y.2.1 = fun _ ↦ false then
          (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ C.plusQubits * w.ofLp y.1
        else 0 := by
    rw [finalState_ofLp]
    change (C.initialState w).ofLp
      (C.reflectedPerm (C.registerEquiv (s, (fun _ ↦ false), r))) = _
    conv_lhs =>
      rw [← C.registerEquiv.apply_symm_apply
        (C.reflectedPerm (C.registerEquiv (s, (fun _ ↦ false), r))),
        initialState_ofLp_registerEquiv]
  rw [sum_eq_single (fun _ : Fin C.zeroQubits ↦ false)
    (fun z _ hz ↦ sum_eq_zero fun r _ ↦ by rw [hleft z r, ite_eq_right hz]; simp)
    (fun h ↦ absurd (mem_univ _) h)]
  calc ∑ r : Fin C.plusQubits → Bool,
        (star ((C.finalState w).ofLp (e (s, (fun _ ↦ false), r))) *
          (C.finalState w).ofLp (flipBit0 C.totalQubits_pos (e (s, (fun _ ↦ false), r)))).re
      = ∑ r : Fin C.plusQubits → Bool,
          let y := C.registerEquiv.symm (C.reflectedPerm (C.registerEquiv (s, (fun _ ↦ false), r)))
          if y.2.1 = fun _ ↦ false then
            (1 / (2 ^ C.plusQubits : ℝ)) * (star (w.ofLp s) * w.ofLp y.1).re
          else 0 := by
          refine sum_congr rfl fun r _ ↦ ?_
          rw [hleft (fun _ ↦ false) r, ite_eq_left rfl, hright r]
          dsimp only
          split_ifs
          · have hmul :
                star ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ C.plusQubits * w.ofLp s) *
                  ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ C.plusQubits *
                    w.ofLp (C.registerEquiv.symm
                      (C.reflectedPerm (C.registerEquiv (s, (fun _ ↦ false), r)))).1) =
                ((((Real.sqrt 2)⁻¹ : ℝ) ^ C.plusQubits) ^ 2 : ℝ) *
                  (star (w.ofLp s) *
                    w.ofLp (C.registerEquiv.symm
                      (C.reflectedPerm (C.registerEquiv (s, (fun _ ↦ false), r)))).1) := by
              simp only [map_mul, map_pow, RCLike.star_def, Complex.conj_ofReal,
                Complex.ofReal_pow]
              ring
            rw [hmul, Complex.re_ofReal_mul, hsq]
          · simp
    _ = ∑ s' : Fin C.witnessQubits → Bool,
          C.reducedMatrix s s' * (star (w.ofLp s) * w.ofLp s').re := by
          unfold reducedMatrix
          conv_rhs =>
            arg 2; ext s'
            rw [div_mul_eq_mul_div, ← nsmul_eq_mul, ← sum_const, sum_filter, sum_div]
          rw [sum_comm]
          refine sum_congr rfl fun r _ ↦ ?_
          set y := C.registerEquiv.symm
            (C.reflectedPerm (C.registerEquiv (s, (fun _ ↦ false), r)))
          rw [sum_eq_single y.1 (fun s' _ hs' ↦ by simp [hs'.symm])
            (fun h ↦ absurd (mem_univ y.1) h)]
          dsimp only
          by_cases hy : y.2.1 = fun _ ↦ false
          · rw [ite_eq_left hy, ite_eq_left ⟨rfl, hy⟩]; ring
          · rw [ite_eq_right hy, ite_eq_right (fun h ↦ hy h.2), zero_div]

/-- Replacing any quantum witness `w` by its entrywise modulus `absQubits w` never decreases
`stoqAcceptProb`. -/
theorem stoqAcceptProb_le_absQubits (C : ReversibleCircuit) (w : Qubits C.witnessQubits) :
    C.stoqAcceptProb w ≤ C.stoqAcceptProb (absQubits w) := by
  rw [stoqAcceptProb_eq_sum_reducedMatrix, stoqAcceptProb_eq_sum_reducedMatrix, norm_absQubits]
  refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  refine sum_le_sum fun s _ ↦ sum_le_sum fun s' _ ↦ ?_
  refine mul_le_mul_of_nonneg_left ?_ (C.reducedMatrix_nonneg s s')
  simp only [absQubits_ofLp, RCLike.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
    Complex.ofReal_re]
  calc (starRingEnd ℂ (w.ofLp s) * w.ofLp s').re
      ≤ ‖starRingEnd ℂ (w.ofLp s) * w.ofLp s'‖ := Complex.re_le_norm _
    _ = ‖w.ofLp s‖ * ‖w.ofLp s'‖ := by rw [norm_mul, Complex.norm_conj]

/-- Every non-negative unit witness `w` has `C.stoqAcceptProb w ≥ 1 / 2`. -/
theorem stoqAcceptProb_ge_half_of_isNonnegState (C : ReversibleCircuit)
    {w : Qubits C.witnessQubits} (hunit : ‖w‖ = 1) (hnn : IsNonnegState w) :
    (1 / 2 : ℝ) ≤ C.stoqAcceptProb w := by
  rw [← absQubits_eq_self_of_isNonnegState hnn, stoqAcceptProb_eq_sum_reducedMatrix,
    norm_absQubits, hunit, one_pow, mul_one]
  have hsum_nn : 0 ≤ ∑ s : Fin C.witnessQubits → Bool, ∑ s' : Fin C.witnessQubits → Bool,
      C.reducedMatrix s s' * (star ((absQubits w).ofLp s) * (absQubits w).ofLp s').re := by
    refine sum_nonneg fun s _ ↦ sum_nonneg fun s' _ ↦ mul_nonneg (C.reducedMatrix_nonneg s s') ?_
    simp only [absQubits_ofLp, RCLike.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Complex.ofReal_re]
    positivity
  linarith

end ReversibleCircuit

/-! ### Uniform reversible verifiers and `StoqMA` complexity classes -/

/-- A polynomial-time uniformly generated family `a ↦ V_a` of classical reversible verification
circuits with respect to instance encoding `enc : α ↪ List Bool`. -/
@[ext]
structure UniformReversibleVerifier {α : Type} (enc : α ↪ List Bool) where
  /-- Verification circuit `V_a` associated with instance `a : α`. -/
  circuit : α → ReversibleCircuit
  /-- Polynomial-time computability of `n_w(a)` in unary. -/
  computableInPolyTime_witnessQubits :
    ComputableInPolyTime (fun a ↦ (circuit a).witnessQubits) enc encUnary
  /-- Polynomial-time computability of `n_0(a)` in unary. -/
  computableInPolyTime_zeroQubits :
    ComputableInPolyTime (fun a ↦ (circuit a).zeroQubits) enc encUnary
  /-- Polynomial-time computability of `n_+(a)` in unary. -/
  computableInPolyTime_plusQubits :
    ComputableInPolyTime (fun a ↦ (circuit a).plusQubits) enc encUnary
  /-- Polynomial-time computability of the gate list `V_a` in `encList encGateCode`. -/
  computableInPolyTime_gates :
    ComputableInPolyTime (fun a ↦ (circuit a).gates) enc (encList encGateCode)

/-- Admissible completeness and soundness thresholds `(a, b)` for `StoqMA(a, b)`:
`1 / 2 ≤ b(n) < a(n) ≤ 1` with inverse-polynomial gap `a(n) - b(n) ≥ 1 / (p(n) + 1)`. -/
def ValidStoqMAParams (a b : ℕ → ℝ) : Prop :=
  (∀ n : ℕ, 1 / 2 ≤ b n ∧ b n < a n ∧ a n ≤ 1) ∧
    ∃ p : Polynomial ℕ, ∀ n : ℕ, (1 : ℝ) / (((p.eval n : ℕ) : ℝ) + 1) ≤ a n - b n

/-- **`StoqMA(a, b)`** for promise problems: decided by a polynomial-time uniform family of
reversible verification circuits with non-negative unit witnesses on `yes` instances, arbitrary
unit witnesses on `no` instances, and a Hadamard-basis `|+⟩` measurement on output qubit `0`. -/
def PromiseStoqMA {α : Type} (a b : ℕ → ℝ) (enc : α ↪ List Bool) : Set (PromiseProblem α) :=
  {Q | ∃ V : UniformReversibleVerifier enc,
    ∀ x,
      (x ∈ Q.yes → ∃ w : Qubits (V.circuit x).witnessQubits,
        ‖w‖ = 1 ∧ IsNonnegState w ∧ a (enc x).length ≤ (V.circuit x).stoqAcceptProb w) ∧
      (x ∈ Q.no → ∀ w : Qubits (V.circuit x).witnessQubits,
        ‖w‖ = 1 → (V.circuit x).stoqAcceptProb w ≤ b (enc x).length)}

theorem PromiseStoqMA_mono {α : Type} {enc : α ↪ List Bool} {a a' b b' : ℕ → ℝ}
    (ha : ∀ n, a' n ≤ a n) (hb : ∀ n, b n ≤ b' n) :
    PromiseStoqMA a b enc ⊆ PromiseStoqMA a' b' enc := by
  rintro Q ⟨V, hV⟩
  refine ⟨V, fun x ↦ ⟨fun hx ↦ ?_, fun hx w hw ↦ ((hV x).2 hx w hw).trans (hb _)⟩⟩
  obtain ⟨w, hw, hnn, h⟩ := (hV x).1 hx
  exact ⟨w, hw, hnn, (ha _).trans h⟩

/-- Requiring a non-negative witness on `yes` instances and soundness against all complex unit
witnesses on `no` instances is equivalent to allowing arbitrary complex unit witnesses on `yes`
instances and requiring soundness only against non-negative unit witnesses on `no` instances. -/
theorem mem_PromiseStoqMA_iff_nonneg {α : Type} {enc : α ↪ List Bool} {a b : ℕ → ℝ}
    {Q : PromiseProblem α} :
    Q ∈ PromiseStoqMA a b enc ↔
      ∃ V : UniformReversibleVerifier enc,
        ∀ x,
          (x ∈ Q.yes → ∃ w : Qubits (V.circuit x).witnessQubits,
            ‖w‖ = 1 ∧ a (enc x).length ≤ (V.circuit x).stoqAcceptProb w) ∧
          (x ∈ Q.no → ∀ w : Qubits (V.circuit x).witnessQubits,
            ‖w‖ = 1 → IsNonnegState w → (V.circuit x).stoqAcceptProb w ≤ b (enc x).length) := by
  constructor
  · rintro ⟨V, hV⟩
    refine ⟨V, fun x ↦ ⟨fun hx ↦ ?_, fun hx w hw _ ↦ (hV x).2 hx w hw⟩⟩
    obtain ⟨w, hw, _, h⟩ := (hV x).1 hx
    exact ⟨w, hw, h⟩
  · rintro ⟨V, hV⟩
    refine ⟨V, fun x ↦ ⟨fun hx ↦ ?_, fun hx w hw ↦ ?_⟩⟩
    · obtain ⟨w, hw, h⟩ := (hV x).1 hx
      exact ⟨absQubits w, by rw [norm_absQubits, hw],
        isNonnegState_absQubits w, h.trans ((V.circuit x).stoqAcceptProb_le_absQubits w)⟩
    · exact ((V.circuit x).stoqAcceptProb_le_absQubits w).trans
        ((hV x).2 hx (absQubits w) (by rw [norm_absQubits, hw]) (isNonnegState_absQubits w))

/-- Unparameterized **`PromiseStoqMA`**: union of `PromiseStoqMA a b` over all admissible
inverse-polynomial-gap parameters `(a, b)`. -/
def PromiseStoqMAClass {α : Type} (enc : α ↪ List Bool) : Set (PromiseProblem α) :=
  {Q | ∃ a b : ℕ → ℝ, ValidStoqMAParams a b ∧ Q ∈ PromiseStoqMA a b enc}

/-- **`StoqMA₁`** (`StoqMA` with perfect completeness `a = 1`). -/
def PromiseStoqMA1 {α : Type} (enc : α ↪ List Bool) : Set (PromiseProblem α) :=
  {Q | ∃ b : ℕ → ℝ, ValidStoqMAParams (fun _ ↦ 1) b ∧ Q ∈ PromiseStoqMA (fun _ ↦ 1) b enc}

/-- **`StoqMA`** for decision problems (`Set α`), with respect to instance encoding `enc`. -/
def StoqMA {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | PromiseProblem.ofSet A ∈ PromiseStoqMAClass enc}

/-- Soundness floor of `StoqMA`: if `b(n) < 1 / 2` for all `n`, every `Q ∈ PromiseStoqMA a b enc`
has `Q.no = ∅`. -/
theorem stoqma_no_empty_of_soundness_lt_half {α : Type} {enc : α ↪ List Bool}
    {a b : ℕ → ℝ} (hb : ∀ n, b n < 1 / 2) {Q : PromiseProblem α}
    (hQ : Q ∈ PromiseStoqMA a b enc) : Q.no = ∅ := by
  obtain ⟨V, hV⟩ := hQ
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  let s0 : Fin (V.circuit x).witnessQubits → Bool := fun _ ↦ false
  let w0 : Qubits (V.circuit x).witnessQubits := ket s0
  have hge := (V.circuit x).stoqAcceptProb_ge_half_of_isNonnegState
    (norm_ket s0) (isNonnegState_ket s0)
  have hle := (hV x).2 hx w0 (norm_ket s0)
  linarith [hb (enc x).length]

end CslibFrontier.Complexity
