/-
Copyright (c) 2026 FormalPapers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Communication.Functions
public import CslibFrontier.Foundations.Quantum.DensityMatrix.Holevo
public import CslibFrontier.Foundations.Quantum.POVM.Density
public import CslibFrontier.Probability.Entropy.Fano
public import CslibFrontier.Probability.MutualInformation
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Uniform

/-!
# Quantum Random Access Codes and One-Way Quantum Communication Lower Bounds

A quantum random access code (QRAC) encodes an `n`-bit string `y` into a quantum state `ρ y` on a
finite-dimensional Hilbert space `ℂ^ι` so that any chosen bit `y i` can be recovered with bounded
error `ε` by an index-dependent binary POVM `M i`.

Combining the chain rule for Holevo information across uniform product coordinates with Holevo's
accessible-information bound and Fano's inequality yields the fundamental dimension bound
`(1 - h₂(ε)) n ≤ log₂ |ι|`, where `h₂(ε) = Real.binEntropy ε / Real.log 2` is the binary Shannon
entropy in bits. Restricting Alice's inputs in Set Disjointness to singleton indicator strings
immediately gives the corresponding linear lower bound `(1 - h₂(ε)) n ≤ log₂ |ι|` on the qubit
cost of one-way quantum communication protocols for Set Disjointness.

## Main definitions

* `CslibFrontier.Computability.Communication.binaryEntropyBits`: binary Shannon entropy in bits.
* `CslibFrontier.Computability.Communication.OneWayQuantumProtocol`: one-way quantum communication
  protocols with density-matrix messages on `ℂ^ι` and POVM readouts.

## Main results

* `CslibFrontier.Computability.Communication.binEntropy_mono_on_half`: monotonicity of
  `Real.binEntropy` on `[0, 1 / 2]`.
* `CslibFrontier.Computability.Communication.qrac_qubit_lower_bound`: any `(n, log₂ |ι|, 1 - ε)`
  quantum random access code with `0 ≤ ε ≤ 1 / 2` satisfies
  `(1 - binaryEntropyBits ε) * n ≤ log₂ |ι|`.
* `CslibFrontier.Computability.Communication.oneWay_disjointness_qubit_lower_bound`: any one-way
  quantum communication protocol solving `Cslib.Communication.disjointness` on `n`-bit strings with
  worst-case error `ε ∈ [0, 1 / 2]` transmits at least `(1 - binaryEntropyBits ε) * n` qubits
  (`n / 24` qubits at `ε = 1 / 3`).
-/

public section

open Finset Matrix
open Cslib.Probability.PMF
open scoped ENNReal

namespace CslibFrontier.Computability.Communication

/-- Binary Shannon entropy in bits `h₂(p) = Real.binEntropy p / Real.log 2`. -/
noncomputable def binaryEntropyBits (p : ℝ) : ℝ :=
  Real.binEntropy p / Real.log 2

/-- `Real.binEntropy` is monotone nondecreasing on `[0, 1 / 2]`. -/
theorem binEntropy_mono_on_half {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1 / 2) :
    Real.binEntropy a ≤ Real.binEntropy b := by
  rcases eq_or_lt_of_le (hab.trans hb) with ha_eq | ha_lt
  · have : a = b := by linarith
    rw [this]
  · have hden : 0 < 1 - 2 * a := by linarith
    set t : ℝ := (b - a) / (1 - 2 * a)
    have ht0 : 0 ≤ t := div_nonneg (by linarith) hden.le
    have ht1 : 0 ≤ 1 - t := sub_nonneg.mpr ((div_le_one hden).mpr (by linarith))
    have hconv : (1 - t) * a + t * (1 - a) = b := by
      calc
        (1 - t) * a + t * (1 - a) = a + t * (1 - 2 * a) := by ring
        _ = a + (b - a) := by rw [div_mul_cancel₀ _ hden.ne']
        _ = b := by ring
    have ha_mem : a ∈ Set.Icc (0 : ℝ) 1 := ⟨ha0, by linarith⟩
    have h1a_mem : 1 - a ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hconc := Real.strictConcave_binEntropy.concaveOn.2 ha_mem h1a_mem ht1 ht0 (by ring)
    simp only [smul_eq_mul, hconv, Real.binEntropy_one_sub] at hconc
    linarith

private theorem densityProb_sum_smul {ι Z : Type*} [Fintype ι] [DecidableEq ι] [Fintype Z]
    {α : Type*} (s : Finset α) (M : Cslib.Quantum.POVM Z ι) (w : α → ℝ)
    (σ : α → Matrix ι ι ℂ) (z : Z) :
    M.densityProb (∑ a ∈ s, w a • σ a) z = ∑ a ∈ s, w a * M.densityProb (σ a) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := M.densityProb_smul 0 0 z
    simp only [zero_smul, zero_mul] at this
    simpa only [sum_empty] using this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, M.densityProb_add, M.densityProb_smul, ih]

private theorem isDensityMatrix_convex_sum {ι α : Type*} [Fintype ι] [Fintype α]
    (p : PMF α) {σ : α → Matrix ι ι ℂ} (hσ : ∀ a, Cslib.Quantum.IsDensityMatrix (σ a)) :
    Cslib.Quantum.IsDensityMatrix (∑ a : α, (p a).toReal • σ a) := by
  classical
  rw [← Cslib.Quantum.partialTraceRight_classicalQuantumState p σ]
  exact (Cslib.Quantum.isDensityMatrix_classicalQuantumState p hσ).partialTraceRight

private theorem one_bit_holevo_lower_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {σ : Bool → Matrix ι ι ℂ} (hσ : ∀ b, Cslib.Quantum.IsDensityMatrix (σ b))
    (M : Cslib.Quantum.POVM Bool ι) {ε : ℝ} (_hε0 : 0 ≤ ε) (hε2 : ε ≤ 1 / 2)
    (hdec : ∀ b : Bool, 1 - ε ≤ M.densityProb (σ b) b) :
    1 - binaryEntropyBits ε ≤
      Cslib.Quantum.holevoInformation (uniformOfFintype Bool) σ := by
  set u₁ : PMF Bool := uniformOfFintype Bool
  set joint : PMF (Bool × Bool) :=
    u₁.bind fun b => (M.measureDensity (σ b) (hσ b)).map (b, ·)
  set swapped : PMF (Bool × Bool) := joint.map Prod.swap
  have hholevo := Cslib.Quantum.mutualInfo_measureDensity_le_holevoInformation u₁ hσ M
  have hmut_eq : mutualInfo joint = mutualInfo swapped := by
    have hid : joint.map (fun ω => (ω.1, ω.2)) = joint := by
      ext ⟨x, y⟩
      exact map_apply_of_injective joint (fun _ _ h => h) (x, y)
    have hmut1 : mutualInfo joint =
        entropy (joint.map Prod.fst) + entropy (joint.map Prod.snd) - entropy joint := by
      simpa only [hid] using mutualInfo_map joint Prod.fst Prod.snd
    have hmut2 : mutualInfo swapped =
        entropy (joint.map Prod.snd) + entropy (joint.map Prod.fst) - entropy swapped :=
      mutualInfo_map joint Prod.snd Prod.fst
    have hent : entropy swapped = entropy joint :=
      entropy_map_of_injective joint Prod.swap_injective
    linarith
  have hsnd_u1 : swapped.map Prod.snd = u₁ := by
    have : swapped.map Prod.snd = joint.map Prod.fst := by rw [_root_.PMF.map_comp]; rfl
    rw [this]
    exact map_fst_bind_pair u₁ _
  have hent_u1 : entropy u₁ = 1 := by
    rw [entropy_uniform, Fintype.card_bool, Nat.cast_ofNat,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
  have hmut_val : mutualInfo swapped = 1 - conditionalEntropy swapped := by
    rw [mutualInfo_eq_entropy_map_snd_sub_conditionalEntropy, hsnd_u1, hent_u1]
  set Pe : ℝ := (swapped.toOuterMeasure {z | ¬z.1 = z.2}).toReal
  have hfano : conditionalEntropy swapped ≤ Real.binEntropy Pe / Real.log 2 := by
    have h1 := conditionalEntropy_le_binEntropy_add_mul_logb swapped id
    have hcard : ((Fintype.card Bool : ℝ) - 1) = 1 := by norm_num
    rw [hcard, Real.logb_one, mul_zero, add_zero] at h1
    exact h1
  have hPe_nonneg : 0 ≤ Pe := ENNReal.toReal_nonneg
  have herr_bound (b : Bool) : M.densityProb (σ b) (!b) ≤ ε := by
    have hsum := M.sum_densityProb (σ b)
    rw [(hσ b).trace_eq_one, Complex.one_re, Fintype.sum_bool] at hsum
    cases b <;> simp only [Bool.not_true, Bool.not_false] <;> linarith [hdec true, hdec false]
  have hPe_le : Pe ≤ ε := by
    have hswap_apply (bhat b : Bool) :
        (swapped (bhat, b)).toReal = (1 / 2 : ℝ) * M.densityProb (σ b) bhat := by
      have hinj : swapped (bhat, b) = joint (b, bhat) := by
        simpa [swapped] using
          map_apply_of_injective joint Prod.swap_injective (b, bhat)
      rw [hinj, bind_map_prodMk_apply, ENNReal.toReal_mul]
      have hu : (u₁ b).toReal = 1 / 2 := by simp [u₁, uniformOfFintype_apply]
      have hm : (M.measureDensity (σ b) (hσ b) bhat).toReal = M.densityProb (σ b) bhat := by
        rw [Cslib.Quantum.POVM.measureDensity_apply,
          ENNReal.toReal_ofReal (M.densityProb_nonneg (hσ b).posSemidef bhat)]
      rw [hu, hm]
    rw [show Pe = (swapped.toOuterMeasure {z | ¬z.1 = z.2}).toReal from rfl,
      toOuterMeasure_apply_toReal, Fintype.sum_prod_type,
      Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
    simp only [Set.mem_ofPred_eq, not_true_eq_false, ↓reduceIte, Bool.true_eq_false,
      not_false_eq_true, Bool.false_eq_true, hswap_apply]
    have hf : M.densityProb (σ false) true ≤ ε := herr_bound false
    have ht : M.densityProb (σ true) false ≤ ε := herr_bound true
    linarith
  have hbin_le : Real.binEntropy Pe / Real.log 2 ≤ binaryEntropyBits ε := by
    rw [binaryEntropyBits]
    exact div_le_div_of_nonneg_right (binEntropy_mono_on_half hPe_nonneg hPe_le hε2)
      (Real.log_pos one_lt_two).le
  linarith [hholevo, hmut_eq, hmut_val, hfano, hbin_le]

/-- **Quantum Random Access Code Lower Bound**: encoding `n`-bit strings into density matrices
`ρ : BitString n → Matrix ι ι ℂ` so that each coordinate `i : Fin n` is recovered with success
probability at least `1 - ε` (`0 ≤ ε ≤ 1 / 2`) requires
`(1 - binaryEntropyBits ε) * n ≤ log₂ |ι|`. -/
theorem qrac_qubit_lower_bound {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ : Cslib.BitString n → Matrix ι ι ℂ}
    (hρ : ∀ y, Cslib.Quantum.IsDensityMatrix (ρ y))
    (M : Fin n → Cslib.Quantum.POVM Bool ι)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε2 : ε ≤ 1 / 2)
    (hdec : ∀ (i : Fin n) (y : Cslib.BitString n), 1 - ε ≤ (M i).densityProb (ρ y) (y i)) :
    (1 - binaryEntropyBits ε) * (n : ℝ) ≤ Real.logb 2 (Fintype.card ι) := by
  suffices hchi : (1 - binaryEntropyBits ε) * (n : ℝ) ≤
      Cslib.Quantum.holevoInformation (uniformOfFintype (Cslib.BitString n)) ρ from
    hchi.trans (Cslib.Quantum.holevoInformation_le_logb_card _ hρ)
  induction n with
  | zero =>
    simpa using Cslib.Quantum.holevoInformation_nonneg
      (uniformOfFintype (Cslib.BitString 0)) hρ
  | succ n ih =>
    set u_succ := uniformOfFintype (Cslib.BitString (n + 1))
    set u₁ := uniformOfFintype Bool
    set u_n := uniformOfFintype (Cslib.BitString n)
    let e : Bool × Cslib.BitString n ≃ Cslib.BitString (n + 1) :=
      Fin.consEquiv (fun _ : Fin (n + 1) => Bool)
    let bar (b : Bool) : Matrix ι ι ℂ :=
      ∑ z : Cslib.BitString n, (u_n z).toReal • ρ (Fin.cons b z)
    have hbar_dens (b : Bool) : Cslib.Quantum.IsDensityMatrix (bar b) :=
      isDensityMatrix_convex_sum u_n fun z => hρ (Fin.cons b z)
    have hbar_dec (b : Bool) : 1 - ε ≤ (M 0).densityProb (bar b) b := by
      dsimp only [bar]
      rw [densityProb_sum_smul]
      calc
        1 - ε = (∑ z : Cslib.BitString n, (u_n z).toReal) * (1 - ε) := by
              rw [sum_toReal u_n, one_mul]
        _ = ∑ z : Cslib.BitString n, (u_n z).toReal * (1 - ε) := Finset.sum_mul _ _ _
        _ ≤ ∑ z : Cslib.BitString n,
              (u_n z).toReal * (M 0).densityProb (ρ (Fin.cons b z)) b := by
              refine Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
              simpa using hdec 0 (Fin.cons b z)
    have hfirst := one_bit_holevo_lower_bound hbar_dens (M 0) hε0 hε2 hbar_dec
    have htail (b : Bool) :
        (1 - binaryEntropyBits ε) * (n : ℝ) ≤
          Cslib.Quantum.holevoInformation u_n (fun z => ρ (Fin.cons b z)) :=
      ih (fun z => hρ (Fin.cons b z)) (fun i => M i.succ) fun i z => by
        simpa using hdec i.succ (Fin.cons b z)
    have hw (b : Bool) (z : Cslib.BitString n) :
        (u_succ (e (b, z))).toReal = (u₁ b).toReal * (u_n z).toReal := by
      have hc : Fintype.card (Cslib.BitString (n + 1)) =
          Fintype.card Bool * Fintype.card (Cslib.BitString n) := by
        rw [← Fintype.card_prod, Fintype.card_congr e]
      simp only [u_succ, u₁, u_n, uniformOfFintype_apply, hc, Nat.cast_mul, ENNReal.toReal_inv,
        ENNReal.toReal_mul, ENNReal.toReal_natCast, mul_inv]
    have havg : (∑ y : Cslib.BitString (n + 1), (u_succ y).toReal • ρ y) =
        ∑ b : Bool, (u₁ b).toReal • bar b := by
      rw [← e.sum_comp, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun b _ => ?_
      dsimp only [bar, e, Fin.consEquiv]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [smul_smul, ← hw b z]
      rfl
    have hent_sum : (∑ y : Cslib.BitString (n + 1),
          (u_succ y).toReal * Cslib.Quantum.vonNeumannEntropy (ρ y)) =
        ∑ b : Bool, (u₁ b).toReal *
          ∑ z : Cslib.BitString n,
            (u_n z).toReal * Cslib.Quantum.vonNeumannEntropy (ρ (Fin.cons b z)) := by
      rw [← e.sum_comp, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [← mul_assoc, ← hw b z]
      rfl
    have hchain : Cslib.Quantum.holevoInformation u_succ ρ =
        Cslib.Quantum.holevoInformation u₁ bar +
          ∑ b : Bool, (u₁ b).toReal *
            Cslib.Quantum.holevoInformation u_n (fun z => ρ (Fin.cons b z)) := by
      simp only [Cslib.Quantum.holevoInformation, havg, hent_sum, mul_sub,
        Finset.sum_sub_distrib]
      ring
    have htail_avg : (1 - binaryEntropyBits ε) * (n : ℝ) ≤
        ∑ b : Bool, (u₁ b).toReal *
          Cslib.Quantum.holevoInformation u_n (fun z => ρ (Fin.cons b z)) := by
      calc
        (1 - binaryEntropyBits ε) * (n : ℝ)
          = (∑ b : Bool, (u₁ b).toReal) * ((1 - binaryEntropyBits ε) * (n : ℝ)) := by
              rw [Cslib.Probability.PMF.sum_toReal u₁, one_mul]
        _ = ∑ b : Bool, (u₁ b).toReal * ((1 - binaryEntropyBits ε) * (n : ℝ)) :=
              Finset.sum_mul _ _ _
        _ ≤ ∑ b : Bool, (u₁ b).toReal *
              Cslib.Quantum.holevoInformation u_n (fun z => ρ (Fin.cons b z)) :=
              Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (htail b) ENNReal.toReal_nonneg
    rw [hchain, Nat.cast_add, Nat.cast_one, mul_add, mul_one]
    linarith

/-- A one-way quantum communication protocol sending a single density-matrix message on `ℂ^ι` from
Bob to Alice, followed by Alice's input-dependent POVM measurement. -/
@[ext]
structure OneWayQuantumProtocol (X Y ι Z : Type*) [Fintype ι] [DecidableEq ι] [Fintype Z] where
  /-- Density matrix prepared and sent by Bob on input `y`. -/
  bobState : Y → Matrix ι ι ℂ
  /-- Validity of Bob's message density matrices. -/
  isDensity_bobState : ∀ y, Cslib.Quantum.IsDensityMatrix (bobState y)
  /-- Alice's readout POVM given input `x`. -/
  alicePOVM : X → Cslib.Quantum.POVM Z ι

/-- Qubit cost `log₂ |ι|` of a one-way quantum protocol on `ℂ^ι`. -/
noncomputable def OneWayQuantumProtocol.qubitCost {X Y ι Z : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Z] (_P : OneWayQuantumProtocol X Y ι Z) : ℝ :=
  Real.logb 2 (Fintype.card ι)

/-- `P` solves `f : X → Y → Z` with worst-case error `ε` if `f x y` is output with probability at
least `1 - ε` on every input pair `(x, y)`. -/
def OneWayQuantumProtocol.Solves {X Y ι Z : Type*} [Fintype ι] [DecidableEq ι] [Fintype Z]
    (P : OneWayQuantumProtocol X Y ι Z) (ε : ℝ) (f : X → Y → Z) : Prop :=
  ∀ x y, 1 - ε ≤ (P.alicePOVM x).densityProb (P.bobState y) (f x y)

/-- One-way quantum communication lower bound for Set Disjointness: any one-way quantum protocol
solving `Cslib.Communication.disjointness` on `n`-bit inputs with error `ε ∈ [0, 1 / 2]` transmits
at least `(1 - binaryEntropyBits ε) * n` qubits. -/
theorem oneWay_disjointness_qubit_lower_bound {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : OneWayQuantumProtocol (Cslib.BitString n) (Cslib.BitString n) ι Bool)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε2 : ε ≤ 1 / 2)
    (hP : P.Solves ε Cslib.Communication.disjointness) :
    (1 - binaryEntropyBits ε) * (n : ℝ) ≤ P.qubitCost := by
  let flip (M : Cslib.Quantum.POVM Bool ι) : Cslib.Quantum.POVM Bool ι :=
    { effect := fun b => M.effect (!b)
      posSemidef := fun b => M.posSemidef (!b)
      sum_effect := by
        have h := M.sum_effect
        rw [Fintype.sum_bool] at h ⊢
        simpa [add_comm] using h }
  let single (i : Fin n) : Cslib.BitString n := fun k => decide (k = i)
  have hsingle (i : Fin n) (y : Cslib.BitString n) :
      Cslib.Communication.disjointness (single i) y = !y i := by
    unfold Cslib.Communication.disjointness single
    cases hyi : y i
    · simp only [Bool.not_false, decide_eq_true_eq]
      intro k
      by_cases hk : k = i
      · subst hk; simp [hyi]
      · simp [hk]
    · simp only [Bool.not_true, decide_eq_false_iff_not, not_forall]
      exact ⟨i, by simp [hyi]⟩
  refine qrac_qubit_lower_bound P.isDensity_bobState
    (fun i => flip (P.alicePOVM (single i))) hε0 hε2 fun i y => ?_
  have hsol := hP (single i) y
  rw [hsingle] at hsol
  exact hsol

/-- Explicit `n / 24` one-way quantum communication lower bound for Set Disjointness at error
`1 / 3`. -/
theorem oneWay_disjointness_one_third_qubit_lower_bound {n : ℕ}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : OneWayQuantumProtocol (Cslib.BitString n) (Cslib.BitString n) ι Bool)
    (hP : P.Solves (1 / 3) Cslib.Communication.disjointness) :
    (n : ℝ) / 24 ≤ P.qubitCost := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hpow : (3 : ℝ) ^ (8 : ℕ) ≤ (2 : ℝ) ^ (13 : ℕ) := by norm_num
  have hlog_pow := Real.log_le_log (by positivity) hpow
  rw [Real.log_pow, Real.log_pow] at hlog_pow
  norm_num at hlog_pow
  have hbin : Real.binEntropy (1 / 3) = Real.log 3 - (2 / 3) * Real.log 2 := by
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    norm_num [Real.negMulLog, Real.log_inv, Real.log_div]
    ring
  have h1_24 : (1 / 24 : ℝ) ≤ 1 - binaryEntropyBits (1 / 3) := by
    rw [binaryEntropyBits, hbin, le_sub_comm, div_le_iff₀ hlog2_pos]
    linarith
  have h1 := oneWay_disjointness_qubit_lower_bound P (by norm_num) (by norm_num) hP
  have h2 := mul_le_mul_of_nonneg_right h1_24 (Nat.cast_nonneg n)
  linarith

end CslibFrontier.Computability.Communication
