/-
Copyright (c) 2026 The CslibFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The CslibFrontier contributors
-/
module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.QMA
public import CslibFrontier.Computability.Complexity.Classes.QMA.MA
public import CslibFrontier.Computability.Complexity.Classes.BQP.Amplification
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Foundations.Combinatorics.MajorityVote.Weighted

/-!
# The class `QCMA` (Quantum-Classical Merlin–Arthur)

`QCMA` (introduced as `MQA` by [Kitaev, Shen, Vyalyi] and named `QCMA` by
[Aharonov, Naveh]) is the restriction of `QMA` to classical witness strings: a
polynomial-time uniform family of quantum verifiers (`Cslib.Quantum.UniformVerifierFamily`)
receives the encoded instance together with a computational-basis witness `|z⟩` on
`witnessLength n` qubits.

This module defines `PromiseQCMA` and `QCMA` on top of `Cslib.Quantum.UniformVerifierFamily` and
establishes three core structural theorems:

1. **Witness-preserving strong error reduction** (`PromiseQCMA_subset_errorExponent`,
   `mem_QCMA_iff_forall_errorExponent`): copying both the classical input and the classical witness
   into `2 r(n)` parallel blocks via `Cslib.Quantum.Amplify.codes` reduces completeness and
   soundness error to `2^{-q(n)}` for any polynomial `q` without increasing witness length.
2. **Automatic soundness against arbitrary quantum witnesses** (`dephaseWitness`,
   `acceptProb_dephaseWitness`, `PromiseQCMA_subset_PromiseQMA`, `QCMA_subset_QMA`): CNOT-copying
   each witness qubit into a fresh zero ancilla before running `V` dephases any entangled/quantum
   witness state `ψ` in the computational basis so its acceptance probability is the convex
   combination `∑_z ‖ψ_z‖² V.acceptProb x |z⟩`, proving `PromiseQCMA c s ⊆ PromiseQMA c s` for all
   `(c, s)`.
3. **Classical inclusions** (`BQP_subset_QCMA`, `MA_subset_QCMA`):
   `BQP ⊆ QCMA` and `MA ⊆ QCMA ⊆ QMA`.
-/

public section

namespace CslibFrontier.Complexity

open Finset Cslib.Quantum Cslib.Complexity Cslib.Quantum.GateCode Turing.MultiTapeTM

variable {α : Type}

/-- The verifier family `V` decides promise problem `Q` in `QCMA(c, s)` when every yes-instance has
a classical witness string `z` accepted as `|z⟩` with probability at least `c n`, and on every
no-instance every classical witness string `z` is accepted as `|z⟩` with probability at most
`s n`, where `n = (enc a).length`. -/
@[expose]
def IsQCMAVerifier (enc : α ↪ List Bool) (c s : ℕ → ℝ) (V : UniformVerifierFamily)
    (Q : PromiseProblem α) : Prop :=
  ∀ a, (a ∈ Q.yes → ∃ z : Fin (V.witnessLength (enc a).length) → Bool,
      c (enc a).length ≤ V.acceptProb (enc a) (ket z)) ∧
    (a ∈ Q.no → ∀ z : Fin (V.witnessLength (enc a).length) → Bool,
      V.acceptProb (enc a) (ket z) ≤ s (enc a).length)

/-- **`QCMA(c, s)`** for promise problems. -/
@[expose]
def PromiseQCMA (c s : ℕ → ℝ) (enc : α ↪ List Bool) : Set (PromiseProblem α) :=
  {Q | ∃ V : UniformVerifierFamily, IsQCMAVerifier enc c s V Q}

/-- **`QCMA`**: decision problems decided by polynomial-time uniform quantum verifiers with
classical witnesses, completeness `2 / 3`, and soundness `1 / 3`. -/
@[expose]
noncomputable def QCMA (enc : α ↪ List Bool) : Set (Set α) :=
  {A | PromiseProblem.ofSet A ∈ PromiseQCMA (fun _ => 2 / 3) (fun _ => 1 / 3) enc}

variable {enc : α ↪ List Bool} {A : Set α}

/-- Membership in `QCMA` unfolded. -/
theorem mem_QCMA : A ∈ QCMA enc ↔ ∃ V : UniformVerifierFamily, ∀ a,
    (a ∈ A → ∃ z : Fin (V.witnessLength (enc a).length) → Bool,
      2 / 3 ≤ V.acceptProb (enc a) (ket z)) ∧
    (a ∉ A → ∀ z : Fin (V.witnessLength (enc a).length) → Bool,
      V.acceptProb (enc a) (ket z) ≤ 1 / 3) := by
  rfl

/-- Weakening completeness and soundness enlarges `PromiseQCMA`. -/
theorem PromiseQCMA_mono {c c' s s' : ℕ → ℝ} (hc : ∀ n, c' n ≤ c n) (hs : ∀ n, s n ≤ s' n) :
    PromiseQCMA c s enc ⊆ PromiseQCMA c' s' enc := by
  rintro Q ⟨V, hV⟩
  refine ⟨V, fun a => ⟨fun ha => ?_, fun ha z => ((hV a).2 ha z).trans (hs _)⟩⟩
  obtain ⟨z, hz⟩ := (hV a).1 ha
  exact ⟨z, (hc _).trans hz⟩

/-- **`BQP ⊆ QCMA`**: a `BQP` circuit family is a `QCMA` verifier reading zero witness bits. -/
theorem BQP_subset_QCMA : BQP enc ⊆ QCMA enc := by
  rintro A ⟨F, hF⟩
  refine ⟨UniformVerifierFamily.ofCircuitFamily F, fun a => ⟨fun ha => ⟨default, ?_⟩,
    fun ha z => ?_⟩⟩
  · rw [UniformVerifierFamily.acceptProb_ofCircuitFamily, norm_ket, one_pow, one_mul]
    exact (hF a).1 ha
  · rw [UniformVerifierFamily.acceptProb_ofCircuitFamily, norm_ket, one_pow, one_mul]
    exact (hF a).2 ha

/-- **`MA ⊆ QCMA`**: Merlin's classical proof is supplied directly as a computational-basis witness
and Arthur's random coins are prepared with Hadamard gates via `UniformVerifierFamily.ofMA`. -/
theorem MA_subset_QCMA : MA enc ⊆ QCMA enc := by
  rintro A ⟨q, p, V, hV, hA⟩
  obtain ⟨F, hF⟩ := exists_uniformCircuitFamily hV
  refine mem_QCMA.mpr ⟨UniformVerifierFamily.ofMA F q p, fun a => ⟨fun ha => ?_, fun ha z => ?_⟩⟩
  · obtain ⟨y, hy⟩ := (hA a).1 ha
    have hge : (2 / 3 : ℝ) ≤
        (univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
          V (a, List.ofFn y ++ List.ofFn r) = true).card / 2 ^ p.eval (enc a).length := by
      rw [le_div_iff₀ (by positivity)]
      linarith [show (2 * 2 ^ p.eval (enc a).length : ℝ) ≤
        3 * #(univ.filter fun r => V (a, List.ofFn y ++ List.ofFn r) = true) from mod_cast hy]
    exact ⟨y, hge.trans_eq
      (UniformVerifierFamily.acceptProb_ofMA_ket F q p (enc a) _ (fun w _ => hF (a, w)) y).symm⟩
  · have hfalse := (hA a).2 ha z
    have hle : ((univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
        V (a, List.ofFn z ++ List.ofFn r) = true).card /
        2 ^ p.eval (enc a).length : ℝ) ≤ 1 / 3 := by
      have hsum := card_filter_add_card_filter_not (s := univ)
        fun r : Fin (p.eval (enc a).length) → Bool => V (a, List.ofFn z ++ List.ofFn r) = true
      simp only [Bool.not_eq_true, card_univ, Fintype.card_fun, Fintype.card_fin,
        Fintype.card_bool] at hsum
      rw [div_le_iff₀ (by positivity)]
      linarith [show (2 * 2 ^ p.eval (enc a).length : ℝ) ≤
          3 * #(univ.filter fun r => V (a, List.ofFn z ++ List.ofFn r) = false) from
          mod_cast hfalse,
        show (#(univ.filter fun r => V (a, List.ofFn z ++ List.ofFn r) = true) : ℝ) +
          #(univ.filter fun r => V (a, List.ofFn z ++ List.ofFn r) = false) =
          2 ^ p.eval (enc a).length from mod_cast hsum]
    exact (UniformVerifierFamily.acceptProb_ofMA_ket F q p (enc a) _
      (fun w _ => hF (a, w)) z).trans_le hle

/-! ### Witness-dephasing unitary and `PromiseQCMA c s ⊆ PromiseQMA c s` -/

/-- CNOT gates copying witness qubits `n, …, n + p - 1` into fresh ancilla qubits
`w, …, w + p - 1`. -/
def dephaseCopyCodes (n p w : ℕ) : List GateCode :=
  (List.range p).map fun i => (false, i + w, [i + n])

theorem isClassical_dephaseCopyCodes {n p w : ℕ} (hnw : n + p ≤ w) :
    IsClassical (w + p) (dephaseCopyCodes n p w) := by
  intro g hg
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hg
  have hi' : i < p := List.mem_range.mp hi
  refine ⟨rfl, by simp, ?_, ?_⟩
  · simp; omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    omega

private theorem wellFormed_mono {w w' : ℕ} {g : GateCode}
    (hg : GateCode.WellFormed w g) (hww : w ≤ w') : GateCode.WellFormed w' g := by
  rcases g with ⟨false | true, t, cs⟩
  · exact ⟨hg.1, hg.2.1, fun i hi => lt_of_lt_of_le (hg.2.2 i hi) hww⟩
  · exact ⟨lt_of_lt_of_le hg.1 hww, hg.2⟩

/-- Modify a quantum verifier `V` to first copy its witness qubits in the computational basis into
`V.witnessLength n` fresh ancilla qubits at the end of the register, dephasing any quantum witness
into an incoherent computational-basis mixture without changing acceptance on basis witnesses. -/
abbrev dephaseWitness (V : UniformVerifierFamily) : UniformVerifierFamily where
  width n := V.width n + V.witnessLength n
  gates n := dephaseCopyCodes n (V.witnessLength n) (V.width n) ++ V.gates n
  computableInPolyTime_width := by
    have := V.computableInPolyTime_width
    have := V.computableInPolyTime_witnessLength
    fun_prop
  computableInPolyTime_gates := by
    have := V.computableInPolyTime_width
    have := V.computableInPolyTime_witnessLength
    have := V.computableInPolyTime_gates
    unfold dephaseCopyCodes
    fun_prop
  le_width n := (V.le_width n).trans (Nat.le_add_right _ _)
  width_pos n := Nat.lt_of_lt_of_le (V.width_pos n) (Nat.le_add_right _ _)
  wellFormed n g hg := by
    rcases List.mem_append.mp hg with hg | hg
    · exact (isClassical_dephaseCopyCodes (V.add_witnessLength_le n) g hg).2
    · exact wellFormed_mono (V.wellFormed n g hg) (Nat.le_add_right _ _)
  witnessLength := V.witnessLength
  computableInPolyTime_witnessLength := V.computableInPolyTime_witnessLength
  add_witnessLength_le n := (V.add_witnessLength_le n).trans (Nat.le_add_right _ _)

/-- On any quantum witness state `ψ`, `dephaseWitness V` accepts with probability
`∑_z ‖ψ_z‖² * V.acceptProb x (ket z)`. -/
theorem acceptProb_dephaseWitness (V : UniformVerifierFamily) (x : List Bool)
    (ψ : Qubits (V.witnessLength x.length)) :
    (dephaseWitness V).acceptProb x ψ =
      ∑ z : Fin (V.witnessLength x.length) → Bool, ‖ψ.ofLp z‖ ^ 2 * V.acceptProb x (ket z) := by
  let n := x.length
  let p := V.witnessLength n
  let w := V.width n
  have hnw : n + p ≤ w := V.add_witnessLength_le n
  have hnw_tot : n + p ≤ w + p := hnw.trans (Nat.le_add_right w p)
  -- Action of `dephaseCopyCodes n p w` on `inputState (w + p) (x ++ List.ofFn z)`:
  have hcopy (z : Fin p → Bool) :
      classicalRun (dephaseCopyCodes n p w)
        (glue (blockEmb n hnw_tot) z (inputState (w + p) x)) =
      glue (blockEmb w (le_refl (w + p))) z (inputState (w + p) (x ++ List.ofFn z)) := by
    have hread : ∀ g ∈ dephaseCopyCodes n p w, ∀ g' ∈ dephaseCopyCodes n p w,
        g.2.1 ∉ g'.2.2 := by
      intro g hg g' hg'
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hg
      obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hg'
      have := List.mem_range.mp hi'
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      omega
    have hnodup : ((dephaseCopyCodes n p w).map fun g => g.2.1).Nodup := by
      simp only [dephaseCopyCodes, List.map_map, Function.comp_def]
      exact (List.nodup_range).map fun i j h => by omega
    let X₀ := glue (blockEmb n hnw_tot) z (inputState (w + p) x)
    have hX₀_eq : X₀ = inputState (w + p) (x ++ List.ofFn z) :=
      glue_blockEmb_inputState hnw_tot x rfl z
    refine funext_readBit fun c => ?_
    by_cases hc : ∃ i < p, i + w = c
    · obtain ⟨i, hi, rfl⟩ := hc
      have hg : ((false, i + w, [i + n]) : GateCode) ∈ dephaseCopyCodes n p w :=
        List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
      have h1 := readBit_classicalRun_of_mem
        (fun g hg' => by
          obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg'
          have := List.mem_range.mp hj
          dsimp only [GateCode.target]; omega)
        hnodup hread X₀ hg
      simp only [GateCode.target_mk, GateCode.controls_mk, List.all_cons, List.all_nil,
        Bool.and_true] at h1
      have hX₀_hi : readBit X₀ (i + w) = false := by
        rw [hX₀_eq]
        exact readBit_inputState_of_le (by simp only [List.length_append, List.length_ofFn]; omega)
      have hX₀_ctrl : readBit X₀ (i + n) = z ⟨i, hi⟩ := by
        rw [readBit_of_lt _ (by omega : i + n < w + p)]
        exact glue_apply_emb (blockEmb n hnw_tot) z (inputState (w + p) x) ⟨i, hi⟩
      rw [h1, hX₀_hi, hX₀_ctrl, Bool.false_xor, readBit_of_lt _ (by omega : i + w < w + p)]
      exact (glue_apply_emb (blockEmb w (le_refl (w + p))) z _ ⟨i, hi⟩).symm
    · push Not at hc
      have h1 := readBit_classicalRun_of_forall_ne
        (gs := dephaseCopyCodes n p w) (q := c) (fun g hg => by
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hg
        dsimp only [GateCode.target]
        exact hc i (List.mem_range.mp hi)) X₀
      rw [h1, readBit_glue_of_forall_ne (blockEmb w (le_refl (w + p))) z _
        (fun q => hc q.1 q.2), hX₀_eq]
  -- Embed `w`-qubit circuit into `w + p` qubits via `blockEmb 0`:
  have hw_le : 0 + w ≤ w + p := by omega
  let e0 : Fin w ↪ Fin (w + p) := blockEmb 0 hw_le
  let eAnc : Fin p ↪ Fin (w + p) := blockEmb w (le_refl (w + p))
  let bg (z : Fin p → Bool) : Fin (w + p) → Bool := glue eAnc z (fun _ => false)
  let φ (z : Fin p → Bool) : Qubits w :=
    Circuit.run (Circuit.ofCodes w (V.gates n)) (inputState w (x ++ List.ofFn z))
  have hcast_codes :
      Circuit.ofCodes (w + p) (V.gates n) =
        (Circuit.ofCodes w (V.gates n)).mapWires e0 := by
    have h0 : GateCode.shift 0 = id := by funext ⟨_, _, _⟩; simp [GateCode.shift]
    have hmap : (V.gates n).map (GateCode.shift 0) = V.gates n := by simp [h0]
    simpa [hmap, e0] using Circuit.ofCodes_map_shift hw_le (V.wellFormed n)
  have hglue_split (z : Fin p → Bool) :
      glue eAnc z (inputState (w + p) (x ++ List.ofFn z)) =
        glue e0 (inputState w (x ++ List.ofFn z)) (bg z) := by
    funext j
    by_cases hjw : (j : ℕ) < w
    · have hj_e0 : j = e0 ⟨j, hjw⟩ := Fin.ext (by simp [e0])
      have hnot_anc : ∀ i : Fin p, eAnc i ≠ j := by
        intro i h
        have := congrArg Fin.val h
        simp [eAnc] at this
        omega
      rw [glue_of_not eAnc z _ hnot_anc]
      conv_rhs => rw [hj_e0, glue_apply_emb]
      rfl
    · have hj_anc : j = eAnc ⟨(j : ℕ) - w, by omega⟩ := Fin.ext (by simp [eAnc]; omega)
      have hnot_e0 : ∀ k : Fin w, e0 k ≠ j := by
        intro k h
        have := congrArg Fin.val h
        simp [e0] at this
        omega
      rw [glue_of_not e0 _ (bg z) hnot_e0]
      dsimp only [bg]
      rw [hj_anc, glue_apply_emb, glue_apply_emb]
  have hagree_iff (Y : Fin (w + p) → Bool) (z : Fin p → Bool) :
      AgreeOff e0 Y (bg z) ↔ Y ∘ eAnc = z := by
    refine ⟨fun h => funext fun i => ?_, fun h j hj => ?_⟩
    · have hnot : ∀ k : Fin w, e0 k ≠ eAnc i := by
        intro k hk
        have := congrArg Fin.val hk
        simp [e0, eAnc] at this
        omega
      exact (h (eAnc i) hnot).trans (glue_apply_emb eAnc z _ i)
    · have hjw : ¬(j : ℕ) < w := fun hlt => hj ⟨j, hlt⟩ (Fin.ext (by simp [e0]))
      have hj_anc : j = eAnc ⟨(j : ℕ) - w, by omega⟩ := Fin.ext (by simp [eAnc]; omega)
      rw [hj_anc]
      dsimp only [bg]
      rw [glue_apply_emb, ← h]
      rfl
  let Ψ : Qubits (w + p) :=
    Circuit.eval (Circuit.ofCodes (w + p) ((dephaseWitness V).gates n))
      (embedState ((dephaseWitness V).witnessQubits n) (inputState (w + p) x) ψ)
  have hΨ_eq : Ψ = ∑ z : Fin p → Bool, ψ.ofLp z • embedState e0 (bg z) (φ z) := by
    dsimp only [Ψ, dephaseWitness, UniformVerifierFamily.witnessQubits]
    rw [embedState_eq_sum, Circuit.ofCodes_append, Circuit.eval_append, map_sum, map_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [map_smul, map_smul, Circuit.eval_ofCodes_ket (isClassical_dephaseCopyCodes hnw),
      hcopy z, hglue_split z, ← embedState_ket, hcast_codes, Circuit.eval_mapWires_embedState]
    rfl
  have hΨ_apply (Y : Fin (w + p) → Bool) :
      Ψ.ofLp Y = ψ.ofLp (Y ∘ eAnc) * (φ (Y ∘ eAnc)).ofLp (Y ∘ e0) := by
    rw [hΨ_eq, WithLp.ofLp_sum, Finset.sum_apply]
    rw [Finset.sum_eq_single (Y ∘ eAnc)]
    · simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, embedState_apply]
      rw [ite_eq_left ((hagree_iff Y (Y ∘ eAnc)).mpr rfl)]
    · intro z _ hz
      simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, embedState_apply]
      have hna : ¬AgreeOff e0 Y (bg z) := fun ha => hz ((hagree_iff Y z).mp ha).symm
      rw [ite_eq_right hna, mul_zero]
    · exact fun h => absurd (mem_univ _) h
  have hw_pos : 0 < w := V.width_pos n
  have hwtot_pos : 0 < w + p := by omega
  have hacc_glue (z : Fin p → Bool) (y : Fin w → Bool) :
      glue e0 y (bg z) ∈ accepting (w + p) ↔ y ∈ accepting w := by
    rw [mem_accepting hwtot_pos, mem_accepting hw_pos]
    have h0 : (⟨0, hwtot_pos⟩ : Fin (w + p)) = e0 ⟨0, hw_pos⟩ := Fin.ext (by simp [e0])
    rw [h0, glue_apply_emb]
  change measureProb Ψ (accepting (w + p)) = _
  rw [measureProb]
  -- Partition sum over `Y : Fin (w + p) → Bool` by `z = Y ∘ eAnc` via `sum_agreeOff`:
  calc
    (∑ Y ∈ accepting (w + p), ‖Ψ.ofLp Y‖ ^ 2) =
        ∑ Y : Fin (w + p) → Bool,
          if Y ∈ accepting (w + p) then
            ‖ψ.ofLp (Y ∘ eAnc)‖ ^ 2 * ‖(φ (Y ∘ eAnc)).ofLp (Y ∘ e0)‖ ^ 2
          else 0 := by
      have hacc_f : accepting (w + p) = univ.filter (· ∈ accepting (w + p)) := by ext; simp
      conv_lhs => rw [hacc_f, Finset.sum_filter]
      refine Finset.sum_congr rfl fun Y _ => ?_
      split_ifs with hY
      · rw [hΨ_apply, norm_mul, mul_pow]
      · rfl
    _ = ∑ Y : Fin (w + p) → Bool, ∑ z : Fin p → Bool,
          if AgreeOff e0 Y (bg z) then
            (if Y ∈ accepting (w + p) then ‖ψ.ofLp z‖ ^ 2 * ‖(φ z).ofLp (Y ∘ e0)‖ ^ 2 else 0)
          else 0 := by
      refine Finset.sum_congr rfl fun Y _ => ?_
      rw [Finset.sum_eq_single (Y ∘ eAnc)]
      · rw [ite_eq_left ((hagree_iff Y (Y ∘ eAnc)).mpr rfl)]
      · intro z _ hz
        exact ite_eq_right fun ha => hz ((hagree_iff Y z).mp ha).symm
      · exact fun h => absurd (mem_univ _) h
    _ = ∑ z : Fin p → Bool, ∑ Y : Fin (w + p) → Bool,
          if AgreeOff e0 Y (bg z) then
            (if Y ∈ accepting (w + p) then ‖ψ.ofLp z‖ ^ 2 * ‖(φ z).ofLp (Y ∘ e0)‖ ^ 2 else 0)
          else 0 := Finset.sum_comm
    _ = ∑ z : Fin p → Bool, ‖ψ.ofLp z‖ ^ 2 * V.acceptProb x (ket z) := by
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [sum_agreeOff e0 (bg z) (fun Y =>
        if Y ∈ accepting (w + p) then ‖ψ.ofLp z‖ ^ 2 * ‖(φ z).ofLp (Y ∘ e0)‖ ^ 2 else 0)]
      simp only [hacc_glue z, glue_comp]
      rw [← Finset.sum_filter, ← Finset.mul_sum, UniformVerifierFamily.acceptProb_ket]
      have hf : (univ.filter fun i => i ∈ accepting w) = accepting w := by ext; simp
      rw [hf]
      rfl

/-- **`PromiseQCMA c s ⊆ PromiseQMA c s`**: any `QCMA(c, s)` verifier can be made sound against
arbitrary quantum witnesses by dephasing the witness register in the computational basis via
`dephaseWitness`. -/
theorem PromiseQCMA_subset_PromiseQMA {c s : ℕ → ℝ} (_hs_nn : ∀ n, 0 ≤ s n) :
    PromiseQCMA c s enc ⊆ PromiseQMA c s enc := by
  rintro Q ⟨V, hV⟩
  refine ⟨dephaseWitness V, fun a => ⟨fun ha => ?_, fun ha ψ hψ => ?_⟩⟩
  · obtain ⟨z, hz⟩ := (hV a).1 ha
    refine ⟨ket z, norm_ket z, ?_⟩
    rw [acceptProb_dephaseWitness, Finset.sum_eq_single z]
    · simpa [ket_apply] using hz
    · intro z' _ hne
      simp [ket_apply, hne]
    · exact fun h => absurd (mem_univ _) h
  · rw [acceptProb_dephaseWitness]
    calc
      (∑ z : Fin (V.witnessLength (enc a).length) → Bool,
          ‖ψ.ofLp z‖ ^ 2 * V.acceptProb (enc a) (ket z)) ≤
          ∑ z : Fin (V.witnessLength (enc a).length) → Bool,
            ‖ψ.ofLp z‖ ^ 2 * s (enc a).length :=
        Finset.sum_le_sum fun z _ =>
          mul_le_mul_of_nonneg_left ((hV a).2 ha z) (sq_nonneg _)
      _ = (∑ z : Fin (V.witnessLength (enc a).length) → Bool, ‖ψ.ofLp z‖ ^ 2) *
            s (enc a).length := (Finset.sum_mul ..).symm
      _ = s (enc a).length := by
        rw [← EuclideanSpace.norm_sq_eq, hψ, one_pow, one_mul]

/-- **`QCMA ⊆ QMA`**: decision problems with classical witnesses and quantum verification lie in
`QMA`. -/
theorem QCMA_subset_QMA : QCMA enc ⊆ QMA enc := by
  exact fun _ hA => PromiseQCMA_subset_PromiseQMA (fun _ => by norm_num) hA

/-! ### Witness-preserving strong error reduction for `QCMA` -/

/-- **Threshold vote of a quantum verifier on a shared classical witness**: copies both the `n`-bit
input and the `V.witnessLength n`-bit classical witness into `k(n)` parallel blocks of width
`V.width n` and outputs whether more than `t(n)` blocks accept. -/
@[expose]
def thresholdClassicalVerifier (V : UniformVerifierFamily) (k t : ℕ → ℕ)
    (hk : ComputableInPolyTime k encUnary encUnary)
    (ht : ComputableInPolyTime t encUnary encUnary) : UniformVerifierFamily where
  width n := Amplify.width (V.width n) (k n) (t n)
  gates n := Amplify.codes (n + V.witnessLength n) (V.width n) (k n) (t n) (V.gates n)
  computableInPolyTime_width := by
    have := V.computableInPolyTime_width
    simp only [Amplify.width, Amplify.base]
    fun_prop
  computableInPolyTime_gates := by
    have hnw : ComputableInPolyTime (fun n => n + V.witnessLength n) encUnary encUnary := by
      have := V.computableInPolyTime_witnessLength
      fun_prop
    exact Amplify.computableInPolyTime_codes hnw V.computableInPolyTime_width hk ht
      V.computableInPolyTime_gates
  le_width n := by
    have := V.le_width n
    have : V.width n ≤ Amplify.base (V.width n) (k n) := Amplify.le_base
    have := Amplify.base_lt_width (w := V.width n) (k := k n) (t := t n)
    omega
  width_pos n := Nat.lt_of_le_of_lt (Nat.zero_le _) Amplify.base_lt_width
  wellFormed n g hg := by
    have hw := V.width_pos n
    rcases List.mem_append.mp hg with hg | hg
    · exact (Amplify.isClassical_copyCodes (V.add_witnessLength_le n) hw g hg).2
    rcases List.mem_append.mp hg with hg | hg
    · obtain ⟨j, hj, hg⟩ := List.mem_flatMap.mp hg
      obtain ⟨g, hg', rfl⟩ := List.mem_map.mp hg
      exact (V.wellFormed n g hg').shift (Amplify.block_le_width (List.mem_range.mp hj))
    · exact (Amplify.isClassical_counter_swap hw g hg).2
  witnessLength := V.witnessLength
  computableInPolyTime_witnessLength := V.computableInPolyTime_witnessLength
  add_witnessLength_le n := by
    have := V.add_witnessLength_le n
    have : V.width n ≤ Amplify.base (V.width n) (k n) := Amplify.le_base
    have := Amplify.base_lt_width (w := V.width n) (k := k n) (t := t n)
    omega

theorem acceptProb_thresholdClassicalVerifier_ket (V : UniformVerifierFamily) {k t : ℕ → ℕ}
    (hk : ComputableInPolyTime k encUnary encUnary)
    (ht : ComputableInPolyTime t encUnary encUnary) (x : List Bool)
    (z : Fin (V.witnessLength x.length) → Bool) :
    (thresholdClassicalVerifier V k t hk ht).acceptProb x (ket z) =
      ∑ b : Fin (k x.length) → Bool with t x.length < (univ.filter fun j => b j = true).card,
        ∏ j, if b j then V.acceptProb x (ket z) else 1 - V.acceptProb x (ket z) := by
  erw [UniformVerifierFamily.acceptProb_ket, UniformVerifierFamily.acceptProb_ket]
  exact acceptProb_threshold_codes (V.width_pos x.length) (V.add_witnessLength_le x.length)
    (V.wellFormed x.length) (x ++ List.ofFn z) (by simp)

/-- Witness-preserving strict-majority error reduction for `QCMA`: `2 r(n)` parallel runs on the
same classical witness `z`. -/
@[expose]
def amplifyClassicalVerifier (V : UniformVerifierFamily) (r : ℕ → ℕ)
    (hr : ComputableInPolyTime r encUnary encUnary) : UniformVerifierFamily :=
  thresholdClassicalVerifier V (fun n => 2 * r n) r (by fun_prop) hr

/-- **Strong error reduction for `PromiseQCMA`**: `QCMA(2/3, 1/3) ⊆ QCMA(1 - 2^{-q}, 2^{-q})` for
every polynomial `q`, without increasing witness length. -/
theorem PromiseQCMA_subset_errorExponent (q : Polynomial ℕ) :
    PromiseQCMA (fun _ => 2 / 3) (fun _ => 1 / 3) enc ⊆
      PromiseQCMA (fun n => 1 - ((2 : ℝ) ^ q.eval n)⁻¹) (fun n => ((2 : ℝ) ^ q.eval n)⁻¹) enc := by
  rintro Q ⟨V, hV⟩
  have hr : ComputableInPolyTime (fun n => 6 * q.eval n) encUnary encUnary := by fun_prop
  refine ⟨amplifyClassicalVerifier V _ hr, fun a => ⟨fun ha => ?_,
    fun ha (z : Fin (V.witnessLength (enc a).length) → Bool) => ?_⟩⟩
  · obtain ⟨z, hz⟩ := (hV a).1 ha
    refine ⟨z, ?_⟩
    set p := V.acceptProb (enc a) (ket z)
    set R := 6 * q.eval (enc a).length
    have hp_le : p ≤ 1 := by
      have := V.acceptProb_le (enc a) (ket z)
      rwa [norm_ket, one_pow] at this
    have hq_nn : ∀ c : Bool, 0 ≤ if c then p else 1 - p := fun c => by
      cases c <;> simp <;> linarith
    have hsum1 : ∑ c : Bool, (if c then p else 1 - p) = 1 := by simp
    have hbad := Cslib.sum_prod_le_of_card_filter_le (fun c : Bool => if c then p else 1 - p)
      hq_nn hsum1 {true} (by simpa using (by linarith : (2 : ℝ) ≤ 3 * p)) R
    simp only [mem_singleton] at hbad
    have htotal := (Fintype.sum_pow (fun c : Bool => if c then p else 1 - p) (2 * R)).symm
    rw [hsum1, one_pow, ← sum_filter_add_sum_filter_not univ
      (fun b : Fin (2 * R) → Bool => R < (univ.filter fun j => b j = true).card)] at htotal
    simp only [not_lt] at htotal
    have hacc : (amplifyClassicalVerifier V _ hr).acceptProb (enc a) (ket z) =
        ∑ b : Fin (2 * R) → Bool with R < (univ.filter fun j => b j = true).card,
          ∏ j, if b j then p else 1 - p :=
      acceptProb_thresholdClassicalVerifier_ket V _ hr (enc a) z
    have h89 := eight_ninths_pow_le (q.eval (enc a).length)
    erw [hacc]
    linarith
  · have hz := (hV a).2 ha z
    set p := V.acceptProb (enc a) (ket z)
    set R := 6 * q.eval (enc a).length
    have hp_nn : 0 ≤ p := V.acceptProb_nonneg (enc a) (ket z)
    have hq_nn : ∀ c : Bool, 0 ≤ if c then p else 1 - p := fun c => by
      cases c <;> simp <;> linarith
    have hsum1 : ∑ c : Bool, (if c then p else 1 - p) = 1 := by simp
    have hbad := Cslib.sum_prod_le_of_card_filter_le (fun c : Bool => if c then p else 1 - p)
      hq_nn hsum1 {false} (by simpa using (by linarith : (2 : ℝ) ≤ 3 * (1 - p))) R
    simp only [mem_singleton] at hbad
    have hacc : (amplifyClassicalVerifier V _ hr).acceptProb (enc a) (ket z) =
        ∑ b : Fin (2 * R) → Bool with R < (univ.filter fun j => b j = true).card,
          ∏ j, if b j then p else 1 - p :=
      acceptProb_thresholdClassicalVerifier_ket V _ hr (enc a) z
    erw [hacc]
    refine le_trans (sum_le_sum_of_subset_of_nonneg (fun b hb => ?_)
      fun b _ _ => prod_nonneg fun j _ => hq_nn _) (hbad.trans (eight_ninths_pow_le _))
    rw [mem_filter] at hb ⊢
    refine ⟨mem_univ _, ?_⟩
    have hcard := card_filter_add_card_filter_not (s := (univ : Finset (Fin (2 * R))))
      (fun j => b j = true)
    have he : (univ.filter fun j => ¬b j = true) = univ.filter fun j => b j = false := by
      ext j; simp
    rw [he, card_univ, Fintype.card_fin] at hcard
    omega

/-- Characterization of `QCMA` via arbitrary polynomial exponential error reduction. -/
theorem mem_QCMA_iff_forall_errorExponent :
    A ∈ QCMA enc ↔ ∀ q : Polynomial ℕ,
      PromiseProblem.ofSet A ∈ PromiseQCMA
        (fun n => 1 - ((2 : ℝ) ^ q.eval n)⁻¹) (fun n => ((2 : ℝ) ^ q.eval n)⁻¹) enc := by
  refine ⟨fun h q => PromiseQCMA_subset_errorExponent q h, fun h => ?_⟩
  exact PromiseQCMA_mono (fun _ => by simp; norm_num) (fun _ => by simp; norm_num)
    (h (Polynomial.C 2))

end CslibFrontier.Complexity
