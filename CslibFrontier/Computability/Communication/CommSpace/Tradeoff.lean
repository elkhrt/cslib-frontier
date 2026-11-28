module

public import CslibFrontier.Computability.Communication.CommSpace.Circuit
public import CslibFrontier.Computability.Communication.DirectProduct.Disjointness
import Cslib.Probability.PMF
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Communication-Space Tradeoffs for Boolean Matrix Products

Communication-space tradeoffs for bounded-error randomized two-party communicating circuits
computing Boolean matrix products, proved via time-slicing and reduction to the strong direct
product theorem for `k`-fold Nondisjointness:

* Circuit slicing (`exists_heavy_slice`) and state-guessing simulation into a two-party
  `PublicCoin` protocol (`slice_to_publicCoin`).
* Block restriction embeddings of `NDISJ_{N/m}^(m)` into `boolMatVec N` and `boolMatMul N`.
* `comm_space_tradeoff_boolMatVec`: `C * S = Ω(N ^ 2)` for `N × N` Boolean matrix-vector product.
* `comm_space_tradeoff_boolMatMul`: `C * S = Ω(N ^ 3)` for `N × N` Boolean matrix multiplication.
-/

open Cslib Cslib.Communication Cslib.Probability Finset

namespace CslibFrontier.Computability.Communication

public section

/-! ### Circuit Slicing and Simulation by a 2-Party Public-Coin Protocol -/

/-- Number of crossing wires in steps `[a, b)`. -/
private def commInSlice {Out : Type*} {S : ℕ} (sch : CommSchedule Out S) (a b : ℕ) : ℕ :=
  (Finset.univ.filter fun t : Fin sch.steps =>
    a ≤ t.val ∧ t.val < b ∧ sch.isCommStep t = true).card

/-- Simulate steps `[k, k + d)` of circuit `D` as a 2-party `Protocol`, tracking Alice's emitted
outputs `outs : Fin m → Out` and concluding by having Alice transmit those `m` bits. -/
private def simSliceAliceAux {X Y Out : Type*} [DecidableEq Out] {S : ℕ}
    {sch : CommSchedule Out S} (D : CommCircuit X Y sch) {m : ℕ} (outs : Fin m → Out) :
    (d k : ℕ) → (hkd : k + d ≤ sch.steps) →
    (X → BitString (sch.spaceA ⟨k, by omega⟩)) →
    (Y → BitString (sch.spaceB ⟨k, by omega⟩)) →
    (X → BitString m) → Protocol X Y (BitString m)
  | 0, _, _, _, _, acc => Protocol.aliceSend m acc Protocol.output
  | d + 1, k, hkd, sA, sB, acc =>
    let t : Fin sch.steps := ⟨k, by omega⟩
    let sA' (b : Bool) : X → BitString (sch.spaceA ⟨k + 1, by omega⟩) :=
      fun x => D.nextA t x (sA x) b
    let sB' (b : Bool) : Y → BitString (sch.spaceB ⟨k + 1, by omega⟩) :=
      fun y => D.nextB t y (sB y) b
    match sch.kind t with
    | .aliceToBob =>
      Protocol.alice (fun x => D.sendA t x (sA x))
        (simSliceAliceAux D outs d (k + 1) (by omega) (sA' false) (sB' false) acc)
        (simSliceAliceAux D outs d (k + 1) (by omega) (sA' false) (sB' true) acc)
    | .bobToAlice =>
      Protocol.bob (fun y => D.sendB t y (sB y))
        (simSliceAliceAux D outs d (k + 1) (by omega) (sA' false) (sB' false) acc)
        (simSliceAliceAux D outs d (k + 1) (by omega) (sA' true) (sB' false) acc)
    | .emitAlice _ =>
      let acc' : X → BitString m := fun x i =>
        if sch.emitStep (outs i) = t then D.outA t x (sA x) else acc x i
      simSliceAliceAux D outs d (k + 1) (by omega) (sA' false) (sB' false) acc'
    | _ =>
      simSliceAliceAux D outs d (k + 1) (by omega) (sA' false) (sB' false) acc

private theorem depth_simSliceAliceAux_le {X Y Out : Type*} [DecidableEq Out] {S : ℕ}
    {sch : CommSchedule Out S} (D : CommCircuit X Y sch) {m : ℕ} (outs : Fin m → Out)
    (d k : ℕ) (hkd : k + d ≤ sch.steps)
    (sA : X → BitString (sch.spaceA ⟨k, by omega⟩))
    (sB : Y → BitString (sch.spaceB ⟨k, by omega⟩)) (acc : X → BitString m) :
    (simSliceAliceAux D outs d k hkd sA sB acc).depth ≤ commInSlice sch k (k + d) + m := by
  induction d generalizing k acc with
  | zero =>
    have h0 : commInSlice sch k (k + 0) = 0 := by
      unfold commInSlice; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro t _; omega
    rw [h0, zero_add]
    exact (Protocol.depth_aliceSend_le (d := 0) (fun _ => by simp)).trans (by omega)
  | succ d ih =>
    let t : Fin sch.steps := ⟨k, by omega⟩
    have hsplit : commInSlice sch k (k + (d + 1)) =
        (if sch.isCommStep t = true then 1 else 0) + commInSlice sch (k + 1) ((k + 1) + d) := by
      unfold commInSlice
      let S₁ := Finset.univ.filter fun s : Fin sch.steps =>
        k ≤ s.val ∧ s.val < k + (d + 1) ∧ sch.isCommStep s = true
      let S₂ := Finset.univ.filter fun s : Fin sch.steps =>
        k + 1 ≤ s.val ∧ s.val < (k + 1) + d ∧ sch.isCommStep s = true
      change S₁.card = (if sch.isCommStep t = true then 1 else 0) + S₂.card
      by_cases hc : sch.isCommStep t = true
      · have hEq : S₁ = insert t S₂ := by
          ext s
          simp only [S₁, S₂, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
            Fin.ext_iff, t]
          constructor
          · rintro ⟨h1, h2, h3⟩
            by_cases hsk : s.val = k
            · left; exact hsk
            · right; exact ⟨by omega, by omega, h3⟩
          · rintro (rfl | ⟨h1, h2, h3⟩)
            · exact ⟨le_rfl, by omega, hc⟩
            · exact ⟨by omega, by omega, h3⟩
        have hnot : t ∉ S₂ := by
          simp only [S₂, Finset.mem_filter, Finset.mem_univ, true_and, t]; omega
        rw [ite_eq_left hc, hEq, Finset.card_insert_of_notMem hnot]
        omega
      · have hEq : S₁ = S₂ := by
          ext s
          simp only [S₁, S₂, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨h1, h2, h3⟩
            have hne : s.val ≠ k := by
              intro heq
              have hst : s = t := Fin.ext heq
              exact hc (hst ▸ h3)
            exact ⟨by omega, by omega, h3⟩
          · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, by omega, h3⟩
        rw [ite_eq_right hc, zero_add, hEq]
    rw [hsplit]
    unfold simSliceAliceAux
    dsimp only
    let sA' (b : Bool) : X → BitString (sch.spaceA ⟨k + 1, by omega⟩) :=
      fun x => D.nextA t x (sA x) b
    let sB' (b : Bool) : Y → BitString (sch.spaceB ⟨k + 1, by omega⟩) :=
      fun y => D.nextB t y (sB y) b
    cases hkind : sch.kind ⟨k, by omega⟩ with
    | aliceToBob =>
      have hc : sch.isCommStep t = true := sch.isCommStep_of_aliceToBob hkind
      rw [ite_eq_left hc]
      simp only [Protocol.depth_alice]
      have h0 := ih (k + 1) (by omega) (sA' false) (sB' false) acc
      have h1 := ih (k + 1) (by omega) (sA' false) (sB' true) acc
      dsimp only [sA', sB', t] at h0 h1
      omega
    | bobToAlice =>
      have hc : sch.isCommStep t = true := sch.isCommStep_of_bobToAlice hkind
      rw [ite_eq_left hc]
      simp only [Protocol.depth_bob]
      have h0 := ih (k + 1) (by omega) (sA' false) (sB' false) acc
      have h1 := ih (k + 1) (by omega) (sA' true) (sB' false) acc
      dsimp only [sA', sB', t] at h0 h1
      omega
    | localStep =>
      have hc : ¬ sch.isCommStep t = true := by rw [sch.isCommStep_of_localStep hkind]; decide
      rw [ite_eq_right hc, zero_add]
      exact ih (k + 1) (by omega) _ _ acc
    | emitAlice _ =>
      have hc : ¬ sch.isCommStep t = true := by rw [sch.isCommStep_of_emitAlice hkind]; decide
      rw [ite_eq_right hc, zero_add]
      exact ih (k + 1) (by omega) _ _ _
    | emitBob _ =>
      have hc : ¬ sch.isCommStep t = true := by rw [sch.isCommStep_of_emitBob hkind]; decide
      rw [ite_eq_right hc, zero_add]
      exact ih (k + 1) (by omega) _ _ acc

private theorem run_simSliceAliceAux {X Y Out : Type*} [DecidableEq Out] {S : ℕ}
    {sch : CommSchedule Out S} (D : CommCircuit X Y sch) {m : ℕ} (outs : Fin m → Out)
    (x : X) (y : Y)
    (d k : ℕ) (hkd : k + d ≤ sch.steps)
    (sA : X → BitString (sch.spaceA ⟨k, by omega⟩))
    (sB : Y → BitString (sch.spaceB ⟨k, by omega⟩)) (acc : X → BitString m)
    (hsA : sA x = (D.stateAtNat x y k (by omega)).1)
    (hsB : sB y = (D.stateAtNat x y k (by omega)).2) :
    ∀ i : Fin m,
      (simSliceAliceAux D outs d k hkd sA sB acc).run x y i =
        if k ≤ (sch.emitStep (outs i)).val ∧ (sch.emitStep (outs i)).val < k + d ∧
            sch.kind (sch.emitStep (outs i)) = .emitAlice (outs i)
        then D.eval x y (outs i) else acc x i := by
  induction d generalizing k acc with
  | zero =>
    intro i
    simp only [simSliceAliceAux, Protocol.run_aliceSend, Protocol.run_output]
    have hnot : ¬ (k ≤ (sch.emitStep (outs i)).val ∧ (sch.emitStep (outs i)).val < k + 0 ∧
        sch.kind (sch.emitStep (outs i)) = .emitAlice (outs i)) := by omega
    rw [ite_eq_right hnot]
  | succ d ih =>
    intro i
    let t : Fin sch.steps := ⟨k, by omega⟩
    have hst_next : D.stateAtNat x y (k + 1) (by omega) =
        D.stepState x y t (D.stateAtNat x y k (by omega)) := rfl
    unfold simSliceAliceAux
    dsimp only
    cases hkind : sch.kind ⟨k, by omega⟩ with
    | aliceToBob =>
      simp only [Protocol.run_alice]
      have hstep : D.stateAtNat x y (k + 1) (by omega) =
          (D.nextA t x (sA x) false, D.nextB t y (sB y) (D.sendA t x (sA x))) := by
        rw [hst_next, D.stepState_of_aliceToBob x y hkind, hsA, hsB]
      have hne : sch.emitStep (outs i) ≠ t := by
        intro heq
        rcases sch.emitStep_spec (outs i) with h | h <;>
          rw [heq, show sch.kind t = .aliceToBob from hkind] at h <;> cases h
      have hne_val : (sch.emitStep (outs i)).val ≠ k := fun hv => hne (Fin.ext hv)
      cases hbit : D.sendA ⟨k, by omega⟩ x (sA x)
      · simp only [Bool.cond_false]
        rw [ih (k + 1) (by omega) _ _ acc
          (by rw [hstep]) (by rw [hstep]; dsimp only [t]; rw [hbit]) i]
        by_cases hc : k + 1 ≤ (sch.emitStep (outs i)).val ∧
            (sch.emitStep (outs i)).val < (k + 1) + d ∧
            sch.kind (sch.emitStep (outs i)) = .emitAlice (outs i)
        · rw [ite_eq_left hc, ite_eq_left ⟨by omega, by omega, hc.2.2⟩]
        · rw [ite_eq_right hc, ite_eq_right (fun h => hc ⟨by omega, by omega, h.2.2⟩)]
      · simp only [Bool.cond_true]
        rw [ih (k + 1) (by omega) _ _ acc
          (by rw [hstep]) (by rw [hstep]; dsimp only [t]; rw [hbit]) i]
        by_cases hc : k + 1 ≤ (sch.emitStep (outs i)).val ∧
            (sch.emitStep (outs i)).val < (k + 1) + d ∧
            sch.kind (sch.emitStep (outs i)) = .emitAlice (outs i)
        · rw [ite_eq_left hc, ite_eq_left ⟨by omega, by omega, hc.2.2⟩]
        · rw [ite_eq_right hc, ite_eq_right (fun h => hc ⟨by omega, by omega, h.2.2⟩)]
    | bobToAlice =>
      simp only [Protocol.run_bob]
      have hstep : D.stateAtNat x y (k + 1) (by omega) =
          (D.nextA t x (sA x) (D.sendB t y (sB y)), D.nextB t y (sB y) false) := by
        rw [hst_next, D.stepState_of_bobToAlice x y hkind, hsA, hsB]
      have hne : sch.emitStep (outs i) ≠ t := by
        intro heq
        rcases sch.emitStep_spec (outs i) with h | h <;>
          rw [heq, show sch.kind t = .bobToAlice from hkind] at h <;> cases h
      have hne_val : (sch.emitStep (outs i)).val ≠ k := fun hv => hne (Fin.ext hv)
      cases hbit : D.sendB ⟨k, by omega⟩ y (sB y)
      · simp only [Bool.cond_false]
        rw [ih (k + 1) (by omega) _ _ acc
          (by rw [hstep]; dsimp only [t]; rw [hbit]) (by rw [hstep]) i]
        by_cases hc : k + 1 ≤ (sch.emitStep (outs i)).val ∧
            (sch.emitStep (outs i)).val < (k + 1) + d ∧
            sch.kind (sch.emitStep (outs i)) = .emitAlice (outs i)
        · rw [ite_eq_left hc, ite_eq_left ⟨by omega, by omega, hc.2.2⟩]
        · rw [ite_eq_right hc, ite_eq_right (fun h => hc ⟨by omega, by omega, h.2.2⟩)]
      · simp only [Bool.cond_true]
        rw [ih (k + 1) (by omega) _ _ acc
          (by rw [hstep]; dsimp only [t]; rw [hbit]) (by rw [hstep]) i]
        by_cases hc : k + 1 ≤ (sch.emitStep (outs i)).val ∧
            (sch.emitStep (outs i)).val < (k + 1) + d ∧
            sch.kind (sch.emitStep (outs i)) = .emitAlice (outs i)
        · rw [ite_eq_left hc, ite_eq_left ⟨by omega, by omega, hc.2.2⟩]
        · rw [ite_eq_right hc, ite_eq_right (fun h => hc ⟨by omega, by omega, h.2.2⟩)]
    | localStep =>
      have hstep : D.stateAtNat x y (k + 1) (by omega) =
          (D.nextA t x (sA x) false, D.nextB t y (sB y) false) := by
        rw [hst_next, D.stepState_of_localStep x y hkind, hsA, hsB]
      have hne : sch.emitStep (outs i) ≠ t := by
        intro heq
        rcases sch.emitStep_spec (outs i) with h | h <;>
          rw [heq, show sch.kind t = .localStep from hkind] at h <;> cases h
      have hne_val : (sch.emitStep (outs i)).val ≠ k := fun hv => hne (Fin.ext hv)
      rw [ih (k + 1) (by omega) _ _ acc (by rw [hstep]) (by rw [hstep]) i]
      by_cases hc : k + 1 ≤ (sch.emitStep (outs i)).val ∧
          (sch.emitStep (outs i)).val < (k + 1) + d ∧
          sch.kind (sch.emitStep (outs i)) = .emitAlice (outs i)
      · rw [ite_eq_left hc, ite_eq_left ⟨by omega, by omega, hc.2.2⟩]
      · rw [ite_eq_right hc, ite_eq_right (fun h => hc ⟨by omega, by omega, h.2.2⟩)]
    | emitBob o =>
      have hstep : D.stateAtNat x y (k + 1) (by omega) =
          (D.nextA t x (sA x) false, D.nextB t y (sB y) false) := by
        rw [hst_next, D.stepState_of_emitBob x y hkind, hsA, hsB]
      rw [ih (k + 1) (by omega) _ _ acc (by rw [hstep]) (by rw [hstep]) i]
      by_cases heq : sch.emitStep (outs i) = t
      · have hnot1 : ¬ (k + 1 ≤ (sch.emitStep (outs i)).val ∧
            (sch.emitStep (outs i)).val < (k + 1) + d ∧
            sch.kind (sch.emitStep (outs i)) = .emitAlice (outs i)) := by
          rw [heq]; simp [t]
        have hnot2 : ¬ (k ≤ (sch.emitStep (outs i)).val ∧
            (sch.emitStep (outs i)).val < k + (d + 1) ∧
            sch.kind (sch.emitStep (outs i)) = .emitAlice (outs i)) := by
          rw [heq, show sch.kind t = .emitBob o from hkind]; rintro ⟨_, _, h⟩; cases h
        rw [ite_eq_right hnot1, ite_eq_right hnot2]
      · have hne_val : (sch.emitStep (outs i)).val ≠ k := fun hv => heq (Fin.ext hv)
        by_cases hc : k + 1 ≤ (sch.emitStep (outs i)).val ∧
            (sch.emitStep (outs i)).val < (k + 1) + d ∧
            sch.kind (sch.emitStep (outs i)) = .emitAlice (outs i)
        · rw [ite_eq_left hc, ite_eq_left ⟨by omega, by omega, hc.2.2⟩]
        · rw [ite_eq_right hc, ite_eq_right (fun h => hc ⟨by omega, by omega, h.2.2⟩)]
    | emitAlice o =>
      have hstep : D.stateAtNat x y (k + 1) (by omega) =
          (D.nextA t x (sA x) false, D.nextB t y (sB y) false) := by
        rw [hst_next, D.stepState_of_emitAlice x y hkind, hsA, hsB]
      rw [ih (k + 1) (by omega) _ _ _ (by rw [hstep]) (by rw [hstep]) i]
      by_cases heq : sch.emitStep (outs i) = t
      · have hnot1 : ¬ (k + 1 ≤ (sch.emitStep (outs i)).val ∧
            (sch.emitStep (outs i)).val < (k + 1) + d ∧
            sch.kind (sch.emitStep (outs i)) = .emitAlice (outs i)) := by
          rw [heq]; simp [t]
        have ho_eq : o = outs i := by
          rcases sch.emitStep_spec (outs i) with h | h
          · rw [heq, show sch.kind t = .emitAlice o from hkind] at h
            exact CommStepKind.emitAlice.inj h
          · rw [heq, show sch.kind t = .emitAlice o from hkind] at h; cases h
        have hcond : k ≤ (sch.emitStep (outs i)).val ∧
            (sch.emitStep (outs i)).val < k + (d + 1) ∧
            sch.kind (sch.emitStep (outs i)) = .emitAlice (outs i) := by
          rw [heq, show sch.kind t = .emitAlice o from hkind, ho_eq]
          exact ⟨le_rfl, by dsimp only [t]; omega, rfl⟩
        rw [ite_eq_right hnot1, ite_eq_left heq, ite_eq_left hcond]
        have hke : sch.kind (sch.emitStep (outs i)) = .emitAlice o := by
          rw [heq]; exact hkind
        rw [D.eval_of_emitAlice x y hke, heq, D.stateAt_eq_stateAtNat]
        simp only [Fin.val_castSucc, t]
        rw [hsA]
      · have hne_val : (sch.emitStep (outs i)).val ≠ k := fun hv => heq (Fin.ext hv)
        by_cases hc : k + 1 ≤ (sch.emitStep (outs i)).val ∧
            (sch.emitStep (outs i)).val < (k + 1) + d ∧
            sch.kind (sch.emitStep (outs i)) = .emitAlice (outs i)
        · rw [ite_eq_left hc, ite_eq_left ⟨by omega, by omega, hc.2.2⟩]
        · rw [ite_eq_right hc, ite_eq_right heq,
            ite_eq_right (fun h => hc ⟨by omega, by omega, h.2.2⟩)]

/-- Symmetric simulation when Bob emits outputs `outs : Fin m → Out` inside steps `[k, k + d)`. -/
private def simSliceBobAux {X Y Out : Type*} [DecidableEq Out] {S : ℕ}
    {sch : CommSchedule Out S} (D : CommCircuit X Y sch) {m : ℕ} (outs : Fin m → Out) :
    (d k : ℕ) → (hkd : k + d ≤ sch.steps) →
    (X → BitString (sch.spaceA ⟨k, by omega⟩)) →
    (Y → BitString (sch.spaceB ⟨k, by omega⟩)) →
    (Y → BitString m) → Protocol X Y (BitString m)
  | 0, _, _, _, _, acc => Protocol.bobSend m acc Protocol.output
  | d + 1, k, hkd, sA, sB, acc =>
    let t : Fin sch.steps := ⟨k, by omega⟩
    let sA' (b : Bool) : X → BitString (sch.spaceA ⟨k + 1, by omega⟩) :=
      fun x => D.nextA t x (sA x) b
    let sB' (b : Bool) : Y → BitString (sch.spaceB ⟨k + 1, by omega⟩) :=
      fun y => D.nextB t y (sB y) b
    match sch.kind t with
    | .aliceToBob =>
      Protocol.alice (fun x => D.sendA t x (sA x))
        (simSliceBobAux D outs d (k + 1) (by omega) (sA' false) (sB' false) acc)
        (simSliceBobAux D outs d (k + 1) (by omega) (sA' false) (sB' true) acc)
    | .bobToAlice =>
      Protocol.bob (fun y => D.sendB t y (sB y))
        (simSliceBobAux D outs d (k + 1) (by omega) (sA' false) (sB' false) acc)
        (simSliceBobAux D outs d (k + 1) (by omega) (sA' true) (sB' false) acc)
    | .emitBob _ =>
      let acc' : Y → BitString m := fun y i =>
        if sch.emitStep (outs i) = t then D.outB t y (sB y) else acc y i
      simSliceBobAux D outs d (k + 1) (by omega) (sA' false) (sB' false) acc'
    | _ =>
      simSliceBobAux D outs d (k + 1) (by omega) (sA' false) (sB' false) acc

private theorem depth_simSliceBobAux_le {X Y Out : Type*} [DecidableEq Out] {S : ℕ}
    {sch : CommSchedule Out S} (D : CommCircuit X Y sch) {m : ℕ} (outs : Fin m → Out)
    (d k : ℕ) (hkd : k + d ≤ sch.steps)
    (sA : X → BitString (sch.spaceA ⟨k, by omega⟩))
    (sB : Y → BitString (sch.spaceB ⟨k, by omega⟩)) (acc : Y → BitString m) :
    (simSliceBobAux D outs d k hkd sA sB acc).depth ≤ commInSlice sch k (k + d) + m := by
  induction d generalizing k acc with
  | zero =>
    have h0 : commInSlice sch k (k + 0) = 0 := by
      unfold commInSlice; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro t _; omega
    rw [h0, zero_add]
    exact (Protocol.depth_bobSend_le (d := 0) (fun _ => by simp)).trans (by omega)
  | succ d ih =>
    let t : Fin sch.steps := ⟨k, by omega⟩
    have hsplit : commInSlice sch k (k + (d + 1)) =
        (if sch.isCommStep t = true then 1 else 0) + commInSlice sch (k + 1) ((k + 1) + d) := by
      unfold commInSlice
      let S₁ := Finset.univ.filter fun s : Fin sch.steps =>
        k ≤ s.val ∧ s.val < k + (d + 1) ∧ sch.isCommStep s = true
      let S₂ := Finset.univ.filter fun s : Fin sch.steps =>
        k + 1 ≤ s.val ∧ s.val < (k + 1) + d ∧ sch.isCommStep s = true
      change S₁.card = (if sch.isCommStep t = true then 1 else 0) + S₂.card
      by_cases hc : sch.isCommStep t = true
      · have hEq : S₁ = insert t S₂ := by
          ext s
          simp only [S₁, S₂, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
            Fin.ext_iff, t]
          constructor
          · rintro ⟨h1, h2, h3⟩
            by_cases hsk : s.val = k
            · left; exact hsk
            · right; exact ⟨by omega, by omega, h3⟩
          · rintro (rfl | ⟨h1, h2, h3⟩)
            · exact ⟨le_rfl, by omega, hc⟩
            · exact ⟨by omega, by omega, h3⟩
        have hnot : t ∉ S₂ := by
          simp only [S₂, Finset.mem_filter, Finset.mem_univ, true_and, t]; omega
        rw [ite_eq_left hc, hEq, Finset.card_insert_of_notMem hnot]
        omega
      · have hEq : S₁ = S₂ := by
          ext s
          simp only [S₁, S₂, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨h1, h2, h3⟩
            have hne : s.val ≠ k := by
              intro heq
              have hst : s = t := Fin.ext heq
              exact hc (hst ▸ h3)
            exact ⟨by omega, by omega, h3⟩
          · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, by omega, h3⟩
        rw [ite_eq_right hc, zero_add, hEq]
    rw [hsplit]
    unfold simSliceBobAux
    dsimp only
    let sA' (b : Bool) : X → BitString (sch.spaceA ⟨k + 1, by omega⟩) :=
      fun x => D.nextA t x (sA x) b
    let sB' (b : Bool) : Y → BitString (sch.spaceB ⟨k + 1, by omega⟩) :=
      fun y => D.nextB t y (sB y) b
    cases hkind : sch.kind ⟨k, by omega⟩ with
    | aliceToBob =>
      have hc : sch.isCommStep t = true := sch.isCommStep_of_aliceToBob hkind
      rw [ite_eq_left hc]; simp only [Protocol.depth_alice]
      have h0 := ih (k + 1) (by omega) (sA' false) (sB' false) acc
      have h1 := ih (k + 1) (by omega) (sA' false) (sB' true) acc
      dsimp only [sA', sB', t] at h0 h1
      omega
    | bobToAlice =>
      have hc : sch.isCommStep t = true := sch.isCommStep_of_bobToAlice hkind
      rw [ite_eq_left hc]; simp only [Protocol.depth_bob]
      have h0 := ih (k + 1) (by omega) (sA' false) (sB' false) acc
      have h1 := ih (k + 1) (by omega) (sA' true) (sB' false) acc
      dsimp only [sA', sB', t] at h0 h1
      omega
    | localStep =>
      have hc : ¬ sch.isCommStep t = true := by rw [sch.isCommStep_of_localStep hkind]; decide
      rw [ite_eq_right hc, zero_add]; exact ih (k + 1) (by omega) _ _ acc
    | emitAlice _ =>
      have hc : ¬ sch.isCommStep t = true := by rw [sch.isCommStep_of_emitAlice hkind]; decide
      rw [ite_eq_right hc, zero_add]; exact ih (k + 1) (by omega) _ _ acc
    | emitBob _ =>
      have hc : ¬ sch.isCommStep t = true := by rw [sch.isCommStep_of_emitBob hkind]; decide
      rw [ite_eq_right hc, zero_add]; exact ih (k + 1) (by omega) _ _ _

private theorem run_simSliceBobAux {X Y Out : Type*} [DecidableEq Out] {S : ℕ}
    {sch : CommSchedule Out S} (D : CommCircuit X Y sch) {m : ℕ} (outs : Fin m → Out)
    (x : X) (y : Y)
    (d k : ℕ) (hkd : k + d ≤ sch.steps)
    (sA : X → BitString (sch.spaceA ⟨k, by omega⟩))
    (sB : Y → BitString (sch.spaceB ⟨k, by omega⟩)) (acc : Y → BitString m)
    (hsA : sA x = (D.stateAtNat x y k (by omega)).1)
    (hsB : sB y = (D.stateAtNat x y k (by omega)).2) :
    ∀ i : Fin m,
      (simSliceBobAux D outs d k hkd sA sB acc).run x y i =
        if k ≤ (sch.emitStep (outs i)).val ∧ (sch.emitStep (outs i)).val < k + d ∧
            sch.kind (sch.emitStep (outs i)) = .emitBob (outs i)
        then D.eval x y (outs i) else acc y i := by
  induction d generalizing k acc with
  | zero =>
    intro i
    simp only [simSliceBobAux, Protocol.run_bobSend, Protocol.run_output]
    have hnot : ¬ (k ≤ (sch.emitStep (outs i)).val ∧ (sch.emitStep (outs i)).val < k + 0 ∧
        sch.kind (sch.emitStep (outs i)) = .emitBob (outs i)) := by omega
    rw [ite_eq_right hnot]
  | succ d ih =>
    intro i
    let t : Fin sch.steps := ⟨k, by omega⟩
    have hst_next : D.stateAtNat x y (k + 1) (by omega) =
        D.stepState x y t (D.stateAtNat x y k (by omega)) := rfl
    unfold simSliceBobAux
    dsimp only
    cases hkind : sch.kind ⟨k, by omega⟩ with
    | aliceToBob =>
      simp only [Protocol.run_alice]
      have hstep : D.stateAtNat x y (k + 1) (by omega) =
          (D.nextA t x (sA x) false, D.nextB t y (sB y) (D.sendA t x (sA x))) := by
        rw [hst_next, D.stepState_of_aliceToBob x y hkind, hsA, hsB]
      have hne : sch.emitStep (outs i) ≠ t := by
        intro heq
        rcases sch.emitStep_spec (outs i) with h | h <;>
          rw [heq, show sch.kind t = .aliceToBob from hkind] at h <;> cases h
      have hne_val : (sch.emitStep (outs i)).val ≠ k := fun hv => hne (Fin.ext hv)
      cases hbit : D.sendA ⟨k, by omega⟩ x (sA x)
      · simp only [Bool.cond_false]
        rw [ih (k + 1) (by omega) _ _ acc
          (by rw [hstep]) (by rw [hstep]; dsimp only [t]; rw [hbit]) i]
        by_cases hc : k + 1 ≤ (sch.emitStep (outs i)).val ∧
            (sch.emitStep (outs i)).val < (k + 1) + d ∧
            sch.kind (sch.emitStep (outs i)) = .emitBob (outs i)
        · rw [ite_eq_left hc, ite_eq_left ⟨by omega, by omega, hc.2.2⟩]
        · rw [ite_eq_right hc, ite_eq_right (fun h => hc ⟨by omega, by omega, h.2.2⟩)]
      · simp only [Bool.cond_true]
        rw [ih (k + 1) (by omega) _ _ acc
          (by rw [hstep]) (by rw [hstep]; dsimp only [t]; rw [hbit]) i]
        by_cases hc : k + 1 ≤ (sch.emitStep (outs i)).val ∧
            (sch.emitStep (outs i)).val < (k + 1) + d ∧
            sch.kind (sch.emitStep (outs i)) = .emitBob (outs i)
        · rw [ite_eq_left hc, ite_eq_left ⟨by omega, by omega, hc.2.2⟩]
        · rw [ite_eq_right hc, ite_eq_right (fun h => hc ⟨by omega, by omega, h.2.2⟩)]
    | bobToAlice =>
      simp only [Protocol.run_bob]
      have hstep : D.stateAtNat x y (k + 1) (by omega) =
          (D.nextA t x (sA x) (D.sendB t y (sB y)), D.nextB t y (sB y) false) := by
        rw [hst_next, D.stepState_of_bobToAlice x y hkind, hsA, hsB]
      have hne : sch.emitStep (outs i) ≠ t := by
        intro heq
        rcases sch.emitStep_spec (outs i) with h | h <;>
          rw [heq, show sch.kind t = .bobToAlice from hkind] at h <;> cases h
      have hne_val : (sch.emitStep (outs i)).val ≠ k := fun hv => hne (Fin.ext hv)
      cases hbit : D.sendB ⟨k, by omega⟩ y (sB y)
      · simp only [Bool.cond_false]
        rw [ih (k + 1) (by omega) _ _ acc
          (by rw [hstep]; dsimp only [t]; rw [hbit]) (by rw [hstep]) i]
        by_cases hc : k + 1 ≤ (sch.emitStep (outs i)).val ∧
            (sch.emitStep (outs i)).val < (k + 1) + d ∧
            sch.kind (sch.emitStep (outs i)) = .emitBob (outs i)
        · rw [ite_eq_left hc, ite_eq_left ⟨by omega, by omega, hc.2.2⟩]
        · rw [ite_eq_right hc, ite_eq_right (fun h => hc ⟨by omega, by omega, h.2.2⟩)]
      · simp only [Bool.cond_true]
        rw [ih (k + 1) (by omega) _ _ acc
          (by rw [hstep]; dsimp only [t]; rw [hbit]) (by rw [hstep]) i]
        by_cases hc : k + 1 ≤ (sch.emitStep (outs i)).val ∧
            (sch.emitStep (outs i)).val < (k + 1) + d ∧
            sch.kind (sch.emitStep (outs i)) = .emitBob (outs i)
        · rw [ite_eq_left hc, ite_eq_left ⟨by omega, by omega, hc.2.2⟩]
        · rw [ite_eq_right hc, ite_eq_right (fun h => hc ⟨by omega, by omega, h.2.2⟩)]
    | localStep =>
      have hstep : D.stateAtNat x y (k + 1) (by omega) =
          (D.nextA t x (sA x) false, D.nextB t y (sB y) false) := by
        rw [hst_next, D.stepState_of_localStep x y hkind, hsA, hsB]
      have hne : sch.emitStep (outs i) ≠ t := by
        intro heq
        rcases sch.emitStep_spec (outs i) with h | h <;>
          rw [heq, show sch.kind t = .localStep from hkind] at h <;> cases h
      have hne_val : (sch.emitStep (outs i)).val ≠ k := fun hv => hne (Fin.ext hv)
      rw [ih (k + 1) (by omega) _ _ acc (by rw [hstep]) (by rw [hstep]) i]
      by_cases hc : k + 1 ≤ (sch.emitStep (outs i)).val ∧
          (sch.emitStep (outs i)).val < (k + 1) + d ∧
          sch.kind (sch.emitStep (outs i)) = .emitBob (outs i)
      · rw [ite_eq_left hc, ite_eq_left ⟨by omega, by omega, hc.2.2⟩]
      · rw [ite_eq_right hc, ite_eq_right (fun h => hc ⟨by omega, by omega, h.2.2⟩)]
    | emitAlice o =>
      have hstep : D.stateAtNat x y (k + 1) (by omega) =
          (D.nextA t x (sA x) false, D.nextB t y (sB y) false) := by
        rw [hst_next, D.stepState_of_emitAlice x y hkind, hsA, hsB]
      rw [ih (k + 1) (by omega) _ _ acc (by rw [hstep]) (by rw [hstep]) i]
      by_cases heq : sch.emitStep (outs i) = t
      · have hnot1 : ¬ (k + 1 ≤ (sch.emitStep (outs i)).val ∧
            (sch.emitStep (outs i)).val < (k + 1) + d ∧
            sch.kind (sch.emitStep (outs i)) = .emitBob (outs i)) := by
          rw [heq]; simp [t]
        have hnot2 : ¬ (k ≤ (sch.emitStep (outs i)).val ∧
            (sch.emitStep (outs i)).val < k + (d + 1) ∧
            sch.kind (sch.emitStep (outs i)) = .emitBob (outs i)) := by
          rw [heq, show sch.kind t = .emitAlice o from hkind]; rintro ⟨_, _, h⟩; cases h
        rw [ite_eq_right hnot1, ite_eq_right hnot2]
      · have hne_val : (sch.emitStep (outs i)).val ≠ k := fun hv => heq (Fin.ext hv)
        by_cases hc : k + 1 ≤ (sch.emitStep (outs i)).val ∧
            (sch.emitStep (outs i)).val < (k + 1) + d ∧
            sch.kind (sch.emitStep (outs i)) = .emitBob (outs i)
        · rw [ite_eq_left hc, ite_eq_left ⟨by omega, by omega, hc.2.2⟩]
        · rw [ite_eq_right hc, ite_eq_right (fun h => hc ⟨by omega, by omega, h.2.2⟩)]
    | emitBob o =>
      have hstep : D.stateAtNat x y (k + 1) (by omega) =
          (D.nextA t x (sA x) false, D.nextB t y (sB y) false) := by
        rw [hst_next, D.stepState_of_emitBob x y hkind, hsA, hsB]
      rw [ih (k + 1) (by omega) _ _ _ (by rw [hstep]) (by rw [hstep]) i]
      by_cases heq : sch.emitStep (outs i) = t
      · have hnot1 : ¬ (k + 1 ≤ (sch.emitStep (outs i)).val ∧
            (sch.emitStep (outs i)).val < (k + 1) + d ∧
            sch.kind (sch.emitStep (outs i)) = .emitBob (outs i)) := by
          rw [heq]; simp [t]
        have ho_eq : o = outs i := by
          rcases sch.emitStep_spec (outs i) with h | h
          · rw [heq, show sch.kind t = .emitBob o from hkind] at h; cases h
          · rw [heq, show sch.kind t = .emitBob o from hkind] at h
            exact CommStepKind.emitBob.inj h
        have hcond : k ≤ (sch.emitStep (outs i)).val ∧
            (sch.emitStep (outs i)).val < k + (d + 1) ∧
            sch.kind (sch.emitStep (outs i)) = .emitBob (outs i) := by
          rw [heq, show sch.kind t = .emitBob o from hkind, ho_eq]
          exact ⟨le_rfl, by dsimp only [t]; omega, rfl⟩
        rw [ite_eq_right hnot1, ite_eq_left heq, ite_eq_left hcond]
        have hke : sch.kind (sch.emitStep (outs i)) = .emitBob o := by
          rw [heq]; exact hkind
        rw [D.eval_of_emitBob x y hke, heq, D.stateAt_eq_stateAtNat]
        simp only [Fin.val_castSucc, t]
        rw [hsB]
      · have hne_val : (sch.emitStep (outs i)).val ≠ k := fun hv => heq (Fin.ext hv)
        by_cases hc : k + 1 ≤ (sch.emitStep (outs i)).val ∧
            (sch.emitStep (outs i)).val < (k + 1) + d ∧
            sch.kind (sch.emitStep (outs i)) = .emitBob (outs i)
        · rw [ite_eq_left hc, ite_eq_left ⟨by omega, by omega, hc.2.2⟩]
        · rw [ite_eq_right hc, ite_eq_right heq,
            ite_eq_right (fun h => hc ⟨by omega, by omega, h.2.2⟩)]

/-- Given a slice `[a, a + d)` of a randomized communicating circuit `μ` solving `f` with error
`≤ ε` where one player (Alice or Bob) emits `m` outputs `outs : Fin m → Out`, guessing the
initial `≤ S`-bit register state uniformly produces a 2-party `PublicCoin` protocol computing
`fun x y i => f x y (outs i)` of depth `≤ commInSlice sch a (a + d) + m` and worst-case success
probability `≥ (1 - ε) * 2 ^ (-S)`. -/
private theorem slice_to_publicCoin {X Y Out : Type*} {S : ℕ}
    {sch : CommSchedule Out S} {μ : RandCommCircuit X Y sch} {ε : ℝ} {f : X → Y → Out → Bool}
    (hsolves : μ.Solves ε f)
    {a d m : ℕ} (had : a + d ≤ sch.steps) (outs : Fin m → Out)
    (houts :
      (∀ i, a ≤ (sch.emitStep (outs i)).val ∧ (sch.emitStep (outs i)).val < a + d ∧
        sch.kind (sch.emitStep (outs i)) = .emitAlice (outs i)) ∨
      (∀ i, a ≤ (sch.emitStep (outs i)).val ∧ (sch.emitStep (outs i)).val < a + d ∧
        sch.kind (sch.emitStep (outs i)) = .emitBob (outs i))) :
    ∃ ν : PublicCoin X Y (BitString m),
      ν.depth ≤ commInSlice sch a (a + d) + m ∧
      SolvesWithSuccess ν ((1 - ε) * (2 : ℝ) ^ (-(S : ℝ)))
        (fun x y v => (fun i => f x y (outs i)) = v) := by
  classical
  let R := BitString (sch.spaceA ⟨a, by omega⟩) × BitString (sch.spaceB ⟨a, by omega⟩)
  have hcardR : Fintype.card R = 2 ^ (sch.spaceA ⟨a, by omega⟩ + sch.spaceB ⟨a, by omega⟩) := by
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, Fintype.card_fin, pow_add]
  have hcardR_le : (Fintype.card R : ℝ) ≤ (2 : ℝ) ^ S := by
    rw [hcardR]; exact_mod_cast Nat.pow_le_pow_right (by norm_num) (sch.space_bound ⟨a, by omega⟩)
  let unifR : PMF R := Cslib.Probability.PMF.uniformOfFintype R
  have hunif_ge : ∀ r : R, ((2 : ℝ) ^ (-(S : ℝ))) ≤ (unifR r).toReal := by
    intro r
    rw [Cslib.Probability.PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      Real.rpow_neg zero_le_two, Real.rpow_natCast]
    exact inv_anti₀ (Nat.cast_pos.mpr Fintype.card_pos) hcardR_le
  -- Common builder given a family `sim : CommCircuit X Y sch → R → Protocol X Y (BitString m)`.
  have hbuild : ∀ (sim : CommCircuit X Y sch → R → Protocol X Y (BitString m)),
      (∀ D r, (sim D r).depth ≤ commInSlice sch a (a + d) + m) →
      (∀ D x y, D.eval x y = f x y →
        (sim D (D.stateAtNat x y a (by omega))).run x y = fun i => f x y (outs i)) →
      ∃ ν : PublicCoin X Y (BitString m),
        ν.depth ≤ commInSlice sch a (a + d) + m ∧
        SolvesWithSuccess ν ((1 - ε) * (2 : ℝ) ^ (-(S : ℝ)))
          (fun x y v => (fun i => f x y (outs i)) = v) := by
    intro sim hdepth_sim hrun_sim
    let ν : PublicCoin X Y (BitString m) := μ.bind fun D => unifR.map (sim D)
    refine ⟨ν, ?_, ?_⟩
    · rw [PublicCoin.depth_le_iff]
      intro p hp
      rw [PMF.mem_support_bind_iff] at hp
      obtain ⟨D, _, hpD⟩ := hp
      rw [PMF.support_map] at hpD
      obtain ⟨r, _, rfl⟩ := hpD
      exact_mod_cast hdepth_sim D r
    · intro x y
      rw [successProb_eq_toOuterMeasure]
      let E : Set (Protocol X Y (BitString m)) := {p | (fun i => f x y (outs i)) = p.run x y}
      have hENN : ENNReal.ofReal ((2 : ℝ) ^ (-(S : ℝ))) *
          μ.toOuterMeasure {D | D.eval x y = f x y} ≤ ν.toOuterMeasure E := by
        rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_left]
        refine tsum_le_tsum fun D => ?_
        by_cases hD : D.eval x y = f x y
        · rw [Set.indicator_of_mem hD, mul_comm]
          gcongr
          rw [PMF.toOuterMeasure_map_apply]
          have hmem : D.stateAtNat x y a (by omega) ∈ sim D ⁻¹' E := by
            change (fun i => f x y (outs i)) = (sim D (D.stateAtNat x y a (by omega))).run x y
            exact (hrun_sim D x y hD).symm
          have hpt : unifR (D.stateAtNat x y a (by omega)) ≤
              unifR.toOuterMeasure (sim D ⁻¹' E) := by
            rw [PMF.toOuterMeasure_apply]
            exact le_trans (le_of_eq (Set.indicator_of_mem hmem (⇑unifR)).symm)
              (le_tsum (fun r => (sim D ⁻¹' E).indicator (⇑unifR) r)
                (D.stateAtNat x y a (by omega)))
          refine le_trans ?_ hpt
          rw [← ENNReal.ofReal_toReal (PMF.apply_ne_top unifR _)]
          exact ENNReal.ofReal_le_ofReal (hunif_ge _)
        · rw [Set.indicator_of_notMem hD, mul_zero]; exact zero_le
      have htoReal := ENNReal.toReal_mono (ne_of_lt (lt_of_le_of_lt
        (Cslib.Probability.PMF.toOuterMeasure_le_one ν _) ENNReal.one_lt_top)) hENN
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at htoReal
      refine le_trans ?_ htoReal
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (hsolves.successProb_ge x y) (by positivity)
  rcases houts with hA | hB
  · refine hbuild
      (fun D r => simSliceAliceAux D outs d a had (fun _ => r.1) (fun _ => r.2) (fun _ _ => false))
      (fun D r => depth_simSliceAliceAux_le D outs d a had _ _ _) ?_
    intro D x y hD
    funext i
    rw [run_simSliceAliceAux D outs x y d a had _ _ _ rfl rfl i, ite_eq_left (hA i), hD]
  · refine hbuild
      (fun D r => simSliceBobAux D outs d a had (fun _ => r.1) (fun _ => r.2) (fun _ _ => false))
      (fun D r => depth_simSliceBobAux_le D outs d a had _ _ _) ?_
    intro D x y hD
    funext i
    rw [run_simSliceBobAux D outs x y d a had _ _ _ rfl rfl i, ite_eq_left (hB i), hD]

/-- Prefix count of crossing wires strictly before step `t`. -/
private def prefixComm {Out : Type*} {S : ℕ} (sch : CommSchedule Out S) (t : Fin sch.steps) : ℕ :=
  (Finset.univ.filter fun s : Fin sch.steps => s.val < t.val ∧ sch.isCommStep s = true).card

private theorem prefixComm_mono {Out : Type*} {S : ℕ} (sch : CommSchedule Out S)
    {s t : Fin sch.steps} (h : s.val ≤ t.val) :
    prefixComm sch s ≤ prefixComm sch t := by
  refine Finset.card_le_card fun u hu => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  exact ⟨lt_of_lt_of_le hu.1 h, hu.2⟩

private theorem prefixComm_strictMono_on_comm {Out : Type*} {S : ℕ} (sch : CommSchedule Out S)
    {s t : Fin sch.steps} (hlt : s.val < t.val) (hs : sch.isCommStep s = true) :
    prefixComm sch s < prefixComm sch t := by
  refine Finset.card_lt_card ⟨fun u hu => ?_, fun hsub => ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    exact ⟨lt_trans hu.1 hlt, hu.2⟩
  · have hmem : s ∈ Finset.univ.filter (fun u : Fin sch.steps =>
        u.val < t.val ∧ sch.isCommStep u = true) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, hs⟩
    have := hsub hmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact lt_irrefl _ this.1

/-- Partitioning `sch` by `prefixComm t / B` yields a contiguous slice `[a, a + d)` containing
at most `B` crossing wires and at least `|Out| / (C / B + 1)` outputs emitted by a single player
(either Alice or Bob). -/
private theorem exists_heavy_slice {Out : Type*} [Fintype Out] {S : ℕ}
    (sch : CommSchedule Out S) {B : ℕ} (hB : 1 ≤ B) (hOut : 1 ≤ Fintype.card Out) :
    ∃ (a d : ℕ) (_ : a + d ≤ sch.steps) (k₁ : ℕ) (outs : Fin k₁ → Out),
      Function.Injective outs ∧
      Fintype.card Out ≤ (sch.commCount / B + 1) * (2 * k₁) ∧
      commInSlice sch a (a + d) ≤ B ∧
      ((∀ i, a ≤ (sch.emitStep (outs i)).val ∧ (sch.emitStep (outs i)).val < a + d ∧
          sch.kind (sch.emitStep (outs i)) = .emitAlice (outs i)) ∨
       (∀ i, a ≤ (sch.emitStep (outs i)).val ∧ (sch.emitStep (outs i)).val < a + d ∧
          sch.kind (sch.emitStep (outs i)) = .emitBob (outs i))) := by
  classical
  let M := sch.commCount / B + 1
  have hbucket_lt : ∀ o : Out, prefixComm sch (sch.emitStep o) / B < M := by
    intro o
    have hle : prefixComm sch (sch.emitStep o) ≤ sch.commCount := by
      refine Finset.card_le_card fun s hs => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
      exact hs.2
    exact Nat.lt_succ_of_le (Nat.div_le_div_right hle)
  let bucket (j : Fin M) : Finset Out :=
    Finset.univ.filter fun o : Out => prefixComm sch (sch.emitStep o) / B = j.val
  have hsum_buckets : ∑ j : Fin M, (bucket j).card = Fintype.card Out := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext o
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, bucket, Finset.mem_filter,
        iff_true]
      exact ⟨⟨prefixComm sch (sch.emitStep o) / B, hbucket_lt o⟩, rfl⟩
    · intro j₁ _ j₂ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro o h1 h2
      simp only [bucket, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      exact hne (Fin.ext (h1.symm.trans h2))
  -- Pigeonhole: some bucket `j` has `Fintype.card Out ≤ M * (bucket j).card`.
  have hMpos : 0 < M := Nat.succ_pos _
  have hex_j : ∃ j : Fin M, Fintype.card Out ≤ M * (bucket j).card := by
    by_contra h
    push Not at h
    have hlt : ∑ j : Fin M, M * (bucket j).card < ∑ _j : Fin M, Fintype.card Out :=
      Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.mpr ⟨⟨0, hMpos⟩⟩) fun j _ => h j
    rw [← Finset.mul_sum, hsum_buckets, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨j, hj⟩ := hex_j
  have hbj_nonempty : (bucket j).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, Finset.card_empty, mul_zero] at hj
    omega
  -- Contiguous interval `[a, b)` spanning the steps of `bucket j`.
  let stepsJ : Finset ℕ := (bucket j).image fun o => (sch.emitStep o).val
  have hstepsJ_ne : stepsJ.Nonempty := hbj_nonempty.image _
  let a := stepsJ.min' hstepsJ_ne
  let maxS := stepsJ.max' hstepsJ_ne
  have ha_le : a ≤ maxS := Finset.min'_le _ _ (Finset.max'_mem stepsJ hstepsJ_ne)
  have hmax_lt : maxS < sch.steps := by
    obtain ⟨o, _, ho⟩ := Finset.mem_image.mp (Finset.max'_mem stepsJ hstepsJ_ne)
    dsimp only [maxS]; rw [← ho]; exact (sch.emitStep o).isLt
  let d := maxS + 1 - a
  have had : a + d ≤ sch.steps := by omega
  -- Every step `t` in `[a, a + d)` has `prefixComm sch t / B = j.val`.
  have hslice_bucket : ∀ t : Fin sch.steps, a ≤ t.val → t.val < a + d →
      prefixComm sch t / B = j.val := by
    intro t ht1 ht2
    obtain ⟨o₁, ho₁, ha_eq⟩ := Finset.mem_image.mp (Finset.min'_mem stepsJ hstepsJ_ne)
    obtain ⟨o₂, ho₂, hb_eq⟩ := Finset.mem_image.mp (Finset.max'_mem stepsJ hstepsJ_ne)
    have hlo : prefixComm sch (sch.emitStep o₁) ≤ prefixComm sch t :=
      prefixComm_mono sch (by omega)
    have hhi : prefixComm sch t ≤ prefixComm sch (sch.emitStep o₂) :=
      prefixComm_mono sch (by omega)
    have hj1 : prefixComm sch (sch.emitStep o₁) / B = j.val := (Finset.mem_filter.mp ho₁).2
    have hj2 : prefixComm sch (sch.emitStep o₂) / B = j.val := (Finset.mem_filter.mp ho₂).2
    have h1 := Nat.div_le_div_right (c := B) hlo
    have h2 := Nat.div_le_div_right (c := B) hhi
    omega
  -- Therefore `commInSlice sch a (a + d) ≤ B`.
  have hcomm_le : commInSlice sch a (a + d) ≤ B := by
    let CS := Finset.univ.filter fun t : Fin sch.steps =>
      a ≤ t.val ∧ t.val < a + d ∧ sch.isCommStep t = true
    have hinj : Set.InjOn (fun t : Fin sch.steps => prefixComm sch t - j.val * B) (CS : Set _) := by
      intro s hs t ht heq
      simp only [Finset.mem_coe, CS, Finset.mem_filter, Finset.mem_univ, true_and] at hs ht
      have hqs := hslice_bucket s hs.1 hs.2.1
      have hqt := hslice_bucket t ht.1 ht.2.1
      have hge_s : j.val * B ≤ prefixComm sch s := by
        rw [← hqs, mul_comm]; exact Nat.mul_div_le _ _
      have hge_t : j.val * B ≤ prefixComm sch t := by
        rw [← hqt, mul_comm]; exact Nat.mul_div_le _ _
      have hp_eq : prefixComm sch s = prefixComm sch t := by
        dsimp only at heq
        calc
          prefixComm sch s = (prefixComm sch s - j.val * B) + j.val * B :=
            (Nat.sub_add_cancel hge_s).symm
          _ = (prefixComm sch t - j.val * B) + j.val * B := by rw [heq]
          _ = prefixComm sch t := Nat.sub_add_cancel hge_t
      rcases lt_trichotomy s.val t.val with hlt | hEq | hgt
      · exact absurd hp_eq (ne_of_lt (prefixComm_strictMono_on_comm sch hlt hs.2.2))
      · exact Fin.ext hEq
      · exact absurd hp_eq.symm (ne_of_lt (prefixComm_strictMono_on_comm sch hgt ht.2.2))
    have hmaps : ∀ t ∈ CS, prefixComm sch t - j.val * B ∈ Finset.range B := by
      intro t ht
      simp only [CS, Finset.mem_filter, Finset.mem_univ, true_and] at ht
      have hqt := hslice_bucket t ht.1 ht.2.1
      rw [Finset.mem_range]
      have hdm := Nat.div_add_mod (prefixComm sch t) B
      have hmlt := Nat.mod_lt (prefixComm sch t) (by omega : 0 < B)
      rw [hqt] at hdm
      have hmul : B * j.val = j.val * B := mul_comm B j.val
      omega
    calc
      commInSlice sch a (a + d) = CS.card := rfl
      _ ≤ (Finset.range B).card := Finset.card_le_card_of_injOn _ hmaps hinj
      _ = B := Finset.card_range B
  -- Split `bucket j` into Alice-emitted and Bob-emitted outputs and take the larger half.
  let BA := (bucket j).filter fun o => sch.kind (sch.emitStep o) = .emitAlice o
  let BB := (bucket j).filter fun o => sch.kind (sch.emitStep o) = .emitBob o
  have hsplit_j : BA.card + BB.card = (bucket j).card := by
    have hdisj : Disjoint BA BB := by
      rw [Finset.disjoint_left]
      intro o h1 h2
      simp only [BA, BB, Finset.mem_filter] at h1 h2
      have hcontra := h1.2.symm.trans h2.2
      cases hcontra
    have hunion : BA ∪ BB = bucket j := by
      ext o
      simp only [BA, BB, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h; rcases sch.emitStep_spec o with hA | hB
        · exact Or.inl ⟨h, hA⟩
        · exact Or.inr ⟨h, hB⟩
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  by_cases hmaj : BB.card ≤ BA.card
  · let e := BA.equivFin
    refine ⟨a, d, had, BA.card, fun i => (e.symm i).1, ?_, ?_, hcomm_le, Or.inl ?_⟩
    · intro i₁ i₂ h
      exact e.symm.injective (Subtype.ext h)
    · have : (bucket j).card ≤ 2 * BA.card := by omega
      exact hj.trans (Nat.mul_le_mul_left M this)
    · intro i
      have hmem := (e.symm i).2
      have hbj : (e.symm i).1 ∈ bucket j := (Finset.mem_filter.mp hmem).1
      have hA : sch.kind (sch.emitStep (e.symm i).1) = .emitAlice (e.symm i).1 :=
        (Finset.mem_filter.mp hmem).2
      have hstep_mem : (sch.emitStep (e.symm i).1).val ∈ stepsJ :=
        Finset.mem_image.mpr ⟨_, hbj, rfl⟩
      exact ⟨Finset.min'_le _ _ hstep_mem,
        Nat.lt_of_le_of_lt (Finset.le_max' _ _ hstep_mem) (by omega), hA⟩
  · let e := BB.equivFin
    refine ⟨a, d, had, BB.card, fun i => (e.symm i).1, ?_, ?_, hcomm_le, Or.inr ?_⟩
    · intro i₁ i₂ h
      exact e.symm.injective (Subtype.ext h)
    · have : (bucket j).card ≤ 2 * BB.card := by omega
      exact hj.trans (Nat.mul_le_mul_left M this)
    · intro i
      have hmem := (e.symm i).2
      have hbj : (e.symm i).1 ∈ bucket j := (Finset.mem_filter.mp hmem).1
      have hB' : sch.kind (sch.emitStep (e.symm i).1) = .emitBob (e.symm i).1 :=
        (Finset.mem_filter.mp hmem).2
      have hstep_mem : (sch.emitStep (e.symm i).1).val ∈ stepsJ :=
        Finset.mem_image.mpr ⟨_, hbj, rfl⟩
      exact ⟨Finset.min'_le _ _ hstep_mem,
        Nat.lt_of_le_of_lt (Finset.le_max' _ _ hstep_mem) (by omega), hB'⟩

/-! ### Restriction Embeddings into `NDISJ_{N/m}^(m)` and Main Tradeoff Constant -/

/-- Explicit positive constant for Boolean matrix-product communication-space tradeoffs. -/
noncomputable def cCommSpace : ℝ := alphaNDisj * betaNDisj / 64

/-- `cCommSpace > 0`. -/
theorem cCommSpace_pos : 0 < cCommSpace := by
  unfold cCommSpace
  have := alphaNDisj_mem.1
  have := betaNDisj_mem.1
  positivity

/-- Given `m` distinct outputs of a bounded-error `PublicCoin` protocol on `boolMatVec N` (with
`1 ≤ m ≤ B ≤ β'' N / 4`), restrict inputs to `m` disjoint blocks of size `N / m` to apply the
strong direct product theorem `sdpt_ndisj_bound` and obtain `alphaNDisj * m ≤ 2 * S`. -/
private theorem slice_outputs_bound_mv {N S B m : ℕ} (hS : 1 ≤ S) (hB : 1 ≤ B)
    (hB_le : (B : ℝ) ≤ betaNDisj * (N : ℝ) / 4) (hm1 : 1 ≤ m) (hmB : m ≤ B)
    {outs : Fin m → Fin N} (houts_inj : Function.Injective outs)
    {ν : PublicCoin (Fin N → BitString N) (BitString N) (BitString m)}
    (hdepth : ν.depth ≤ B + m)
    (hsolves : SolvesWithSuccess ν ((2 / 3 : ℝ) * (2 : ℝ) ^ (-(S : ℝ)))
      (fun A b v => (fun i => boolMatVec N A b (outs i)) = v)) :
    alphaNDisj * (m : ℝ) ≤ 2 * (S : ℝ) := by
  classical
  have hBN : 4 * B ≤ N := by
    have h1 : (4 * B : ℝ) ≤ betaNDisj * (N : ℝ) := by linarith
    have h2 : betaNDisj * (N : ℝ) ≤ (N : ℝ) :=
      mul_le_of_le_one_left (Nat.cast_nonneg N) betaNDisj_mem.2
    exact_mod_cast h1.trans h2
  let q := N / m
  have hq1 : 1 ≤ q := Nat.div_pos (by omega) (by omega)
  have hmq_le : m * q ≤ N := Nat.mul_div_le N m
  -- Embed `m` instances of `BitString q` into `(A, b)`.
  let embA (x : Fin m → BitString q) : Fin N → BitString N := fun i j =>
    if hj : j.val < m * q then
      let r : Fin m :=
        ⟨j.val / q, (Nat.div_lt_iff_lt_mul (by omega)).mpr (by simpa [mul_comm] using hj)⟩
      if outs r = i then x r ⟨j.val % q, Nat.mod_lt _ (by omega)⟩ else false
    else false
  let embB (y : Fin m → BitString q) : BitString N := fun j =>
    if hj : j.val < m * q then
      let r : Fin m :=
        ⟨j.val / q, (Nat.div_lt_iff_lt_mul (by omega)).mpr (by simpa [mul_comm] using hj)⟩
      y r ⟨j.val % q, Nat.mod_lt _ (by omega)⟩
    else false
  have hemb_correct : ∀ x y r, boolMatVec N (embA x) (embB y) (outs r) = ndisjK q m x y r := by
    intro x y r
    rw [boolMatVec_apply, ndisjK_apply]
    rw [Bool.eq_iff_iff, ndisj_eq_true_iff_exists, ndisj_eq_true_iff_exists]
    constructor
    · rintro ⟨j, hA, hB'⟩
      by_cases hj : j.val < m * q
      · simp only [embA, embB, hj, ↓reduceDIte] at hA hB'
        split_ifs at hA with hr'
        have heq : (⟨j.val / q, (Nat.div_lt_iff_lt_mul hq1).mpr
            (by simpa [mul_comm] using hj)⟩ : Fin m) = r := houts_inj hr'
        refine ⟨⟨j.val % q, Nat.mod_lt _ hq1⟩, ?_, ?_⟩
        · exact heq ▸ hA
        · exact heq ▸ hB'
      · simp only [embA, hj, ↓reduceDIte] at hA; cases hA
    · rintro ⟨l, hx, hy⟩
      have hlt : r.val * q + l.val < m * q := by
        have h1 : (r.val + 1) * q ≤ m * q := Nat.mul_le_mul_right q r.isLt
        have : r.val * q + q ≤ m * q := by linarith
        omega
      let j : Fin N := ⟨r.val * q + l.val, lt_of_lt_of_le hlt hmq_le⟩
      have hj_lt : j.val < m * q := hlt
      have hdiv : j.val / q = r.val := by
        change (r.val * q + l.val) / q = r.val
        rw [mul_comm r.val q, Nat.mul_add_div hq1, Nat.div_eq_of_lt l.isLt, add_zero]
      have hmod : j.val % q = l.val := by
        change (r.val * q + l.val) % q = l.val
        rw [mul_comm r.val q, Nat.mul_add_mod, Nat.mod_eq_of_lt l.isLt]
      have hr_eq : (⟨j.val / q, (Nat.div_lt_iff_lt_mul hq1).mpr
          (by simpa [mul_comm] using hj_lt)⟩ : Fin m) = r := Fin.ext hdiv
      have hl_eq : (⟨j.val % q, Nat.mod_lt _ hq1⟩ : Fin q) = l := Fin.ext hmod
      refine ⟨j, ?_, ?_⟩
      · simp only [embA, hj_lt, ↓reduceDIte]
        rw [hr_eq, ite_eq_left rfl, hl_eq]; exact hx
      · simp only [embB, hj_lt, ↓reduceDIte]
        rw [hr_eq, hl_eq]; exact hy
  -- Pull back `ν` along `(embA, embB)`.
  let comapP (p : Protocol (Fin N → BitString N) (BitString N) (BitString m)) :
      Protocol (Fin m → BitString q) (Fin m → BitString q) (BitString m) :=
    p.comap embA embB
  let ν' : PublicCoin (Fin m → BitString q) (Fin m → BitString q) (BitString m) := ν.map comapP
  have hdepth' : ν'.depth ≤ (B + m : ℕ) := by
    rw [PublicCoin.depth_le_iff]
    intro p hp
    rw [PMF.support_map] at hp
    obtain ⟨p₀, hp₀, rfl⟩ := hp
    rw [show (comapP p₀).depth = p₀.depth from Protocol.depth_comap embA embB p₀]
    exact (PublicCoin.depth_le_depth hp₀).trans hdepth
  have hsolves' : SolvesWithSuccess ν' ((2 / 3 : ℝ) * (2 : ℝ) ^ (-(S : ℝ)))
      (fun x y v => ndisjK q m x y = v) := by
    intro x y
    rw [successProb_eq_toOuterMeasure, PMF.toOuterMeasure_map_apply]
    have hset : comapP ⁻¹' {p | ndisjK q m x y = p.run x y} =
        {p | (fun i => boolMatVec N (embA x) (embB y) (outs i)) = p.run (embA x) (embB y)} := by
      ext p
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, comapP, Protocol.run_comap]
      have hfun : (fun i => boolMatVec N (embA x) (embB y) (outs i)) = ndisjK q m x y :=
        funext (hemb_correct x y)
      rw [hfun]
    rw [hset]
    exact (successProb_eq_toOuterMeasure ν
      (fun A b v => (fun i => boolMatVec N A b (outs i)) = v) (embA x) (embB y)).symm ▸
      hsolves (embA x) (embB y)
  -- Check communication budget `B + m ≤ betaNDisj * m * q`.
  have hcomm_bd : ((B + m : ℕ) : ℝ) ≤ betaNDisj * (m : ℝ) * (q : ℝ) := by
    have hmq_ge : 3 * N ≤ 4 * (m * q) := by
      have hrem : N = m * q + N % m := (Nat.div_add_mod N m).symm
      have hlt : N % m < m := Nat.mod_lt N (by omega)
      omega
    have hmq_R : (3 / 4 : ℝ) * (N : ℝ) ≤ (m : ℝ) * (q : ℝ) := by
      have : (3 * (N : ℝ)) ≤ 4 * ((m : ℝ) * (q : ℝ)) := by exact_mod_cast hmq_ge
      linarith
    have hBm : ((B + m : ℕ) : ℝ) ≤ 2 * (B : ℝ) := by
      push_cast; linarith [show (m : ℝ) ≤ B by exact_mod_cast hmB]
    have hβ0 : 0 ≤ betaNDisj := betaNDisj_mem.1.le
    calc
      ((B + m : ℕ) : ℝ) ≤ 2 * (B : ℝ) := hBm
      _ ≤ 2 * (betaNDisj * (N : ℝ) / 4) := by linarith
      _ = betaNDisj * ((1 / 2 : ℝ) * (N : ℝ)) := by ring
      _ ≤ betaNDisj * ((3 / 4 : ℝ) * (N : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ hβ0; linarith [Nat.cast_nonneg (α := ℝ) N]
      _ ≤ betaNDisj * ((m : ℝ) * (q : ℝ)) := mul_le_mul_of_nonneg_left hmq_R hβ0
      _ = betaNDisj * (m : ℝ) * (q : ℝ) := by ring
  have hsdpt := sdpt_ndisj_bound hq1 hcomm_bd hdepth' hsolves'
  -- Deduce `2 ^ (-(S + 1)) ≤ 2 ^ (-alphaNDisj * m)`.
  have h2pow : (2 : ℝ) ^ (-((S : ℝ) + 1)) ≤ (2 : ℝ) ^ (-alphaNDisj * (m : ℝ)) := by
    have hhalf : (2 : ℝ) ^ (-((S : ℝ) + 1)) = (1 / 2 : ℝ) * (2 : ℝ) ^ (-(S : ℝ)) := by
      rw [neg_add, Real.rpow_add two_pos, mul_comm]
      norm_num
    rw [hhalf]
    exact le_trans (mul_le_mul_of_nonneg_right (by norm_num : (1 / 2 : ℝ) ≤ 2 / 3) (by positivity))
      hsdpt
  have hexp : -((S : ℝ) + 1) ≤ -alphaNDisj * (m : ℝ) :=
    (Real.rpow_le_rpow_left_iff one_lt_two).mp h2pow
  have hS1 : (1 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS
  linarith

/-- Symmetric `NDISJ_{N/m}^(m)` restriction bound for `boolMatMul N`. -/
private theorem slice_outputs_bound_mm {N S B m : ℕ} (hS : 1 ≤ S) (hB : 1 ≤ B)
    (hB_le : (B : ℝ) ≤ betaNDisj * (N : ℝ) / 4) (hm1 : 1 ≤ m) (hmB : m ≤ B)
    {outs : Fin m → Fin N × Fin N} (houts_inj : Function.Injective outs)
    {ν : PublicCoin (Fin N → BitString N) (Fin N → BitString N) (BitString m)}
    (hdepth : ν.depth ≤ B + m)
    (hsolves : SolvesWithSuccess ν ((2 / 3 : ℝ) * (2 : ℝ) ^ (-(S : ℝ)))
      (fun A B' v => (fun i => boolMatMul N A B' (outs i)) = v)) :
    alphaNDisj * (m : ℝ) ≤ 2 * (S : ℝ) := by
  classical
  have hBN : 4 * B ≤ N := by
    have h1 : (4 * B : ℝ) ≤ betaNDisj * (N : ℝ) := by linarith
    have h2 : betaNDisj * (N : ℝ) ≤ (N : ℝ) :=
      mul_le_of_le_one_left (Nat.cast_nonneg N) betaNDisj_mem.2
    exact_mod_cast h1.trans h2
  let q := N / m
  have hq1 : 1 ≤ q := Nat.div_pos (by omega) (by omega)
  have hmq_le : m * q ≤ N := Nat.mul_div_le N m
  -- Block `r` of coordinates `{0, ..., m * q - 1}` is assigned to output `outs r = (i_r, j_r)`.
  let embA (x : Fin m → BitString q) : Fin N → BitString N := fun i l =>
    if hl : l.val < m * q then
      let r : Fin m :=
        ⟨l.val / q, (Nat.div_lt_iff_lt_mul (by omega)).mpr (by simpa [mul_comm] using hl)⟩
      if (outs r).1 = i then x r ⟨l.val % q, Nat.mod_lt _ (by omega)⟩ else false
    else false
  let embB (y : Fin m → BitString q) : Fin N → BitString N := fun l j =>
    if hl : l.val < m * q then
      let r : Fin m :=
        ⟨l.val / q, (Nat.div_lt_iff_lt_mul (by omega)).mpr (by simpa [mul_comm] using hl)⟩
      if (outs r).2 = j then y r ⟨l.val % q, Nat.mod_lt _ (by omega)⟩ else false
    else false
  have hemb_correct : ∀ x y r, boolMatMul N (embA x) (embB y) (outs r) = ndisjK q m x y r := by
    intro x y r
    rw [boolMatMul_apply, ndisjK_apply]
    rw [Bool.eq_iff_iff, ndisj_eq_true_iff_exists, ndisj_eq_true_iff_exists]
    constructor
    · rintro ⟨l, hA, hB'⟩
      by_cases hl : l.val < m * q
      · simp only [embA, embB, hl, ↓reduceDIte] at hA hB'
        split_ifs at hA with h1
        split_ifs at hB' with h2
        have hr_eq : (⟨l.val / q, (Nat.div_lt_iff_lt_mul hq1).mpr
            (by simpa [mul_comm] using hl)⟩ : Fin m) = r := houts_inj (Prod.ext h1 h2)
        refine ⟨⟨l.val % q, Nat.mod_lt _ hq1⟩, ?_, ?_⟩
        · exact hr_eq ▸ hA
        · exact hr_eq ▸ hB'
      · simp only [embA, hl, ↓reduceDIte] at hA; cases hA
    · rintro ⟨t, hx, hy⟩
      have hlt : r.val * q + t.val < m * q := by
        have h1 : (r.val + 1) * q ≤ m * q := Nat.mul_le_mul_right q r.isLt
        have : r.val * q + q ≤ m * q := by linarith
        omega
      let l : Fin N := ⟨r.val * q + t.val, lt_of_lt_of_le hlt hmq_le⟩
      have hl_lt : l.val < m * q := hlt
      have hdiv : l.val / q = r.val := by
        change (r.val * q + t.val) / q = r.val
        rw [mul_comm r.val q, Nat.mul_add_div hq1, Nat.div_eq_of_lt t.isLt, add_zero]
      have hmod : l.val % q = t.val := by
        change (r.val * q + t.val) % q = t.val
        rw [mul_comm r.val q, Nat.mul_add_mod, Nat.mod_eq_of_lt t.isLt]
      have hr_eq : (⟨l.val / q, (Nat.div_lt_iff_lt_mul hq1).mpr
          (by simpa [mul_comm] using hl_lt)⟩ : Fin m) = r := Fin.ext hdiv
      have ht_eq : (⟨l.val % q, Nat.mod_lt _ hq1⟩ : Fin q) = t := Fin.ext hmod
      refine ⟨l, ?_, ?_⟩
      · simp only [embA, hl_lt, ↓reduceDIte]
        rw [hr_eq, ite_eq_left rfl, ht_eq]; exact hx
      · simp only [embB, hl_lt, ↓reduceDIte]
        rw [hr_eq, ite_eq_left rfl, ht_eq]; exact hy
  let comapP (p : Protocol (Fin N → BitString N) (Fin N → BitString N) (BitString m)) :
      Protocol (Fin m → BitString q) (Fin m → BitString q) (BitString m) :=
    p.comap embA embB
  let ν' : PublicCoin (Fin m → BitString q) (Fin m → BitString q) (BitString m) := ν.map comapP
  have hdepth' : ν'.depth ≤ (B + m : ℕ) := by
    rw [PublicCoin.depth_le_iff]
    intro p hp
    rw [PMF.support_map] at hp
    obtain ⟨p₀, hp₀, rfl⟩ := hp
    rw [show (comapP p₀).depth = p₀.depth from Protocol.depth_comap embA embB p₀]
    exact (PublicCoin.depth_le_depth hp₀).trans hdepth
  have hsolves' : SolvesWithSuccess ν' ((2 / 3 : ℝ) * (2 : ℝ) ^ (-(S : ℝ)))
      (fun x y v => ndisjK q m x y = v) := by
    intro x y
    rw [successProb_eq_toOuterMeasure, PMF.toOuterMeasure_map_apply]
    have hset : comapP ⁻¹' {p | ndisjK q m x y = p.run x y} =
        {p | (fun i => boolMatMul N (embA x) (embB y) (outs i)) = p.run (embA x) (embB y)} := by
      ext p
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, comapP, Protocol.run_comap]
      have hfun : (fun i => boolMatMul N (embA x) (embB y) (outs i)) = ndisjK q m x y :=
        funext (hemb_correct x y)
      rw [hfun]
    rw [hset]
    exact (successProb_eq_toOuterMeasure ν
      (fun A B' v => (fun i => boolMatMul N A B' (outs i)) = v) (embA x) (embB y)).symm ▸
      hsolves (embA x) (embB y)
  have hcomm_bd : ((B + m : ℕ) : ℝ) ≤ betaNDisj * (m : ℝ) * (q : ℝ) := by
    have hmq_ge : 3 * N ≤ 4 * (m * q) := by
      have hrem : N = m * q + N % m := (Nat.div_add_mod N m).symm
      have hlt : N % m < m := Nat.mod_lt N (by omega)
      omega
    have hmq_R : (3 / 4 : ℝ) * (N : ℝ) ≤ (m : ℝ) * (q : ℝ) := by
      have : (3 * (N : ℝ)) ≤ 4 * ((m : ℝ) * (q : ℝ)) := by exact_mod_cast hmq_ge
      linarith
    have hBm : ((B + m : ℕ) : ℝ) ≤ 2 * (B : ℝ) := by
      push_cast; linarith [show (m : ℝ) ≤ B by exact_mod_cast hmB]
    have hβ0 : 0 ≤ betaNDisj := betaNDisj_mem.1.le
    calc
      ((B + m : ℕ) : ℝ) ≤ 2 * (B : ℝ) := hBm
      _ ≤ 2 * (betaNDisj * (N : ℝ) / 4) := by linarith
      _ = betaNDisj * ((1 / 2 : ℝ) * (N : ℝ)) := by ring
      _ ≤ betaNDisj * ((3 / 4 : ℝ) * (N : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ hβ0; linarith [Nat.cast_nonneg (α := ℝ) N]
      _ ≤ betaNDisj * ((m : ℝ) * (q : ℝ)) := mul_le_mul_of_nonneg_left hmq_R hβ0
      _ = betaNDisj * (m : ℝ) * (q : ℝ) := by ring
  have hsdpt := sdpt_ndisj_bound hq1 hcomm_bd hdepth' hsolves'
  have h2pow : (2 : ℝ) ^ (-((S : ℝ) + 1)) ≤ (2 : ℝ) ^ (-alphaNDisj * (m : ℝ)) := by
    have hhalf : (2 : ℝ) ^ (-((S : ℝ) + 1)) = (1 / 2 : ℝ) * (2 : ℝ) ^ (-(S : ℝ)) := by
      rw [neg_add, Real.rpow_add two_pos, mul_comm]
      norm_num
    rw [hhalf]
    exact le_trans (mul_le_mul_of_nonneg_right (by norm_num : (1 / 2 : ℝ) ≤ 2 / 3) (by positivity))
      hsdpt
  have hexp : -((S : ℝ) + 1) ≤ -alphaNDisj * (m : ℝ) :=
    (Real.rpow_le_rpow_left_iff one_lt_two).mp h2pow
  have hS1 : (1 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS
  linarith

/-- Unified arithmetic finisher combining the slice output bound with the unconstrained bound
`|Out| ≤ 4 C` and `1 ≤ S`. -/
private theorem comm_space_combine {N OutCard C S : ℕ} (hN : 1 ≤ N) (hOut_ge_N : N ≤ OutCard)
    (hS : 1 ≤ S) (hC : OutCard ≤ 4 * C)
    (hslice : ∀ B : ℕ, 1 ≤ B → (B : ℝ) ≤ betaNDisj * (N : ℝ) / 4 →
      ∃ k₁ : ℕ, OutCard ≤ (C / B + 1) * (2 * k₁) ∧
        alphaNDisj * ((min k₁ B : ℕ) : ℝ) ≤ 2 * (S : ℝ)) :
    cCommSpace * (N : ℝ) * (OutCard : ℝ) ≤ (C : ℝ) * (S : ℝ) := by
  have hα0 := alphaNDisj_mem.1
  have hα1 := alphaNDisj_mem.2
  have hβ0 := betaNDisj_mem.1
  have hβ1 := betaNDisj_mem.2
  have hCR : (OutCard : ℝ) / 4 ≤ (C : ℝ) := by
    have : (OutCard : ℝ) ≤ 4 * (C : ℝ) := by exact_mod_cast hC
    linarith
  have hSR : (1 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS
  have hNR : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hOutR : (0 : ℝ) ≤ (OutCard : ℝ) := Nat.cast_nonneg OutCard
  let B := Nat.floor (betaNDisj * (N : ℝ) / 4)
  by_cases hB0 : B = 0
  · -- Small `N`: `betaNDisj * N / 4 < 1`, so `cCommSpace * N * OutCard ≤ OutCard / 4 ≤ C * S`.
    have hN_lt : betaNDisj * (N : ℝ) / 4 < 1 := by
      have h1 := Nat.lt_floor_add_one (betaNDisj * (N : ℝ) / 4)
      dsimp only [B] at hB0
      rw [hB0] at h1
      simpa using h1
    have hfactor : cCommSpace * (N : ℝ) ≤ 1 / 4 := by
      unfold cCommSpace
      nlinarith
    calc
      cCommSpace * (N : ℝ) * (OutCard : ℝ)
        ≤ (1 / 4 : ℝ) * (OutCard : ℝ) := mul_le_mul_of_nonneg_right hfactor hOutR
      _ = (OutCard : ℝ) / 4 := by ring
      _ ≤ (C : ℝ) * 1 := by linarith
      _ ≤ (C : ℝ) * (S : ℝ) := mul_le_mul_of_nonneg_left hSR (by positivity)
  · have hB1 : 1 ≤ B := Nat.pos_of_ne_zero hB0
    have hB_le : (B : ℝ) ≤ betaNDisj * (N : ℝ) / 4 :=
      Nat.floor_le (by positivity)
    have hB_ge : betaNDisj * (N : ℝ) / 8 ≤ (B : ℝ) := by
      have h1 := Nat.lt_floor_add_one (betaNDisj * (N : ℝ) / 4)
      have hB1R : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB1
      dsimp only [B]
      linarith
    obtain ⟨k₁, hk₁_cover, hm_bd⟩ := hslice B hB1 hB_le
    by_cases hmin : B ≤ k₁
    · -- `min k₁ B = B`, so `S ≥ (α'' β'' / 16) * N`.
      rw [min_eq_right hmin] at hm_bd
      have hS_ge : alphaNDisj * betaNDisj / 16 * (N : ℝ) ≤ (S : ℝ) := by nlinarith
      calc
        cCommSpace * (N : ℝ) * (OutCard : ℝ)
          = ((OutCard : ℝ) / 4) * (alphaNDisj * betaNDisj / 16 * (N : ℝ)) := by
            unfold cCommSpace; ring
        _ ≤ (C : ℝ) * (S : ℝ) :=
            mul_le_mul hCR hS_ge (by positivity) (by positivity)
    · -- `min k₁ B = k₁`, so `alphaNDisj * k₁ ≤ 2 * S`.
      rw [min_eq_left (Nat.le_of_not_ge hmin)] at hm_bd
      by_cases hCB : B ≤ C
      · -- `C / B + 1 ≤ 2 * C / B`.
        have hM_le : ((C / B + 1 : ℕ) : ℝ) ≤ 2 * (C : ℝ) / (B : ℝ) := by
          have hdiv : ((C / B : ℕ) : ℝ) ≤ (C : ℝ) / (B : ℝ) := by
            rw [le_div_iff₀ (by positivity : (0 : ℝ) < (B : ℝ))]
            exact_mod_cast Nat.div_mul_le_self C B
          have h1le : (1 : ℝ) ≤ (C : ℝ) / (B : ℝ) := by
            rw [le_div_iff₀ (by positivity : (0 : ℝ) < (B : ℝ)), one_mul]
            exact_mod_cast hCB
          push_cast; rw [mul_div_assoc]; linarith
        have hcoverR : (OutCard : ℝ) ≤ ((C / B + 1 : ℕ) : ℝ) * (2 * (k₁ : ℝ)) := by
          exact_mod_cast hk₁_cover
        have h1 : alphaNDisj * (B : ℝ) * (OutCard : ℝ) ≤ 8 * (C : ℝ) * (S : ℝ) := by
          have hBpos : (0 : ℝ) < (B : ℝ) := by positivity
          have hk1_nonneg : (0 : ℝ) ≤ (k₁ : ℝ) := Nat.cast_nonneg k₁
          have hstep1 : (OutCard : ℝ) ≤ (2 * (C : ℝ) / (B : ℝ)) * (2 * (k₁ : ℝ)) :=
            hcoverR.trans (mul_le_mul_of_nonneg_right hM_le (by positivity))
          have hstep2 : (B : ℝ) * (OutCard : ℝ) ≤ 4 * (C : ℝ) * (k₁ : ℝ) := by
            have := mul_le_mul_of_nonneg_left hstep1 hBpos.le
            have heq : (B : ℝ) * ((2 * (C : ℝ) / (B : ℝ)) * (2 * (k₁ : ℝ))) =
                4 * (C : ℝ) * (k₁ : ℝ) := by field_simp; ring
            linarith
          have hstep3 : alphaNDisj * ((B : ℝ) * (OutCard : ℝ)) ≤
              4 * (C : ℝ) * (alphaNDisj * (k₁ : ℝ)) := by
            have := mul_le_mul_of_nonneg_left hstep2 hα0.le
            linarith
          have hstep4 : 4 * (C : ℝ) * (alphaNDisj * (k₁ : ℝ)) ≤ 4 * (C : ℝ) * (2 * (S : ℝ)) :=
            mul_le_mul_of_nonneg_left hm_bd (by positivity)
          linarith
        calc
          cCommSpace * (N : ℝ) * (OutCard : ℝ)
            = (alphaNDisj / 8) * (betaNDisj * (N : ℝ) / 8) * (OutCard : ℝ) := by
              unfold cCommSpace; ring
          _ ≤ (alphaNDisj / 8) * (B : ℝ) * (OutCard : ℝ) := by
              apply mul_le_mul_of_nonneg_right _ hOutR
              exact mul_le_mul_of_nonneg_left hB_ge (by positivity)
          _ ≤ (C : ℝ) * (S : ℝ) := by linarith
      · -- `C < B`, so `C / B = 0`, `OutCard ≤ 2 * k₁`, hence `alphaNDisj * OutCard ≤ 4 * S`.
        have hCdiv : C / B = 0 := Nat.div_eq_of_lt (Nat.lt_of_not_ge hCB)
        rw [hCdiv, zero_add, one_mul] at hk₁_cover
        have hOut_le : (OutCard : ℝ) ≤ 2 * (k₁ : ℝ) := by exact_mod_cast hk₁_cover
        have hN_le_Out : (N : ℝ) ≤ (OutCard : ℝ) := by exact_mod_cast hOut_ge_N
        have hS_ge : alphaNDisj / 4 * (N : ℝ) ≤ (S : ℝ) := by nlinarith
        have hβ_le_1 : betaNDisj ≤ 1 := hβ1
        calc
          cCommSpace * (N : ℝ) * (OutCard : ℝ)
            ≤ (alphaNDisj / 16) * (N : ℝ) * (OutCard : ℝ) := by
              have hle : cCommSpace ≤ alphaNDisj / 16 := by
                unfold cCommSpace; nlinarith
              exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hNR) hOutR
          _ = ((OutCard : ℝ) / 4) * (alphaNDisj / 4 * (N : ℝ)) := by ring
          _ ≤ (C : ℝ) * (S : ℝ) :=
              mul_le_mul hCR hS_ge (by positivity) (by positivity)

/-! ### Communication-Space Tradeoffs for Boolean Matrix Products -/

/-- Communication-space tradeoff for Boolean matrix-vector
Product): There exists a universal constant `c > 0` such that every bounded-error (error `≤ 1 / 3`)
communicating circuit with communication `C` and storage `S` computing the `N × N` Boolean
matrix-vector product satisfies `c * N ^ 2 ≤ C * S`. -/
theorem comm_space_tradeoff_boolMatVec :
    ∃ c : ℝ, 0 < c ∧
      ∀ (N S : ℕ) (sch : CommSchedule (Fin N) S)
        (μ : RandCommCircuit (Fin N → BitString N) (BitString N) sch),
        μ.Solves (1 / 3) (boolMatVec N) →
        c * (N : ℝ) ^ 2 ≤ (sch.commCount : ℝ) * (S : ℝ) := by
  refine ⟨cCommSpace, cCommSpace_pos, fun N S sch μ hsolves => ?_⟩
  by_cases hN0 : N = 0
  · subst hN0; simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero]; positivity
  have hN : 1 ≤ N := Nat.pos_of_ne_zero hN0
  obtain ⟨hS, hC⟩ := mv_unconstrained_bounds hN hsolves
  have hcomb := comm_space_combine (N := N) (OutCard := N) (C := sch.commCount) (S := S)
    hN le_rfl hS hC (fun B hB hB_le => by
      have hcard : Fintype.card (Fin N) = N := Fintype.card_fin N
      obtain ⟨a, d, had, k₁, outs, hinj, hcover, hcomm, hside⟩ :=
        exists_heavy_slice sch hB (by omega)
      rw [hcard] at hcover
      refine ⟨k₁, hcover, ?_⟩
      let m := min k₁ B
      have hk₁_pos : 1 ≤ k₁ := by
        by_contra h0; have : k₁ = 0 := by omega
        rw [this, mul_zero, mul_zero] at hcover; omega
      have hm1 : 1 ≤ m := le_min hk₁_pos hB
      have hmB : m ≤ B := min_le_right k₁ B
      let outs' : Fin m → Fin N := fun i => outs ⟨i.val, lt_of_lt_of_le i.isLt (min_le_left _ _)⟩
      have hinj' : Function.Injective outs' := by
        intro i₁ i₂ h
        exact Fin.ext (Fin.mk.inj (hinj h))
      have hside' :
          (∀ i, a ≤ (sch.emitStep (outs' i)).val ∧ (sch.emitStep (outs' i)).val < a + d ∧
            sch.kind (sch.emitStep (outs' i)) = .emitAlice (outs' i)) ∨
          (∀ i, a ≤ (sch.emitStep (outs' i)).val ∧ (sch.emitStep (outs' i)).val < a + d ∧
            sch.kind (sch.emitStep (outs' i)) = .emitBob (outs' i)) :=
        hside.imp (fun h i => h _) (fun h i => h _)
      obtain ⟨ν, hdepth, hν_solves⟩ := slice_to_publicCoin hsolves had outs' hside'
      have hdepth' : ν.depth ≤ (B + m : ℕ) :=
        hdepth.trans (by exact_mod_cast Nat.add_le_add_right hcomm m)
      have hν' : SolvesWithSuccess ν ((2 / 3 : ℝ) * (2 : ℝ) ^ (-(S : ℝ)))
          (fun A b v => (fun i => boolMatVec N A b (outs' i)) = v) := by
        rw [show (2 / 3 : ℝ) = 1 - 1 / 3 by norm_num]; exact hν_solves
      exact slice_outputs_bound_mv hS hB hB_le hm1 hmB hinj' hdepth' hν')
  calc
    cCommSpace * (N : ℝ) ^ 2 = cCommSpace * (N : ℝ) * (N : ℝ) := by ring
    _ ≤ (sch.commCount : ℝ) * (S : ℝ) := hcomb

/-- Communication-space tradeoff for Boolean matrix
Multiplication): There exists a universal constant `c > 0` such that every bounded-error
(error `≤ 1 / 3`) communicating circuit with communication `C` and storage `S` computing the
`N × N` Boolean matrix product satisfies `c * N ^ 3 ≤ C * S`. -/
theorem comm_space_tradeoff_boolMatMul :
    ∃ c : ℝ, 0 < c ∧
      ∀ (N S : ℕ) (sch : CommSchedule (Fin N × Fin N) S)
        (μ : RandCommCircuit (Fin N → BitString N) (Fin N → BitString N) sch),
        μ.Solves (1 / 3) (boolMatMul N) →
        c * (N : ℝ) ^ 3 ≤ (sch.commCount : ℝ) * (S : ℝ) := by
  refine ⟨cCommSpace, cCommSpace_pos, fun N S sch μ hsolves => ?_⟩
  by_cases hN0 : N = 0
  · subst hN0; simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero]; positivity
  have hN : 1 ≤ N := Nat.pos_of_ne_zero hN0
  obtain ⟨hS, hC⟩ := mm_unconstrained_bounds hN hsolves
  have hOut_ge : N ≤ N ^ 2 := by rw [sq]; exact Nat.le_mul_of_pos_right N (by omega)
  have hcomb := comm_space_combine (N := N) (OutCard := N ^ 2) (C := sch.commCount) (S := S)
    hN hOut_ge hS hC (fun B hB hB_le => by
      have hcard : Fintype.card (Fin N × Fin N) = N ^ 2 := by
        rw [Fintype.card_prod, Fintype.card_fin, sq]
      obtain ⟨a, d, had, k₁, outs, hinj, hcover, hcomm, hside⟩ :=
        exists_heavy_slice sch hB (by rw [hcard]; exact Nat.pow_pos (by omega))
      rw [hcard] at hcover
      refine ⟨k₁, hcover, ?_⟩
      let m := min k₁ B
      have hk₁_pos : 1 ≤ k₁ := by
        by_contra h0; have : k₁ = 0 := by omega
        rw [this, mul_zero, mul_zero] at hcover
        have : 1 ≤ N ^ 2 := Nat.pow_pos (by omega)
        omega
      have hm1 : 1 ≤ m := le_min hk₁_pos hB
      have hmB : m ≤ B := min_le_right k₁ B
      let outs' : Fin m → Fin N × Fin N :=
        fun i => outs ⟨i.val, lt_of_lt_of_le i.isLt (min_le_left _ _)⟩
      have hinj' : Function.Injective outs' := by
        intro i₁ i₂ h
        exact Fin.ext (Fin.mk.inj (hinj h))
      have hside' :
          (∀ i, a ≤ (sch.emitStep (outs' i)).val ∧ (sch.emitStep (outs' i)).val < a + d ∧
            sch.kind (sch.emitStep (outs' i)) = .emitAlice (outs' i)) ∨
          (∀ i, a ≤ (sch.emitStep (outs' i)).val ∧ (sch.emitStep (outs' i)).val < a + d ∧
            sch.kind (sch.emitStep (outs' i)) = .emitBob (outs' i)) :=
        hside.imp (fun h i => h _) (fun h i => h _)
      obtain ⟨ν, hdepth, hν_solves⟩ := slice_to_publicCoin hsolves had outs' hside'
      have hdepth' : ν.depth ≤ (B + m : ℕ) :=
        hdepth.trans (by exact_mod_cast Nat.add_le_add_right hcomm m)
      have hν' : SolvesWithSuccess ν ((2 / 3 : ℝ) * (2 : ℝ) ^ (-(S : ℝ)))
          (fun A B' v => (fun i => boolMatMul N A B' (outs' i)) = v) := by
        rw [show (2 / 3 : ℝ) = 1 - 1 / 3 by norm_num]; exact hν_solves
      exact slice_outputs_bound_mm hS hB hB_le hm1 hmB hinj' hdepth' hν')
  calc
    cCommSpace * (N : ℝ) ^ 3 = cCommSpace * (N : ℝ) * ((N ^ 2 : ℕ) : ℝ) := by
      push_cast; ring
    _ ≤ (sch.commCount : ℝ) * (S : ℝ) := hcomb

end

end CslibFrontier.Computability.Communication
