module

public import CslibFrontier.Computability.Circuit.ObliviousPoly
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListLookup
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimePrimitives
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Polynomial-Time Rebalance and Scheduled Pass for Oblivious Circuits

This module proves polynomial-time computability of the variable-length oblivious circuit gadgets:
`emitRebalanceLevel`, `emitRebalanceHalfTape`, `emitTapeStep0`, and the guarded scheduled
rebalance pass `safeSchedulePass`.

## Main definitions

* `CslibFrontier.Computability.Circuit.Oblivious.safeRebalanceStep`: guarded single-level rebalance
  step preserving half-tape length and all row counts.
* `CslibFrontier.Computability.Circuit.Oblivious.safeSchedulePass`: guarded scheduled rebalance pass
  agreeing with `emitSchedulePass` on geometric half-tapes.

## Main results

* `CslibFrontier.Computability.Circuit.Oblivious.poly_emitRebalanceLevel`
* `CslibFrontier.Computability.Circuit.Oblivious.poly_emitRebalanceHalfTape`
* `CslibFrontier.Computability.Circuit.Oblivious.poly_emitTapeStep0`
* `CslibFrontier.Computability.Circuit.Oblivious.poly_safeSchedulePass`
-/

public section

namespace CslibFrontier.Computability.Circuit.Oblivious

open Turing MultiTapeTM Cslib.Circuits Cslib.Circuits.Boolean

theorem poly_emitRebalanceLevel :
    ComputableInPolyTime
      (fun p : (Gates × ℕ) × (LevelW × LevelW) => emitRebalanceLevel p.1.1 p.1.2 p.2.1 p.2.2)
      (encPair (encPair encGates encNat) (encPair encLevelW encLevelW))
      (encPair encGates (encPair encLevelW encLevelW)) := by
  set P := (Gates × ℕ) × (LevelW × LevelW)
  set encP : P ↪ List Bool := encPair (encPair encGates encNat) (encPair encLevelW encLevelW)
  have hg : ComputableInPolyTime (fun p : P => p.1.1) encP encGates :=
    poly_fst (ComputableInPolyTime.fst _ _)
  have hfls : ComputableInPolyTime (fun p : P => p.1.2) encP encNat :=
    poly_snd (ComputableInPolyTime.fst _ _)
  have hlo : ComputableInPolyTime (fun p : P => p.2.1) encP encLevelW :=
    poly_fst (ComputableInPolyTime.snd _ _)
  have hhi : ComputableInPolyTime (fun p : P => p.2.2) encP encLevelW :=
    poly_snd (ComputableInPolyTime.snd _ _)
  have hlo1 := poly_fst hlo
  have hlo2 := poly_snd hlo
  have hhi1 := poly_fst hhi
  have hhi2 := poly_snd hhi
  have hcnt := @ComputableInPolyTime.comp' P _ _ encP _ _
    (fun q : (Gates × ℕ) × (List ℕ × List ℕ) => emitCntRebalance q.1.1 q.1.2 q.2.1 q.2.2)
    (fun p => ((p.1.1, p.1.2), (p.2.1.1, p.2.2.1)))
    poly_emitCntRebalance ((hg.prod hfls).prod (hlo1.prod hhi1))
  have hlist := ComputableInPolyTime.range.comp'
    ((ComputableInPolyTime.length (encList encNat)).comp' hlo2)
  set Par := (LevelW × LevelW) × ((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ × ℕ)
  set encPar : Par ↪ List Bool :=
    encPair (encPair encLevelW encLevelW)
      (encPair (encPair (encPair encNat encNat) (encPair encNat encNat))
        (encPair encNat (encPair encNat encNat)))
  set Acc := Gates × (List (List ℕ) × List (List ℕ) × List (List ℕ))
  set encAcc : Acc ↪ List Bool :=
    encPair encGates
      (encPair (encList (encList encNat))
        (encPair (encList (encList encNat)) (encList (encList encNat))))
  have hpar : ComputableInPolyTime
      (fun p : P =>
        let r := emitCntRebalance p.1.1 p.1.2 p.2.1.1 p.2.2.1
        ((p.2.1, p.2.2),
         (((p.2.1.1.getD 0 0, p.2.1.1.getD 1 0), (p.2.1.1.getD 4 0, p.2.1.1.getD 5 0)), r.2.1)))
      encP encPar :=
    ((hlo.prod hhi).prod
      ((((poly_getD_const hlo1 0 0).prod (poly_getD_const hlo1 1 0)).prod
        ((poly_getD_const hlo1 4 0).prod (poly_getD_const hlo1 5 0))).prod
        (poly_fst (poly_snd hcnt)))).of_enc_eq fun _ => rfl
  have hinit : ComputableInPolyTime
      (fun p : P => ((emitCntRebalance p.1.1 p.1.2 p.2.1.1 p.2.2.1).1, ([], [], [])))
      encP encAcc :=
    (poly_fst hcnt).prod
      ((ComputableInPolyTime.const []).prod
        ((ComputableInPolyTime.const []).prod (ComputableInPolyTime.const [])))
  let step : Par → Acc → ℕ → Acc := fun par acc j =>
    let B := par.1.1.2.length
    let r := emitCellRebalance acc.1 par.2.1.1.1 par.2.1.1.2 par.2.1.2.1 par.2.1.2.2
      par.2.2.1 par.2.2.2.1 par.2.2.2.2
      (par.1.1.2.getD j []) (par.1.2.2.getD j []) (par.1.2.2.getD (B + j) [])
    (r.1, (r.2.1 :: acc.2.1, r.2.2.1 :: acc.2.2.1, r.2.2.2 :: acc.2.2.2))
  have hstep : ComputableInPolyTime (fun q : (Par × Acc) × ℕ => step q.1.1 q.1.2 q.2)
      (encPair (encPair encPar encAcc) encUnary) encAcc := by
    have qP := poly_fst (ComputableInPolyTime.fst (encPair encPar encAcc) encUnary)
    have qA := poly_snd (ComputableInPolyTime.fst (encPair encPar encAcc) encUnary)
    have qJ := ComputableInPolyTime.snd (encPair encPar encAcc) encUnary
    have qLo2 := poly_snd (poly_fst (poly_fst qP))
    have qHi2 := poly_snd (poly_snd (poly_fst qP))
    have qB := (ComputableInPolyTime.length (encList encNat)).comp' qLo2
    have hcr := @ComputableInPolyTime.comp' ((Par × Acc) × ℕ) _ _
      (encPair (encPair encPar encAcc) encUnary) _ _
      (fun r : (Gates × ((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ × ℕ)) × (List ℕ × List ℕ × List ℕ) =>
        emitCellRebalance r.1.1 r.1.2.1.1.1 r.1.2.1.1.2 r.1.2.1.2.1 r.1.2.1.2.2
          r.1.2.2.1 r.1.2.2.2.1 r.1.2.2.2.2 r.2.1 r.2.2.1 r.2.2.2)
      (fun q => ((q.1.2.1, q.1.1.2),
        (q.1.1.1.1.2.getD q.2 [], (q.1.1.1.2.2.getD q.2 [],
          q.1.1.1.2.2.getD (q.1.1.1.1.2.length + q.2) []))))
      poly_emitCellRebalance
      (((poly_fst qA).prod (poly_snd qP)).prod
        ((ComputableInPolyTime.listGetDWithInput qLo2 qJ []).prod
          ((ComputableInPolyTime.listGetDWithInput qHi2 qJ []).prod
            (ComputableInPolyTime.listGetDWithInput qHi2
              (ComputableInPolyTime.unary_add.comp' (qB.prod qJ)) []))))
    have hacc2 := poly_snd qA
    exact ((poly_fst hcr).prod
      ((poly_cons' (poly_fst (poly_snd hcr)) (poly_fst hacc2)).prod
        ((poly_cons' (poly_fst (poly_snd (poly_snd hcr))) (poly_fst (poly_snd hacc2))).prod
          (poly_cons' (poly_snd (poly_snd (poly_snd hcr))) (poly_snd (poly_snd hacc2)))))).of_enc_eq
      fun q => congrArg encAcc (by dsimp only [step])
  have hsz_poly : PolyBounded (fun p : P => (encP p).length) (fun p : P =>
      let W := 211 * (encP p).length + 40
      let G := (encP p).length + 4 * W + 11
      let M := (encP p).length + 37 + 210 * (encP p).length
      2 * (2 * (M * (2 * G + 1)) + 1 + W) + 1 +
        3 * (2 * ((encP p).length * (2 * (10 * (2 * W + 1)) + 1)) + 1)) := by
    have hS : PolyBounded (fun p : P => (encP p).length) (fun p : P => (encP p).length) :=
      PolyBounded.self
    have hW : PolyBounded (fun p : P => (encP p).length) (fun p : P => 211 * (encP p).length +
      40) :=
      ((PolyBounded.const 211).mul hS).add (PolyBounded.const 40)
    have hG := (hS.add ((PolyBounded.const 4).mul hW)).add (PolyBounded.const 11)
    have hM := (hS.add (PolyBounded.const 37)).add ((PolyBounded.const 210).mul hS)
    have h1 := ((PolyBounded.const 2).mul
      ((((PolyBounded.const 2).mul (hM.mul (((PolyBounded.const 2).mul hG).add
        (PolyBounded.const 1)))).add
        (PolyBounded.const 1)).add hW)).add (PolyBounded.const 1)
    have h2 := (PolyBounded.const 3).mul
      (((PolyBounded.const 2).mul (hS.mul
        (((PolyBounded.const 2).mul ((PolyBounded.const 10).mul
          (((PolyBounded.const 2).mul hW).add (PolyBounded.const 1)))).add
            (PolyBounded.const 1)))).add
        (PolyBounded.const 1))
    exact h1.add h2
  have hP_proj : ∀ (p : P),
      p.1.1.1.length ≤ (encP p).length ∧ (encNat p.1.1.2).length ≤ (encP p).length ∧
      (encNat p.1.2).length ≤ (encP p).length ∧ p.2.1.2.length ≤ (encP p).length ∧
      (∀ gt ∈ p.1.1.1, (Boolean.encGate gt).length ≤ (encP p).length) ∧
      (∀ w ∈ p.2.1.1, (encNat w).length ≤ (encP p).length) ∧
      (∀ w ∈ p.2.2.1, (encNat w).length ≤ (encP p).length) ∧
      (∀ r ∈ p.2.1.2, ∀ w ∈ r, (encNat w).length ≤ (encP p).length) ∧
      (∀ r ∈ p.2.2.2, ∀ w ∈ r, (encNat w).length ≤ (encP p).length) := by
    intro p
    have hp1 : (encPair encGates encNat p.1).length ≤ (encP p).length :=
      length_le_encPair_left _ _ p
    have hp2 : (encPair encLevelW encLevelW p.2).length ≤ (encP p).length :=
      length_le_encPair_right _ _ p
    have hg_le : (encGates p.1.1).length ≤ (encP p).length := by
      have : (encGates p.1.1).length ≤ (encPair encGates encNat p.1).length := by
        rw [length_encPair]; omega
      omega
    have hfls_le : (encNat p.1.2).length ≤ (encP p).length := by
      have : (encNat p.1.2).length ≤ (encPair encGates encNat p.1).length := by
        rw [length_encPair]; omega
      omega
    have hlo_le : (encLevelW p.2.1).length ≤ (encP p).length := by
      have : (encLevelW p.2.1).length ≤ (encPair encLevelW encLevelW p.2).length := by
        rw [length_encPair]; omega
      omega
    have hhi_le : (encLevelW p.2.2).length ≤ (encP p).length := by
      have : (encLevelW p.2.2).length ≤ (encPair encLevelW encLevelW p.2).length := by
        rw [length_encPair]; omega
      omega
    have hg1_le : (encList Boolean.encGate p.1.1.1).length ≤ (encGates p.1.1).length := by
      change _ ≤ (encPair (encList Boolean.encGate) encNat p.1.1).length; rw [length_encPair]; omega
    have hg2_le : (encNat p.1.1.2).length ≤ (encGates p.1.1).length := by
      change _ ≤ (encPair (encList Boolean.encGate) encNat p.1.1).length; rw [length_encPair]; omega
    have hlo1_le : (encList encNat p.2.1.1).length ≤ (encLevelW p.2.1).length := by
      change _ ≤ (encPair (encList encNat)
        (encList (encList encNat)) p.2.1).length; rw [length_encPair]; omega
    have hlo2_le : (encList (encList encNat) p.2.1.2).length ≤ (encLevelW p.2.1).length := by
      change _ ≤ (encPair (encList encNat)
        (encList (encList encNat)) p.2.1).length; rw [length_encPair]; omega
    have hhi1_le : (encList encNat p.2.2.1).length ≤ (encLevelW p.2.2).length := by
      change _ ≤ (encPair (encList encNat)
        (encList (encList encNat)) p.2.2).length; rw [length_encPair]; omega
    refine ⟨(length_le_encList Boolean.encGate p.1.1.1).trans (by omega), by omega, hfls_le,
      (length_le_encList (encList encNat) p.2.1.2).trans (by omega),
      fun gt hgt => (length_le_encList_of_mem Boolean.encGate hgt).trans (by omega),
      fun w hw => (length_le_encList_of_mem encNat hw).trans (by omega),
      fun w hw => (length_le_encList_of_mem encNat hw).trans (by omega),
      fun r hr w hw => ((length_le_encList_of_mem encNat hw).trans
        (length_encRow_of_mem hr)).trans hlo_le,
      fun r hr w hw => ((length_le_encList_of_mem encNat hw).trans
        (length_encRow_of_mem hr)).trans hhi_le⟩
  have hfold := (ComputableInPolyTime.foldlWith_spec hpar hlist hinit hstep
    (fun p consumed acc =>
      let W := 211 * (encP p).length + 40
      let G := (encP p).length + 4 * W + 11
      let g1 := (emitCntRebalance p.1.1 p.1.2 p.2.1.1 p.2.2.1).1
      acc.1.1.length = g1.1.length + 210 * consumed.length ∧
      acc.1.2 = g1.2 + 210 * consumed.length ∧
      (∀ gt ∈ acc.1.1, (Boolean.encGate gt).length ≤ G) ∧
      acc.2.1.length = consumed.length ∧ acc.2.2.1.length = consumed.length ∧
      acc.2.2.2.length = consumed.length ∧
      (∀ r ∈ acc.2.1, r.length = 10 ∧ ∀ w ∈ r, (encNat w).length ≤ W) ∧
      (∀ r ∈ acc.2.2.1, r.length = 10 ∧ ∀ w ∈ r, (encNat w).length ≤ W) ∧
      (∀ r ∈ acc.2.2.2, r.length = 10 ∧ ∀ w ∈ r, (encNat w).length ≤ W))
    (fun p => by
      obtain ⟨_, hg2, hfls, _, hg1, hlo, hhi, _, _⟩ := hP_proj p
      set W := 211 * (encP p).length + 40
      set G := (encP p).length + 4 * W + 11
      have hcnt_b := emitCntRebalance_bounds (g := p.1.1) (G := G) (W := W)
        (hfls.trans (by omega)) (fun w hw => (hlo w hw).trans (by omega))
        (fun w hw => (hhi w hw).trans (by omega)) (by simp [encNat_apply, W]) (by omega)
        (fun gt hgt => (hg1 gt hgt).trans (by omega))
        ((length_encNat_le_add (w := p.1.1.2 + 37) (a := p.1.1.2) (b :=
          37) le_rfl).trans (by omega))
      exact ⟨by simp, by simp, hcnt_b.2.2.1, by simp, by simp, by simp, by simp, by simp, by simp⟩)
    (fun p consumed acc j hpref hinv => by
      rcases hinv with ⟨hgl, hg2, hgb, hrL, hrH0, hrH1, hmL, hmH0, hmH1⟩
      obtain ⟨_, hg2_0, hfls, hB_le, hg1, hlo, hhi, hrow_lo, hrow_hi⟩ := hP_proj p
      have hclen : consumed.length + 1 ≤ p.2.1.2.length := by
        have := hpref.length_le; simp at this; omega
      set W := 211 * (encP p).length + 40
      set G := (encP p).length + 4 * W + 11
      have h0_b : (encNat 0).length ≤ W := by simp [encNat_apply, W]
      have hcnt_b := emitCntRebalance_bounds (g := p.1.1) (fls := p.1.2)
        (lo := p.2.1.1) (hi := p.2.2.1) (G := G) (W := W)
        (hfls.trans (by omega)) (fun w hw => (hlo w hw).trans (by omega))
        (fun w hw => (hhi w hw).trans (by omega)) h0_b (by omega)
        (fun gt hgt => (hg1 gt hgt).trans (by omega))
        ((length_encNat_le_add (w := p.1.1.2 + 37) (a := p.1.1.2) (b :=
          37) le_rfl).trans (by omega))
      have hW_step : (encNat (acc.1.2 + 210)).length ≤ W := by
        have hle2 : acc.1.2 + 210 ≤ p.1.1.2 + (37 + 210 * (encP p).length) := by
          dsimp only at hcnt_b; rw [hg2, hcnt_b.2.1]; nlinarith
        exact (length_encNat_le_add hle2).trans (by omega)
      have hget_lo : ∀ k, (encNat (p.2.1.1.getD k 0)).length ≤ W := fun k => by
        by_cases hk : k < p.2.1.1.length
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
          exact (hlo _ (List.getElem_mem hk)).trans (by omega)
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; exact h0_b
      have hget_r : ∀ (rows : List (List ℕ)) (k : ℕ), (∀ r ∈ rows, ∀ w ∈ r, (encNat w).length ≤
        (encP p).length) →
          ∀ w ∈ rows.getD k [], (encNat w).length ≤ W := fun rows k hrows w hw => by
        by_cases hk : k < rows.length
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk] at hw
          exact (hrows _ (List.getElem_mem hk) w hw).trans (by omega)
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hw; simp at hw
      have hcr := emitCellRebalance_bounds (g := acc.1) (G := G) (W := W)
        (hget_lo 0) (hget_lo 1) (hget_lo 4) (hget_lo 5)
        hcnt_b.2.2.2.1 hcnt_b.2.2.2.2.1 hcnt_b.2.2.2.2.2.1
        (hget_r _ j hrow_lo) (hget_r _ j hrow_hi) (hget_r _ (p.2.1.2.length + j) hrow_hi)
        h0_b (by omega) hgb hW_step
      refine ⟨by dsimp only [step]; rw [hcr.1, hgl]; simp; omega,
        by dsimp only [step]; rw [hcr.2.1, hg2]; simp; omega,
        by dsimp only [step]; exact hcr.2.2.2.2.2.2.2.2,
        by dsimp only [step]; simp [hrL], by dsimp only [step]; simp [hrH0],
        by dsimp only [step]; simp [hrH1],
        fun r hr => by
          dsimp only [step] at hr; simp only [List.mem_cons] at hr
          rcases hr with rfl | hr
          · exact ⟨hcr.2.2.1, hcr.2.2.2.2.2.1⟩
          · exact hmL r hr,
        fun r hr => by
          dsimp only [step] at hr; simp only [List.mem_cons] at hr
          rcases hr with rfl | hr
          · exact ⟨hcr.2.2.2.1, hcr.2.2.2.2.2.2.1⟩
          · exact hmH0 r hr,
        fun r hr => by
          dsimp only [step] at hr; simp only [List.mem_cons] at hr
          rcases hr with rfl | hr
          · exact ⟨hcr.2.2.2.2.1, hcr.2.2.2.2.2.2.2.1⟩
          · exact hmH1 r hr⟩)
    hsz_poly
    (fun p consumed acc hpref hinv => by
      rcases hinv with ⟨hgl, hg2, hgb, hrL, hrH0, hrH1, hmL, hmH0, hmH1⟩
      obtain ⟨hg_len, hg2_0, _, hB_le, _, _, _, _, _⟩ := hP_proj p
      have hclen : consumed.length ≤ (encP p).length := by
        have := hpref.length_le; rw [List.length_range] at this; omega
      have hcnt_len : (emitCntRebalance p.1.1 p.1.2 p.2.1.1 p.2.2.1).1.1.length =
        p.1.1.1.length + 37 ∧
          (emitCntRebalance p.1.1 p.1.2 p.2.1.1 p.2.2.1).1.2 = p.1.1.2 + 37 := by
        dsimp only [emitCntRebalance_eq, emitMap_eq, Gates.gOr3_eq, Gates.gMux3_eq,
          Gates.gAnd_eq, Gates.gOr_eq,
          Gates.emit_eq, List.foldl_cons, List.foldl_nil]; exact ⟨by simp, by omega⟩
      set W := 211 * (encP p).length + 40
      set G := (encP p).length + 4 * W + 11
      have hacc1_len : acc.1.1.length ≤ (encP p).length + 37 + 210 * (encP p).length := by
        rw [hgl, hcnt_len.1]; nlinarith
      have hacc1_2 : (encNat acc.1.2).length ≤ W := by
        have hle2 : acc.1.2 ≤ p.1.1.2 + (37 + 210 * (encP p).length) := by
          rw [hg2, hcnt_len.2]; nlinarith
        exact (length_encNat_le_add hle2).trans (by omega)
      have hG_b := length_encGates_le hacc1_len hgb hacc1_2
      have hrow_le : ∀ (rs : List (List ℕ)), rs.length = consumed.length →
          (∀ r ∈ rs, r.length = 10 ∧ ∀ w ∈ r, (encNat w).length ≤ W) →
          (encList (encList encNat) rs).length ≤
            (encP p).length * (2 * (10 * (2 * W + 1)) + 1) := by
        intro rs hrs hrm
        refine (length_encList_le (encList encNat) rs
          fun r hr => ?_).trans (Nat.mul_le_mul_right _ (by omega))
        exact (length_encList_le encNat r (hrm r hr).2).trans (Nat.mul_le_mul_right _
          (hrm r hr).1.le)
      have hL_le := hrow_le acc.2.1 hrL hmL
      have hH0_le := hrow_le acc.2.2.1 hrH0 hmH0
      have hH1_le := hrow_le acc.2.2.2 hrH1 hmH1
      change (encPair encGates (encPair (encList (encList encNat))
        (encPair (encList (encList encNat)) (encList (encList encNat)))) acc).length ≤ _
      simp only [length_encPair]
      dsimp only [W, G] at hG_b hL_le hH0_le hH1_le ⊢
      linarith)).1
  have hres_fst := poly_fst hfold
  have hres_snd := poly_snd hfold
  have hrL_rev := ComputableInPolyTime.listReverseWithInput (poly_fst hres_snd)
  have hrH0_rev := ComputableInPolyTime.listReverseWithInput (poly_fst (poly_snd hres_snd))
  have hrH1_rev := ComputableInPolyTime.listReverseWithInput (poly_snd (poly_snd hres_snd))
  have hlowCnt' := poly_fst (poly_snd (poly_snd hcnt))
  have hhiCnt' := poly_snd (poly_snd (poly_snd hcnt))
  exact (hres_fst.prod ((hlowCnt'.prod hrL_rev).prod
    (hhiCnt'.prod (poly_append' hrH0_rev hrH1_rev)))).of_enc_eq fun p =>
    congrArg _ (by dsimp only [emitRebalanceLevel_eq, step])

@[fun_prop] theorem poly_emitRebalanceHalfTape :
    ComputableInPolyTime
      (fun p : (Gates × ℕ) × (HalfW × ℕ) => emitRebalanceHalfTape p.1.1 p.1.2 p.2.1 p.2.2)
      (encPair (encPair encGates encNat) (encPair encHalfW encUnary))
      (encPair encGates encHalfW) := by
  have hg :=
    poly_fst (ComputableInPolyTime.fst (encPair encGates encNat) (encPair encHalfW encUnary))
  have hfls :=
    poly_snd (ComputableInPolyTime.fst (encPair encGates encNat) (encPair encHalfW encUnary))
  have hhw :=
    poly_fst (ComputableInPolyTime.snd (encPair encGates encNat) (encPair encHalfW encUnary))
  have hlvl :=
    poly_snd (ComputableInPolyTime.snd (encPair encGates encNat) (encPair encHalfW encUnary))
  have hlow := ComputableInPolyTime.listGetDWithInput hhw hlvl ([], [])
  have hhi := ComputableInPolyTime.listGetDWithInput hhw
    (ComputableInPolyTime.unary_add.comp' (hlvl.prod (ComputableInPolyTime.const 1))) ([], [])
  have hrb := @ComputableInPolyTime.comp' ((Gates × ℕ) × (HalfW × ℕ)) _ _
    (encPair (encPair encGates encNat) (encPair encHalfW encUnary)) _ _
    (fun q : (Gates × ℕ) × (LevelW × LevelW) => emitRebalanceLevel q.1.1 q.1.2 q.2.1 q.2.2)
    (fun p => ((p.1.1, p.1.2), (p.2.1.getD p.2.2 ([], []), p.2.1.getD (p.2.2 + 1) ([], []))))
    poly_emitRebalanceLevel ((hg.prod hfls).prod (hlow.prod hhi))
  have hlow' := poly_fst (poly_snd hrb)
  have hhi' := poly_snd (poly_snd hrb)
  have htake := ComputableInPolyTime.listTakeWithInput hhw hlvl
  have hdrop := ComputableInPolyTime.listDropWithInput hhw
    (ComputableInPolyTime.unary_add.comp' (hlvl.prod (ComputableInPolyTime.const 2)))
  exact ((poly_fst hrb).prod
    (poly_append' (poly_append' htake (poly_cons' hlow' (poly_cons' hhi'
      (ComputableInPolyTime.const []))))
      hdrop)).of_enc_eq fun p => congrArg _ (by dsimp only [emitRebalanceHalfTape_eq])

theorem poly_emitTapeStep0 :
    ComputableInPolyTime
      (fun p : (Gates × ℕ) × ((ℕ × ℕ × ℕ) × (ℕ × ℕ) × TapeW) =>
        emitTapeStep0 p.1.1 p.1.2 p.2.1.1 p.2.1.2.1 p.2.1.2.2
          p.2.2.1.1 p.2.2.1.2 p.2.2.2)
      (encPair (encPair encGates encNat)
        (encPair (encPair encNat (encPair encNat encNat))
          (encPair (encPair encNat encNat) encTapeW)))
      (encPair encGates encTapeW) := by
  set P := (Gates × ℕ) × ((ℕ × ℕ × ℕ) × (ℕ × ℕ) × TapeW)
  set encP : P ↪ List Bool :=
    encPair (encPair encGates encNat)
      (encPair (encPair encNat (encPair encNat encNat)) (encPair (encPair encNat encNat) encTapeW))
  have hg : ComputableInPolyTime (fun p : P => p.1.1) encP encGates :=
    poly_fst (ComputableInPolyTime.fst _ _)
  have hfls : ComputableInPolyTime (fun p : P => p.1.2) encP encNat :=
    poly_snd (ComputableInPolyTime.fst _ _)
  have hmN : ComputableInPolyTime (fun p : P => p.2.1.1) encP encNat :=
    poly_fst (poly_fst (ComputableInPolyTime.snd _ _))
  have hmZ : ComputableInPolyTime (fun p : P => p.2.1.2.1) encP encNat :=
    poly_fst (poly_snd (poly_fst (ComputableInPolyTime.snd _ _)))
  have hmP : ComputableInPolyTime (fun p : P => p.2.1.2.2) encP encNat :=
    poly_snd (poly_snd (poly_fst (ComputableInPolyTime.snd _ _)))
  have hw0 : ComputableInPolyTime (fun p : P => p.2.2.1.1) encP encNat :=
    poly_fst (poly_fst (poly_snd (ComputableInPolyTime.snd _ _)))
  have hw1 : ComputableInPolyTime (fun p : P => p.2.2.1.2) encP encNat :=
    poly_snd (poly_fst (poly_snd (ComputableInPolyTime.snd _ _)))
  have htw : ComputableInPolyTime (fun p : P => p.2.2.2) encP encTapeW :=
    poly_snd (poly_snd (ComputableInPolyTime.snd _ _))
  have hL : ComputableInPolyTime (fun p : P => p.2.2.2.2.1) encP encHalfW :=
    poly_fst (poly_snd htw)
  have hR : ComputableInPolyTime (fun p : P => p.2.2.2.2.2) encP encHalfW :=
    poly_snd (poly_snd htw)
  have hl0 := poly_getD_const hL 0 ([], [])
  have hr0 := poly_getD_const hR 0 ([], [])
  have hlh0 := poly_getD_const (poly_getD_const (poly_snd hl0) 0 []) 0 0
  have hlh1 := poly_getD_const (poly_getD_const (poly_snd hl0) 0 []) 1 0
  have hrh0 := poly_getD_const (poly_getD_const (poly_snd hr0) 0 []) 0 0
  have hrh1 := poly_getD_const (poly_getD_const (poly_snd hr0) 0 []) 1 0
  have r1 := poly_gMux3' hg hmN hlh0 hmZ hw0 hmP hrh0
  have r2 := poly_gMux3' (poly_fst r1) hmN hlh1 hmZ hw1 hmP hrh1
  have r3 := @ComputableInPolyTime.comp' P _ _ encP _ _
    (fun q : (Gates × ℕ) × ((ℕ × ℕ × ℕ) × (ℕ × ℕ) × LevelW) =>
      emitShiftLevel0 q.1.1 q.1.2 q.2.1.1 q.2.1.2.1 q.2.1.2.2 q.2.2.1.1 q.2.2.1.2 q.2.2.2)
    _ poly_emitShiftLevel0
    (((poly_fst r2).prod hfls).prod ((hmN.prod (hmZ.prod hmP)).prod ((hw0.prod hw1).prod hl0)))
  have r4 := @ComputableInPolyTime.comp' P _ _ encP _ _
    (fun q : (Gates × ℕ) × ((ℕ × ℕ × ℕ) × (ℕ × ℕ) × LevelW) =>
      emitShiftLevel0 q.1.1 q.1.2 q.2.1.1 q.2.1.2.1 q.2.1.2.2 q.2.2.1.1 q.2.2.1.2 q.2.2.2)
    _ poly_emitShiftLevel0
    (((poly_fst r3).prod hfls).prod ((hmP.prod (hmZ.prod hmN)).prod ((hw0.prod hw1).prod hr0)))
  exact ((poly_fst r4).prod
    (((poly_snd r1).prod (poly_snd r2)).prod
      ((poly_cons' (poly_snd r3)
        (ComputableInPolyTime.listDropWithInput hL (ComputableInPolyTime.const 1))).prod
        (poly_cons' (poly_snd r4)
          (ComputableInPolyTime.listDropWithInput hR (ComputableInPolyTime.const 1)))))).of_enc_eq
    fun p => congrArg _ (by dsimp only [emitTapeStep0_eq])

/-! ### Guarded scheduled rebalance pass `safeSchedulePass` -/

/-- Guarded rebalance step preserving `hw.length` and every row count `(hw[i]).2.length`. -/
@[expose] def safeRebalanceStep (fls t : ℕ) (acc : Gates × HalfW) (lvl : ℕ) : Gates × HalfW :=
  if (t + 1) % 2 ^ (lvl + 1) = 0 ∧ lvl + 1 < acc.2.length ∧
      (acc.2.getD (lvl + 1) ([], [])).2.length = 2 * (acc.2.getD lvl ([], [])).2.length then
    emitRebalanceHalfTape acc.1 fls acc.2 lvl
  else acc

/-- Guarded scheduled rebalance pass; agrees with `emitSchedulePass` on geometric half-tapes. -/
@[expose] def safeSchedulePass (L fls t : ℕ) (g : Gates) (hw : HalfW) : Gates × HalfW :=
  (List.range (L - 1)).foldl (safeRebalanceStep fls t) (g, hw)

private theorem poly_safeRebalanceStep :
    ComputableInPolyTime
      (fun q : ((ℕ × ℕ) × (Gates × HalfW)) × ℕ => safeRebalanceStep q.1.1.1 q.1.1.2 q.1.2 q.2)
      (encPair (encPair (encPair encNat encUnary) (encPair encGates encHalfW)) encUnary)
      (encPair encGates encHalfW) := by
  set Q := ((ℕ × ℕ) × (Gates × HalfW)) × ℕ
  set encQ : Q ↪ List Bool :=
    encPair (encPair (encPair encNat encUnary) (encPair encGates encHalfW)) encUnary
  have qFls := poly_fst (poly_fst (ComputableInPolyTime.fst
    (encPair (encPair encNat encUnary) (encPair encGates encHalfW)) encUnary))
  have qT := poly_snd (poly_fst (ComputableInPolyTime.fst
    (encPair (encPair encNat encUnary) (encPair encGates encHalfW)) encUnary))
  have qAcc := poly_snd (ComputableInPolyTime.fst
    (encPair (encPair encNat encUnary) (encPair encGates encHalfW)) encUnary)
  have qG := poly_fst qAcc
  have qHW : ComputableInPolyTime (fun q : Q => q.1.2.2) encQ (encList encLevelW) := poly_snd qAcc
  have qLvl := ComputableInPolyTime.snd
    (encPair (encPair encNat encUnary) (encPair encGates encHalfW)) encUnary
  have qLvl1 := ComputableInPolyTime.unary_add.comp' (qLvl.prod (ComputableInPolyTime.const 1))
  have hc1 := poly_binary_eq'
    (ComputableInPolyTime.binary_mod'
      (ComputableInPolyTime.unary_to_binary.comp'
        (ComputableInPolyTime.unary_add.comp' (qT.prod (ComputableInPolyTime.const 1))))
      (ComputableInPolyTime.binary_two_pow.comp' qLvl1))
    (ComputableInPolyTime.const 0)
  have hc2 := ComputableInPolyTime.unary_lt' qLvl1
    ((ComputableInPolyTime.length encLevelW).comp' qHW)
  have hc3 := ComputableInPolyTime.unary_eq'
    ((ComputableInPolyTime.length (encList encNat)).comp'
      (poly_snd (ComputableInPolyTime.listGetDWithInput qHW qLvl1 ([], []))))
    (ComputableInPolyTime.unary_mul.comp'
      ((ComputableInPolyTime.const 2).prod
        ((ComputableInPolyTime.length (encList encNat)).comp'
          (poly_snd (ComputableInPolyTime.listGetDWithInput qHW qLvl ([], []))))))
  have hcond : ComputableInPolyTime
      (fun q : Q => decide ((q.1.1.2 + 1) % 2 ^ (q.2 + 1) = 0 ∧ q.2 + 1 < q.1.2.2.length ∧
        (q.1.2.2.getD (q.2 + 1) ([], [])).2.length =
          2 * (q.1.2.2.getD q.2 ([], [])).2.length)) encQ encBool := by
    refine (poly_bool_and hc1 (poly_bool_and hc2 hc3)).of_enc_eq fun q => congrArg encBool ?_
    simp
  have hthen := @ComputableInPolyTime.comp' Q _ _ encQ _ _
    (fun r : (Gates × ℕ) × (HalfW × ℕ) => emitRebalanceHalfTape r.1.1 r.1.2 r.2.1 r.2.2)
    (fun q => ((q.1.2.1, q.1.1.1), (q.1.2.2, q.2)))
    poly_emitRebalanceHalfTape ((qG.prod qFls).prod (qHW.prod qLvl))
  exact (ComputableInPolyTime.ite_decide hcond hthen qAcc).of_enc_eq fun q =>
    congrArg (encPair encGates encHalfW) (by dsimp only [safeRebalanceStep])

private theorem emitRebalanceLevel_bounds {g : Gates} {fls : ℕ} {low hi : LevelW} {G W R : ℕ}
    (hfls : (encNat fls).length ≤ W) (hlow1 : ∀ w ∈ low.1, (encNat w).length ≤ W)
    (hhi1 : ∀ w ∈ hi.1, (encNat w).length ≤ W)
    (hlow2 : ∀ row ∈ low.2, row.length ≤ R + 10 ∧ ∀ w ∈ row, (encNat w).length ≤ W)
    (hhi2 : ∀ row ∈ hi.2, row.length ≤ R + 10 ∧ ∀ w ∈ row, (encNat w).length ≤ W)
    (h0 : (encNat 0).length ≤ W) (hG : 4 * W + 11 ≤ G)
    (hg1 : ∀ gt ∈ g.1, (Boolean.encGate gt).length ≤ G)
    (hW : (encNat (g.2 + 37 + 210 * low.2.length)).length ≤ W) :
    let res := emitRebalanceLevel g fls low hi
    (∀ gt ∈ res.1.1, (Boolean.encGate gt).length ≤ G) ∧
    (∀ w ∈ res.2.1.1, (encNat w).length ≤ W) ∧ (∀ w ∈ res.2.2.1, (encNat w).length ≤ W) ∧
    (∀ row ∈ res.2.1.2, row.length = 10 ∧ ∀ w ∈ row, (encNat w).length ≤ W) ∧
    (∀ row ∈ res.2.2.2, row.length = 10 ∧ ∀ w ∈ row, (encNat w).length ≤ W) := by
  have hcnt_wb := emitCntRebalance_bounds (g := g) (fls := fls)
    (lo := low.1) (hi := hi.1) (G := G) (W := W)
    hfls hlow1 hhi1 h0 hG hg1 ((length_encNat_le_of_le (by omega)).trans hW)
  have hfold_wb : ∀ (l : List ℕ) (gc : Gates) (rL rH0 rH1 : List (List ℕ)),
      (∀ gt ∈ gc.1, (Boolean.encGate gt).length ≤ G) →
      gc.2 + 210 * l.length ≤ g.2 + 37 + 210 * low.2.length →
      (∀ row ∈ rL, row.length = 10 ∧ ∀ w ∈ row, (encNat w).length ≤ W) →
      (∀ row ∈ rH0, row.length = 10 ∧ ∀ w ∈ row, (encNat w).length ≤ W) →
      (∀ row ∈ rH1, row.length = 10 ∧ ∀ w ∈ row, (encNat w).length ≤ W) →
      let res := l.foldl (fun (q : Gates × (List (List ℕ) × List (List ℕ) × List (List ℕ))) j =>
        let cr := emitCellRebalance q.1 (low.1.getD 0 0) (low.1.getD 1 0)
          (low.1.getD 4 0) (low.1.getD 5 0)
          (emitCntRebalance g fls low.1 hi.1).2.1.1
          (emitCntRebalance g fls low.1 hi.1).2.1.2.1
          (emitCntRebalance g fls low.1 hi.1).2.1.2.2
          (low.2.getD j []) (hi.2.getD j []) (hi.2.getD (low.2.length + j) [])
        (cr.1, (cr.2.1 :: q.2.1, cr.2.2.1 :: q.2.2.1, cr.2.2.2 :: q.2.2.2))) (gc, (rL, rH0, rH1))
      (∀ gt ∈ res.1.1, (Boolean.encGate gt).length ≤ G) ∧
      (∀ row ∈ res.2.1, row.length = 10 ∧ ∀ w ∈ row, (encNat w).length ≤ W) ∧
      (∀ row ∈ res.2.2.1, row.length = 10 ∧ ∀ w ∈ row, (encNat w).length ≤ W) ∧
      (∀ row ∈ res.2.2.2, row.length = 10 ∧ ∀ w ∈ row, (encNat w).length ≤ W) := by
    intro l; induction l with
    | nil => intro gc rL rH0 rH1 hgc _ h1 h2 h3; exact ⟨hgc, h1, h2, h3⟩
    | cons j tl ih =>
      intro gc rL rH0 rH1 hgc hle h1 h2 h3; simp only [List.foldl_cons]
      have hget_lo : ∀ k, (encNat (low.1.getD k 0)).length ≤ W := fun k => by
        by_cases hk : k < low.1.length
        · rw [List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hk]; exact hlow1 _ (List.getElem_mem hk)
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; exact h0
      have hget_r : ∀ (rows : List (List ℕ)) (k : ℕ),
          (∀ row ∈ rows, row.length ≤ R + 10 ∧ ∀ w ∈ row, (encNat w).length ≤ W) →
          ∀ w ∈ rows.getD k [], (encNat w).length ≤ W := fun rows k hr w hw => by
        by_cases hk : k < rows.length
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk] at hw
          exact (hr _ (List.getElem_mem hk)).2 w hw
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hw; simp at hw
      have hcr := emitCellRebalance_bounds (g := gc) (G := G) (W := W)
        (hget_lo 0) (hget_lo 1) (hget_lo 4) (hget_lo 5)
        hcnt_wb.2.2.2.1 hcnt_wb.2.2.2.2.1 hcnt_wb.2.2.2.2.2.1
        (hget_r _ j hlow2) (hget_r _ j hhi2) (hget_r _ (low.2.length + j) hhi2) h0 hG hgc
        ((length_encNat_le_of_le (by
          simp only [List.length_cons, Nat.mul_succ] at hle; omega)).trans hW)
      exact ih _ _ _ _ hcr.2.2.2.2.2.2.2.2
        (by rw [hcr.2.1]; simp only [List.length_cons, Nat.mul_succ] at hle; omega)
        (fun r hr => by
          simp only [List.mem_cons] at hr
          rcases hr with rfl | hr
          · exact ⟨hcr.2.2.1, hcr.2.2.2.2.2.1⟩
          · exact h1 r hr)
        (fun r hr => by
          simp only [List.mem_cons] at hr
          rcases hr with rfl | hr
          · exact ⟨hcr.2.2.2.1, hcr.2.2.2.2.2.2.1⟩
          · exact h2 r hr)
        (fun r hr => by
          simp only [List.mem_cons] at hr
          rcases hr with rfl | hr
          · exact ⟨hcr.2.2.2.2.1, hcr.2.2.2.2.2.2.2.1⟩
          · exact h3 r hr)
  have hf := hfold_wb (List.range low.2.length) (emitCntRebalance g fls low.1 hi.1).1
    [] [] [] hcnt_wb.2.2.1 (by rw [hcnt_wb.2.1, List.length_range]) (by simp) (by simp) (by simp)
  dsimp only [emitRebalanceLevel_eq]
  refine ⟨hf.1, hcnt_wb.2.2.2.2.2.2.1, hcnt_wb.2.2.2.2.2.2.2,
    fun r hr => hf.2.1 r (List.mem_reverse.mp hr), fun r hr => ?_⟩
  simp only [List.mem_append, List.mem_reverse] at hr
  rcases hr with hr | hr
  · exact hf.2.2.1 r hr
  · exact hf.2.2.2 r hr

theorem getD_take_two_drop {α : Type*} (l : List α) (a b : α) (m i : ℕ) (d : α)
    (hm : m + 2 ≤ l.length) :
    (l.take m ++ [a, b] ++ l.drop (m + 2)).getD i d =
      if i = m then a else if i = m + 1 then b else l.getD i d := by
  have hlen1 : (l.take m).length = m := by simp; omega
  have hlen2 : (l.take m ++ [a, b]).length = m + 2 := by simp [hlen1]
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : i < m
  · have hne1 : i ≠ m := by omega
    have hne2 : i ≠ m + 1 := by omega
    simp only [hne1, hne2, ↓reduceIte]
    rw [List.getElem?_append_left (by rw [hlen2]; omega),
        List.getElem?_append_left (by rw [hlen1]; omega),
        List.getElem?_take_of_lt h1]
  · by_cases h2 : i = m
    · subst h2
      simp only [↓reduceIte]
      rw [List.getElem?_append_left (by rw [hlen2]; omega),
          List.getElem?_append_right (by rw [hlen1]), hlen1, Nat.sub_self]
      rfl
    · by_cases h3 : i = m + 1
      · subst h3
        have hne : m + 1 ≠ m := by omega
        simp only [hne, ↓reduceIte]
        rw [List.getElem?_append_left (by rw [hlen2]; omega),
            List.getElem?_append_right (by rw [hlen1]; omega), hlen1,
            show m + 1 - m = 1 by omega]
        rfl
      · simp only [h2, h3, ↓reduceIte]
        rw [List.getElem?_append_right (by rw [hlen2]; omega), hlen2, List.getElem?_drop,
            Nat.add_sub_cancel' (by omega)]

theorem poly_safeSchedulePass :
    ComputableInPolyTime
      (fun p : ((ℕ × ℕ) × ℕ) × (Gates × HalfW) =>
        safeSchedulePass p.1.1.1 p.1.1.2 p.1.2 p.2.1 p.2.2)
      (encPair (encPair (encPair encUnary encNat) encUnary) (encPair encGates encHalfW))
      (encPair encGates encHalfW) := by
  set P := ((ℕ × ℕ) × ℕ) × (Gates × HalfW)
  set encP : P ↪ List Bool :=
    encPair (encPair (encPair encUnary encNat) encUnary) (encPair encGates encHalfW)
  have hL :=
    poly_fst (poly_fst (ComputableInPolyTime.fst (encPair (encPair encUnary encNat) encUnary)
    (encPair encGates encHalfW)))
  have hfls :=
    poly_snd (poly_fst (ComputableInPolyTime.fst (encPair (encPair encUnary encNat) encUnary)
    (encPair encGates encHalfW)))
  have ht := poly_snd (ComputableInPolyTime.fst (encPair (encPair encUnary encNat) encUnary)
    (encPair encGates encHalfW))
  have hpar : ComputableInPolyTime (fun p : P => (p.1.1.2, p.1.2)) encP (encPair encNat encUnary) :=
    hfls.prod ht
  have hlist : ComputableInPolyTime (fun p : P => List.range (p.1.1.1 -
    1)) encP (encList encUnary) :=
    ComputableInPolyTime.range.comp'
      (ComputableInPolyTime.unary_sub.comp' (hL.prod (ComputableInPolyTime.const 1)))
  have hinit : ComputableInPolyTime (fun p : P => p.2) encP (encPair encGates encHalfW) :=
    ComputableInPolyTime.snd _ _
  have hstep := poly_safeRebalanceStep
  have hsz_poly : PolyBounded (fun p : P => (encP p).length) (fun p : P =>
      let W := 248 * (encP p).length + 10
      let G := (encP p).length + 4 * W + 11
      let M := (encP p).length + 247 * (encP p).length
      let R := (encP p).length + 10
      let L := (encP p).length + 6
      let Lev := 2 * (L * (2 * W + 1)) + 1 + (encP p).length * (2 * (R * (2 * W + 1)) + 1)
      2 * (2 * (M * (2 * G + 1)) + 1 + W) + 1 + (encP p).length * (2 * Lev + 1)) := by
    have hS : PolyBounded (fun p : P => (encP p).length) (fun p : P => (encP p).length) :=
      PolyBounded.self
    have hW := ((PolyBounded.const 248).mul hS).add (PolyBounded.const 10)
    have hG := (hS.add ((PolyBounded.const 4).mul hW)).add (PolyBounded.const 11)
    have hM := hS.add ((PolyBounded.const 247).mul hS)
    have hR := hS.add (PolyBounded.const 10)
    have hL := hS.add (PolyBounded.const 6)
    have hLev := (((PolyBounded.const 2).mul
      (hL.mul (((PolyBounded.const 2).mul hW).add (PolyBounded.const 1)))).add
      (PolyBounded.const 1)).add
      (hS.mul (((PolyBounded.const 2).mul
        (hR.mul (((PolyBounded.const 2).mul hW).add (PolyBounded.const 1)))).add
          (PolyBounded.const 1)))
    have h1 := ((PolyBounded.const 2).mul
      ((((PolyBounded.const 2).mul (hM.mul (((PolyBounded.const 2).mul hG).add
        (PolyBounded.const 1)))).add
        (PolyBounded.const 1)).add hW)).add (PolyBounded.const 1)
    exact h1.add (hS.mul (((PolyBounded.const 2).mul hLev).add (PolyBounded.const 1)))
  have hP_proj : ∀ (p : P),
      (encHalfW p.2.2).length ≤ (encP p).length ∧ (encGates p.2.1).length ≤ (encP p).length ∧
      (encNat p.1.1.2).length ≤ (encP p).length ∧ p.2.1.1.length ≤ (encP p).length ∧
      (encNat p.2.1.2).length ≤ (encP p).length ∧
      ∀ gt ∈ p.2.1.1, (Boolean.encGate gt).length ≤ (encP p).length := by
    intro p
    have hp1 : (encPair (encPair encUnary encNat) encUnary p.1).length ≤ (encP p).length :=
      length_le_encPair_left _ _ p
    have hp2 : (encPair encGates encHalfW p.2).length ≤ (encP p).length :=
      length_le_encPair_right _ _ p
    have hhw : (encHalfW p.2.2).length ≤ (encP p).length :=
      (length_le_encPair_right encGates encHalfW p.2).trans hp2
    have hg : (encGates p.2.1).length ≤ (encP p).length :=
      (length_le_encPair_left encGates encHalfW p.2).trans hp2
    have hfls : (encNat p.1.1.2).length ≤ (encP p).length :=
      ((length_le_encPair_right encUnary encNat p.1.1).trans
        (length_le_encPair_left (encPair encUnary encNat) encUnary p.1)).trans hp1
    have hg1 : (encList Boolean.encGate p.2.1.1).length ≤ (encGates p.2.1).length := by
      change _ ≤ (encPair (encList Boolean.encGate) encNat p.2.1).length; rw [length_encPair]; omega
    have hg2 : (encNat p.2.1.2).length ≤ (encGates p.2.1).length := by
      change _ ≤ (encPair (encList Boolean.encGate) encNat p.2.1).length; rw [length_encPair]; omega
    exact ⟨hhw, hg, hfls, (length_le_encList Boolean.encGate p.2.1.1).trans (by omega), by omega,
      fun gt hgt => (length_le_encList_of_mem Boolean.encGate hgt).trans (by omega)⟩
  have hsum_le_247 : ∀ (hw : HalfW) (m : ℕ),
      ((List.range (min m hw.length)).map fun i => 37 + 210 * (hw.getD i ([], [])).2.length).sum ≤
        247 * (encHalfW hw).length := by
    intro hw m
    have hsub : min m hw.length ≤ hw.length := Nat.min_le_right _ _
    have h1 : ((List.range (min m hw.length)).map fun i => 37 +
      210 * (hw.getD i ([], [])).2.length).sum ≤
        ((List.range hw.length).map fun i => 247 * (1 + (hw.getD i ([], [])).2.length)).sum := by
      have hsplit : List.range hw.length = List.range (min m hw.length) ++
          (List.range (hw.length - min m hw.length)).map (min m hw.length + ·) := by
        have := List.range_add (n := min m hw.length) (m := hw.length - min m hw.length)
        rw [Nat.add_sub_cancel' hsub] at this; exact this
      rw [hsplit, List.map_append, List.sum_append]
      suffices ∀ k, ((List.range k).map fun i => 37 + 210 * (hw.getD i ([], [])).2.length).sum ≤
          ((List.range k).map fun i => 247 * (1 + (hw.getD i ([], [])).2.length)).sum by
        exact (this _).trans (Nat.le_add_right _ _)
      intro k; induction k with
      | zero => simp
      | succ k ih =>
        rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton,
          List.sum_singleton,
          List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]; omega
    have hmul : ∀ (l : List ℕ) (f : ℕ →
      ℕ), (l.map fun i => 247 * f i).sum = 247 * (l.map f).sum := by
      intro l f; induction l with | nil => simp | cons a tl iht => simp [iht]; ring
    rw [hmul] at h1
    exact h1.trans (Nat.mul_le_mul_left 247 (sum_getD_rows_le_encHalfW hw))
  exact (ComputableInPolyTime.foldlWith_spec
    (step := fun (par : ℕ × ℕ) (acc : Gates × HalfW) (lvl : ℕ) =>
      safeRebalanceStep par.1 par.2 acc lvl)
    hpar hlist hinit hstep
    (fun p consumed acc =>
      let W := 248 * (encP p).length + 10
      let G := (encP p).length + 4 * W + 11
      let hw0 := p.2.2
      acc.2.length = hw0.length ∧
      (∀ i < hw0.length, (acc.2.getD i ([], [])).2.length = (hw0.getD i ([], [])).2.length) ∧
      (∀ lv ∈ acc.2, lv.1.length ≤ (encP p).length + 6 ∧
        (∀ w ∈ lv.1, (encNat w).length ≤ W) ∧
        (∀ r ∈ lv.2, r.length ≤ (encP p).length + 10 ∧ ∀ w ∈ r, (encNat w).length ≤ W)) ∧
      (∀ gt ∈ acc.1.1, (Boolean.encGate gt).length ≤ G) ∧
      acc.1.1.length ≤ p.2.1.1.length +
        ((List.range (min consumed.length hw0.length)).map
          fun i => 37 + 210 * (hw0.getD i ([], [])).2.length).sum ∧
      acc.1.2 ≤ p.2.1.2 +
        ((List.range (min consumed.length hw0.length)).map
          fun i => 37 + 210 * (hw0.getD i ([], [])).2.length).sum)
    (fun p => by
      obtain ⟨hhw_le, _, _, _, _, hgb⟩ := hP_proj p
      refine ⟨rfl, fun _ _ => rfl, fun lv hlv => ?_, fun gt hgt => (hgb gt hgt).trans (by omega),
        by simp, by simp⟩
      have hlv_le := (length_le_encList_of_mem encLevelW hlv).trans hhw_le
      have hlv1 : (encList encNat lv.1).length ≤ (encLevelW lv).length := by
        change _ ≤ (encPair (encList encNat)
          (encList (encList encNat)) lv).length; rw [length_encPair]; omega
      exact ⟨(length_le_encList encNat lv.1).trans (by omega),
        fun w hw => ((length_le_encList_of_mem encNat hw).trans hlv1).trans (by omega),
        fun r hr => ⟨(length_le_encList encNat r).trans ((length_encRow_of_mem hr).trans
          (by omega)),
          fun w hw => (length_le_encList_of_mem encNat hw).trans
            ((length_encRow_of_mem hr).trans (by omega))⟩⟩)
    (fun p consumed acc lvl hpref hinv => by
      rcases hinv with ⟨hlen, hrows, hmem, hgb, hgl, hg2⟩
      obtain ⟨hhw_le, _, hfls, _, hg2_0, _⟩ := hP_proj p
      dsimp only [safeRebalanceStep]
      by_cases hc : (p.1.2 + 1) % 2 ^ (lvl + 1) = 0 ∧ lvl + 1 < acc.2.length ∧
          (acc.2.getD (lvl + 1) ([], [])).2.length = 2 * (acc.2.getD lvl ([], [])).2.length
      · simp only [hc, and_self, ↓reduceIte]
        have hlvl_eq : lvl = consumed.length := by
          have hget : (consumed ++ [lvl])[consumed.length]'(by simp) =
              (List.range (p.1.1.1 - 1))[consumed.length]'(by
                have := hpref.length_le; simp at this ⊢; omega) :=
            List.IsPrefix.getElem hpref (by simp)
          simpa using hget
        have hrow_lvl : (acc.2.getD lvl ([], [])).2.length = (p.2.2.getD lvl ([], [])).2.length :=
          hrows lvl (by omega)
        have hmin1 : min (consumed.length + 1) p.2.2.length = lvl + 1 := by omega
        have hmin0 : min consumed.length p.2.2.length = lvl := by omega
        have hsum_step : ((List.range (min consumed.length p.2.2.length)).map
            fun i => 37 + 210 * (p.2.2.getD i ([], [])).2.length).sum +
            (37 + 210 * (p.2.2.getD lvl ([], [])).2.length) =
            ((List.range (min (consumed.length + 1) p.2.2.length)).map
              fun i => 37 + 210 * (p.2.2.getD i ([], [])).2.length).sum := by
          rw [hmin1, List.range_succ, List.map_append, List.sum_append, List.map_singleton,
            List.sum_singleton, ← hmin0]
        have hsum_247 :=
          (hsum_le_247 p.2.2 (consumed.length + 1)).trans (Nat.mul_le_mul_left 247 hhw_le)
        set W := 248 * (encP p).length + 10
        set G := (encP p).length + 4 * W + 11
        have hW_step : (encNat (acc.1.2 + 37 + 210 * (acc.2.getD lvl ([], [])).2.length)).length ≤
          W := by
          have : acc.1.2 + 37 + 210 * (acc.2.getD lvl ([], [])).2.length ≤
            p.2.1.2 + 247 * (encP p).length := by
            rw [hrow_lvl]; omega
          exact (length_encNat_le_add this).trans (by omega)
        have h0_b : (encNat 0).length ≤ W := by simp [encNat_apply, W]
        have hlow_b := hmem (acc.2.getD lvl ([], [])) (by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
          exact List.getElem_mem (by omega))
        have hhi_b := hmem (acc.2.getD (lvl + 1) ([], [])) (by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc.2.1]
          exact List.getElem_mem hc.2.1)
        have hrb_l := emitRebalanceLevel_row_lengths acc.1 p.1.1.2
          (acc.2.getD lvl ([], [])) (acc.2.getD (lvl + 1) ([], []))
        have hrb_wb := emitRebalanceLevel_bounds (g := acc.1) (fls := p.1.1.2)
          (low := acc.2.getD lvl ([], [])) (hi := acc.2.getD (lvl + 1) ([], []))
          (G := G) (W := W) (R := (encP p).length)
          (hfls.trans (by omega)) hlow_b.2.1 hhi_b.2.1 hlow_b.2.2 hhi_b.2.2 h0_b
            (by omega) hgb hW_step
        refine ⟨by simp [emitRebalanceHalfTape_eq, hlen]; omega, fun i hi => ?_, fun lv hlv => ?_,
          by dsimp only [emitRebalanceHalfTape_eq]; exact hrb_wb.1,
          by dsimp only [emitRebalanceHalfTape_eq]; rw [hrb_l.2.2.2.2.1,
            hrow_lvl]; simp only [List.length_append, List.length_singleton]; omega,
          by dsimp only [emitRebalanceHalfTape_eq]; rw [hrb_l.2.2.2.2.2,
            hrow_lvl]; simp only [List.length_append, List.length_singleton]; omega⟩
        · dsimp only [emitRebalanceHalfTape_eq]
          rw [getD_take_two_drop acc.2 _ _ lvl i ([], []) (by omega)]
          by_cases h1 : i = lvl
          · subst h1; simp only [↓reduceIte]; rw [hrb_l.2.2.1]; exact hrows i hi
          · by_cases h2 : i = lvl + 1
            · subst h2; simp only [h1, ↓reduceIte]; rw [hrb_l.2.2.2.1, ← hc.2.2]; exact hrows (lvl +
              1) hi
            · simp only [h1, h2, ↓reduceIte]; exact hrows i hi
        · dsimp only [emitRebalanceHalfTape_eq] at hlv
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hlv
          rcases hlv with (hlv | (rfl | rfl)) | hlv
          · exact hmem lv (List.mem_of_mem_take hlv)
          · exact ⟨by rw [hrb_l.1]; omega, hrb_wb.2.1, fun r hr =>
              ⟨by rw [(hrb_wb.2.2.2.1 r hr).1]; omega, (hrb_wb.2.2.2.1 r hr).2⟩⟩
          · exact ⟨by rw [hrb_l.2.1]; omega, hrb_wb.2.2.1, fun r hr =>
              ⟨by rw [(hrb_wb.2.2.2.2 r hr).1]; omega, (hrb_wb.2.2.2.2 r hr).2⟩⟩
          · exact hmem lv (List.mem_of_mem_drop hlv)
      · simp only [hc, ↓reduceIte]
        have hmono : ((List.range (min consumed.length p.2.2.length)).map
            fun i => 37 + 210 * (p.2.2.getD i ([], [])).2.length).sum ≤
            ((List.range (min (consumed.length + 1) p.2.2.length)).map
              fun i => 37 + 210 * (p.2.2.getD i ([], [])).2.length).sum := by
          by_cases hlt : consumed.length < p.2.2.length
          · rw [show min consumed.length p.2.2.length = consumed.length by omega,
                show min (consumed.length + 1) p.2.2.length = consumed.length + 1 by omega,
                List.range_succ, List.map_append, List.sum_append]; omega
          · rw [show min consumed.length p.2.2.length = p.2.2.length by omega,
                show min (consumed.length + 1) p.2.2.length = p.2.2.length by omega]
        exact ⟨hlen, hrows, hmem, hgb,
          by simp only [List.length_append, List.length_singleton]; omega,
          by simp only [List.length_append, List.length_singleton]; omega⟩)
    hsz_poly
    (fun p consumed acc _ hinv => by
      rcases hinv with ⟨hlen, hrows, hmem, hgb, hgl, hg2⟩
      obtain ⟨hhw_enc, _, _, hg_len, hg2_0, _⟩ := hP_proj p
      set W := 248 * (encP p).length + 10
      set G := (encP p).length + 4 * W + 11
      have hsum_247 := (hsum_le_247 p.2.2 consumed.length).trans (Nat.mul_le_mul_left 247 hhw_enc)
      have hacc1_2 : (encNat acc.1.2).length ≤ W :=
        (length_encNat_le_add (by omega : acc.1.2 ≤
          p.2.1.2 + 247 * (encP p).length)).trans (by omega)
      have hG_b := length_encGates_le (by omega : acc.1.1.length ≤
        (encP p).length + 247 * (encP p).length) hgb hacc1_2
      have hhw_b : (encHalfW acc.2).length ≤ (encP p).length *
          (2 * (2 * (((encP p).length + 6) * (2 * W + 1)) + 1 +
            (encP p).length * (2 * (((encP p).length + 10) * (2 * W + 1)) + 1)) + 1) := by
        refine (length_encList_le encLevelW acc.2 fun lv hlv => ?_).trans
          (Nat.mul_le_mul_right _ (by rw [hlen]; exact
            (length_le_encList encLevelW p.2.2).trans hhw_enc))
        have hlv_len : lv.2.length ≤ (encP p).length := by
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hlv
          have hi' : i < p.2.2.length := by omega
          have hri : acc.2[i].2.length = (p.2.2.getD i ([], [])).2.length := by
            simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] using hrows i hi'
          have h1 : (p.2.2.getD i ([], [])).2.length ≤
            (encLevelW (p.2.2.getD i ([], []))).length := by
            change _ ≤ (encPair (encList encNat)
              (encList (encList encNat)) _).length; rw [length_encPair]
            have := length_le_encList (encList encNat) (p.2.2.getD i ([], [])).2; omega
          have h2 : p.2.2.getD i ([], []) ∈ p.2.2 := by
            rw [List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem hi']; exact List.getElem_mem hi'
          exact hri ▸ h1.trans ((length_le_encList_of_mem encLevelW h2).trans hhw_enc)
        exact length_encLevelW_le (hmem lv hlv).1 (hmem lv hlv).2.1 hlv_len (hmem lv hlv).2.2
      rw [length_encPair]; dsimp only [W, G] at hG_b hhw_b ⊢; linarith)).1.of_enc_eq fun p =>
    congrArg (encPair encGates encHalfW) (by dsimp only [safeSchedulePass])

/-! ### Guarded TM step `safeTmStep` and its polynomial-time certificate -/

private theorem poly_pickWires_orList {k numStates : ℕ} {γ : Type} {encIn : γ ↪ List Bool}
    (sits : List (ActiveSit k numStates)) (pred : ActiveSit k numStates → Bool)
    {fg : γ → Gates} {fbase : γ → ℕ} {finds : γ → List ℕ}
    (hg : ComputableInPolyTime fg encIn encGates)
    (hbase : ComputableInPolyTime fbase encIn encNat)
    (hinds : ComputableInPolyTime finds encIn (encList encNat)) :
    ComputableInPolyTime (fun x => Gates.gOrList (fg x) (fbase x) (pickWires sits (finds x) pred))
      encIn (encPair encGates encNat) := by
  simp only [pickWires_eq]
  exact poly_gOrList_const
    ((List.range sits.length).filter fun idx => (sits[idx]?.map fun sit => pred sit).getD false)
    fg fbase (fun x idx => (finds x).getD idx 0) hg hbase
    (fun idx _ => poly_getD_const hinds idx 0)

/-- Apply `safeSchedulePass` to both half-tapes of a `TapeW` sequentially. -/
@[expose] noncomputable def safeDoubleSchedule (L fls t : ℕ) (g : Gates) (tw : TapeW) :
    Gates × TapeW :=
  let rL := safeSchedulePass L fls t g tw.2.1
  let rR := safeSchedulePass L fls t rL.1 tw.2.2
  (rR.1, (tw.1, (rL.2, rR.2)))

private theorem poly_safeDoubleSchedule :
    ComputableInPolyTime
      (fun p : ((ℕ × ℕ) × ℕ) × (Gates × TapeW) =>
        safeDoubleSchedule p.1.1.1 p.1.1.2 p.1.2 p.2.1 p.2.2)
      (encPair (encPair (encPair encUnary encNat) encUnary) (encPair encGates encTapeW))
      (encPair encGates encTapeW) := by
  set P := ((ℕ × ℕ) × ℕ) × (Gates × TapeW)
  set encP : P ↪ List Bool :=
    encPair (encPair (encPair encUnary encNat) encUnary) (encPair encGates encTapeW)
  have h1 := ComputableInPolyTime.fst (encPair (encPair encUnary encNat) encUnary)
    (encPair encGates encTapeW)
  have h2 := ComputableInPolyTime.snd (encPair (encPair encUnary encNat) encUnary)
    (encPair encGates encTapeW)
  have htw := poly_snd h2
  have hrL := @ComputableInPolyTime.comp' P _ _ encP _ _
    (fun q : ((ℕ × ℕ) × ℕ) × (Gates × HalfW) =>
      safeSchedulePass q.1.1.1 q.1.1.2 q.1.2 q.2.1 q.2.2)
    _ poly_safeSchedulePass (h1.prod ((poly_fst h2).prod (poly_fst (poly_snd htw))))
  have hrR := @ComputableInPolyTime.comp' P _ _ encP _ _
    (fun q : ((ℕ × ℕ) × ℕ) × (Gates × HalfW) =>
      safeSchedulePass q.1.1.1 q.1.1.2 q.1.2 q.2.1 q.2.2)
    _ poly_safeSchedulePass (h1.prod ((poly_fst hrL).prod (poly_snd (poly_snd htw))))
  exact (poly_fst hrR).prod ((poly_fst htw).prod ((poly_snd hrL).prod (poly_snd hrR)))

/-- Work-tape head movement indicator wires (guarded stage 1). -/
@[expose] noncomputable def safeWkMoves {k numStates : ℕ} {State : Type}
    (e : State ≃ Fin numStates) (tm : MultiTapeTM k Bool State)
    (fls sHalt : ℕ) (inds : List ℕ) (gc : Gates) (r : Fin k) : Gates × ℕ × ℕ × ℕ :=
  let sits := allActiveSits k numStates
  let act : ActiveSit k numStates → Action k Bool State := fun sit =>
    tm.tr (e.symm sit.1) sit.2.1.toOption (fun r' => (sit.2.2 r').toOption)
  let r1 := Gates.gOrList gc fls
    (pickWires sits inds fun sit => decide (((act sit).workTapes r).2 = .neg))
  let r2 := Gates.gOrList r1.1 sHalt
    (pickWires sits inds fun sit => decide (((act sit).workTapes r).2 = .zero))
  let r3 := Gates.gOrList r2.1 fls
    (pickWires sits inds fun sit => decide (((act sit).workTapes r).2 = .pos))
  (r3.1, (r1.2, r2.2, r3.2))

/-- Work-tape cell-write wires (guarded stage 2). -/
@[expose] noncomputable def safeWkWrite {k numStates : ℕ} {State : Type}
    (e : State ≃ Fin numStates) (tm : MultiTapeTM k Bool State)
    (sHalt : ℕ) (inds : List ℕ) (tw : TapeW) (gc : Gates) (r : Fin k) : Gates × ℕ × ℕ :=
  let sits := allActiveSits k numStates
  let act : ActiveSit k numStates → Action k Bool State := fun sit =>
    tm.tr (e.symm sit.1) sit.2.1.toOption (fun r' => (sit.2.2 r').toOption)
  let wkCell := fun (sit : ActiveSit k numStates) =>
    match ((act sit).workTapes r).1 with
    | none => sit.2.2 r
    | some s => BlockCell.ofOption s
  let r4 := Gates.gAnd gc sHalt tw.1.1
  let r5 := Gates.gAnd r4.1 sHalt tw.1.2
  let r6 := Gates.gOrList r5.1 r4.2 (pickWires sits inds fun sit => (wkCell sit).1)
  let r7 := Gates.gOrList r6.1 r5.2 (pickWires sits inds fun sit => (wkCell sit).2)
  (r7.1, (r6.2, r7.2))

/-- Guarded single work-tape step using `safeSchedulePass`. -/
@[expose] noncomputable def safeWorkTapeStep {k numStates : ℕ} {State : Type}
    (e : State ≃ Fin numStates) (tm : MultiTapeTM k Bool State)
    (L fls t sHalt : ℕ) (inds : List ℕ) (tw : TapeW) (gc : Gates) (r : Fin k) :
    Gates × TapeW :=
  let m := safeWkMoves e tm fls sHalt inds gc r
  let w := safeWkWrite e tm sHalt inds tw m.1 r
  let t0 := emitTapeStep0 w.1 fls m.2.1 m.2.2.1 m.2.2.2 w.2.1 w.2.2 tw
  safeDoubleSchedule L fls t t0.1 t0.2

private theorem poly_safeWkMoves {k numStates : ℕ} {State : Type}
    (e : State ≃ Fin numStates) (tm : MultiTapeTM k Bool State) (r : Fin k) :
    ComputableInPolyTime
      (fun p : ((ℕ × ℕ) × List ℕ) × Gates => safeWkMoves e tm p.1.1.1 p.1.1.2 p.1.2 p.2 r)
      (encPair (encPair (encPair encNat encNat) (encList encNat)) encGates)
      (encPair encGates (encPair encNat (encPair encNat encNat))) := by
  set P := ((ℕ × ℕ) × List ℕ) × Gates
  set encP : P ↪ List Bool :=
    encPair (encPair (encPair encNat encNat) (encList encNat)) encGates
  let sits := allActiveSits k numStates
  let act : ActiveSit k numStates → Action k Bool State := fun sit =>
    tm.tr (e.symm sit.1) sit.2.1.toOption (fun r' => (sit.2.2 r').toOption)
  have hfls : ComputableInPolyTime (fun p : P => p.1.1.1) encP encNat :=
    poly_fst (poly_fst (ComputableInPolyTime.fst _ _))
  have hsH : ComputableInPolyTime (fun p : P => p.1.1.2) encP encNat :=
    poly_snd (poly_fst (ComputableInPolyTime.fst _ _))
  have hinds : ComputableInPolyTime (fun p : P => p.1.2) encP (encList encNat) :=
    poly_snd (ComputableInPolyTime.fst _ _)
  have hg : ComputableInPolyTime (fun p : P => p.2) encP encGates :=
    ComputableInPolyTime.snd _ _
  have r1 := poly_pickWires_orList sits (fun sit => decide (((act sit).workTapes r).2 = .neg))
    hg hfls hinds
  have r2 := poly_pickWires_orList sits (fun sit => decide (((act sit).workTapes r).2 = .zero))
    (poly_fst r1) hsH hinds
  have r3 := poly_pickWires_orList sits (fun sit => decide (((act sit).workTapes r).2 = .pos))
    (poly_fst r2) hfls hinds
  exact (poly_fst r3).prod ((poly_snd r1).prod ((poly_snd r2).prod (poly_snd r3)))

private theorem poly_safeWkWrite {k numStates : ℕ} {State : Type}
    (e : State ≃ Fin numStates) (tm : MultiTapeTM k Bool State) (r : Fin k) :
    ComputableInPolyTime
      (fun p : (ℕ × List ℕ) × (Gates × TapeW) =>
        safeWkWrite e tm p.1.1 p.1.2 p.2.2 p.2.1 r)
      (encPair (encPair encNat (encList encNat)) (encPair encGates encTapeW))
      (encPair encGates (encPair encNat encNat)) := by
  set P := (ℕ × List ℕ) × (Gates × TapeW)
  set encP : P ↪ List Bool :=
    encPair (encPair encNat (encList encNat)) (encPair encGates encTapeW)
  let sits := allActiveSits k numStates
  let act : ActiveSit k numStates → Action k Bool State := fun sit =>
    tm.tr (e.symm sit.1) sit.2.1.toOption (fun r' => (sit.2.2 r').toOption)
  let wkCell := fun (sit : ActiveSit k numStates) =>
    match ((act sit).workTapes r).1 with | none => sit.2.2 r | some s => BlockCell.ofOption s
  have hsH : ComputableInPolyTime (fun p : P => p.1.1) encP encNat :=
    poly_fst (ComputableInPolyTime.fst _ _)
  have hinds : ComputableInPolyTime (fun p : P => p.1.2) encP (encList encNat) :=
    poly_snd (ComputableInPolyTime.fst _ _)
  have hg : ComputableInPolyTime (fun p : P => p.2.1) encP encGates :=
    poly_fst (ComputableInPolyTime.snd _ _)
  have htw0 : ComputableInPolyTime (fun p : P => p.2.2.1.1) encP encNat :=
    poly_fst (poly_fst (poly_snd (ComputableInPolyTime.snd _ _)))
  have htw1 : ComputableInPolyTime (fun p : P => p.2.2.1.2) encP encNat :=
    poly_snd (poly_fst (poly_snd (ComputableInPolyTime.snd _ _)))
  have r4 := poly_gAnd' hg hsH htw0
  have r5 := poly_gAnd' (poly_fst r4) hsH htw1
  have r6 := poly_pickWires_orList sits (fun sit => (wkCell sit).1)
    (poly_fst r5) (poly_snd r4) hinds
  have r7 := poly_pickWires_orList sits (fun sit => (wkCell sit).2)
    (poly_fst r6) (poly_snd r5) hinds
  exact (poly_fst r7).prod ((poly_snd r6).prod (poly_snd r7))

private theorem poly_safeWorkTapeStep {k numStates : ℕ} {State : Type}
    (e : State ≃ Fin numStates) (tm : MultiTapeTM k Bool State) (r : Fin k) :
    ComputableInPolyTime
      (fun p : (((ℕ × ℕ) × ℕ) × (ℕ × List ℕ)) × (Gates × TapeW) =>
        safeWorkTapeStep e tm p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2.1 p.1.2.2 p.2.2 p.2.1 r)
      (encPair
        (encPair (encPair (encPair encUnary encNat) encUnary) (encPair encNat (encList encNat)))
        (encPair encGates encTapeW))
      (encPair encGates encTapeW) := by
  set P := (((ℕ × ℕ) × ℕ) × (ℕ × List ℕ)) × (Gates × TapeW)
  set encP : P ↪ List Bool :=
    encPair
      (encPair (encPair (encPair encUnary encNat) encUnary) (encPair encNat (encList encNat)))
      (encPair encGates encTapeW)
  have hL : ComputableInPolyTime (fun p : P => p.1.1.1.1) encP encUnary :=
    poly_fst (poly_fst (poly_fst (ComputableInPolyTime.fst _ _)))
  have hfls : ComputableInPolyTime (fun p : P => p.1.1.1.2) encP encNat :=
    poly_snd (poly_fst (poly_fst (ComputableInPolyTime.fst _ _)))
  have ht : ComputableInPolyTime (fun p : P => p.1.1.2) encP encUnary :=
    poly_snd (poly_fst (ComputableInPolyTime.fst _ _))
  have hsH : ComputableInPolyTime (fun p : P => p.1.2.1) encP encNat :=
    poly_fst (poly_snd (ComputableInPolyTime.fst _ _))
  have hinds : ComputableInPolyTime (fun p : P => p.1.2.2) encP (encList encNat) :=
    poly_snd (poly_snd (ComputableInPolyTime.fst _ _))
  have hg : ComputableInPolyTime (fun p : P => p.2.1) encP encGates :=
    poly_fst (ComputableInPolyTime.snd _ _)
  have htw : ComputableInPolyTime (fun p : P => p.2.2) encP encTapeW :=
    poly_snd (ComputableInPolyTime.snd _ _)
  have hm := @ComputableInPolyTime.comp' P _ _ encP _ _
    (fun q : ((ℕ × ℕ) × List ℕ) × Gates => safeWkMoves e tm q.1.1.1 q.1.1.2 q.1.2 q.2 r)
    _ (poly_safeWkMoves e tm r) (((hfls.prod hsH).prod hinds).prod hg)
  have hw := @ComputableInPolyTime.comp' P _ _ encP _ _
    (fun q : (ℕ × List ℕ) × (Gates × TapeW) => safeWkWrite e tm q.1.1 q.1.2 q.2.2 q.2.1 r)
    _ (poly_safeWkWrite e tm r) ((hsH.prod hinds).prod ((poly_fst hm).prod htw))
  have hr8 := @ComputableInPolyTime.comp' P _ _ encP _ _
    (fun q : (Gates × ℕ) × ((ℕ × ℕ × ℕ) × (ℕ × ℕ) × TapeW) =>
      emitTapeStep0 q.1.1 q.1.2 q.2.1.1 q.2.1.2.1 q.2.1.2.2 q.2.2.1.1 q.2.2.1.2 q.2.2.2)
    _ poly_emitTapeStep0
    (((poly_fst hw).prod hfls).prod ((poly_snd hm).prod ((poly_snd hw).prod htw)))
  have hfin := poly_safeDoubleSchedule.comp' (((hL.prod hfls).prod ht).prod hr8)
  exact hfin.of_enc_eq fun _ => rfl

/-- Input and work-tape head negations (guarded stage 1). -/
@[expose] noncomputable def safeTmNegs {k : ℕ} (g : Gates) (sw : StateW) :
    Gates × ((ℕ × ℕ) × (List ℕ × List ℕ)) :=
  let r1 := Gates.gNot g sw.2.1.1.1
  let r2 := Gates.gNot r1.1 sw.2.1.1.2
  let r3 := emitMap r2.1 (fun gc (r : Fin k) =>
    Gates.gNot gc (sw.2.2.getD r.val defaultTapeW).1.1) (List.finRange k)
  let r4 := emitMap r3.1 (fun gc (r : Fin k) =>
    Gates.gNot gc (sw.2.2.getD r.val defaultTapeW).1.2) (List.finRange k)
  (r4.1, ((r1.2, r2.2), (r3.2, r4.2)))

/-- Next-state and next-output wires (guarded stage 3). -/
@[expose] noncomputable def safeTmStateOut {k numStates : ℕ} {State : Type}
    (e : State ≃ Fin numStates) (tm : MultiTapeTM k Bool State)
    (fls sHalt : ℕ) (outW : List ℕ) (inds : List ℕ) (g : Gates) :
    Gates × (List ℕ × List ℕ) :=
  let sits := allActiveSits k numStates
  let act : ActiveSit k numStates → Action k Bool State := fun sit =>
    tm.tr (e.symm sit.1) sit.2.1.toOption (fun r => (sit.2.2 r).toOption)
  let r6 := Gates.gOrList g sHalt
    (pickWires sits inds fun sit => decide ((act sit).state = none))
  let r7 := emitMap r6.1 (fun gc (q' : Fin numStates) =>
    Gates.gOrList gc fls
      (pickWires sits inds fun sit => decide ((act sit).state.map e = some q')))
    (List.finRange numStates)
  let r8 := Gates.gOrList r7.1 fls
    (pickWires sits inds fun sit => decide ((act sit).output = none))
  let r9 := Gates.gOrList r8.1 fls
    (pickWires sits inds fun sit => decide ((act sit).output = some false))
  let r10 := Gates.gOrList r9.1 fls
    (pickWires sits inds fun sit => decide ((act sit).output = some true))
  let r11 := emitOutUpdate r10.1 sHalt r8.2 r9.2 r10.2 outW
  (r11.1, (r6.2 :: r7.2, r11.2))

/-- Input-tape update with guarded scheduled rebalancing (guarded stage 4). -/
@[expose] noncomputable def safeTmInTape {k numStates : ℕ} {State : Type}
    (e : State ≃ Fin numStates) (tm : MultiTapeTM k Bool State)
    (L fls t sHalt : ℕ) (inds : List ℕ) (inTape : TapeW) (g : Gates) :
    Gates × TapeW :=
  let sits := allActiveSits k numStates
  let act : ActiveSit k numStates → Action k Bool State := fun sit =>
    tm.tr (e.symm sit.1) sit.2.1.toOption (fun r => (sit.2.2 r).toOption)
  let r12 := Gates.gOrList g fls (pickWires sits inds fun sit =>
    decide (ObliviousCfg.clampInputMove sit.2.1 (act sit).inputTape = .neg))
  let r13 := Gates.gOrList r12.1 sHalt (pickWires sits inds fun sit =>
    decide (ObliviousCfg.clampInputMove sit.2.1 (act sit).inputTape = .zero))
  let r14 := Gates.gOrList r13.1 fls (pickWires sits inds fun sit =>
    decide (ObliviousCfg.clampInputMove sit.2.1 (act sit).inputTape = .pos))
  let r15 := emitTapeStep0 r14.1 fls r12.2 r13.2 r14.2 inTape.1.1 inTape.1.2 inTape
  safeDoubleSchedule L fls t r15.1 r15.2

/-- Guarded full TM step using `safeSchedulePass` on all tapes. -/
@[expose] noncomputable def safeTmStep {k numStates : ℕ} {State : Type}
    (e : State ≃ Fin numStates) (tm : MultiTapeTM k Bool State)
    (L fls tru t : ℕ) (g : Gates) (sw : StateW) : Gates × StateW :=
  let negs := safeTmNegs (k := k) g sw
  let ind := emitIndicators negs.1 tru sw negs.2.1.1 negs.2.1.2 negs.2.2.1 negs.2.2.2
    (allActiveSits k numStates)
  let sHalt := sw.1.1.getD 0 0
  let so := safeTmStateOut e tm fls sHalt sw.1.2 ind.2 ind.1
  let inT := safeTmInTape e tm L fls t sHalt ind.2 sw.2.1 so.1
  let resWk := (List.finRange k).foldl (fun (acc : Gates × List TapeW) (r : Fin k) =>
    let p := safeWorkTapeStep e tm L fls t sHalt ind.2
      (sw.2.2.getD r.val defaultTapeW) acc.1 r
    (p.1, p.2 :: acc.2)) (inT.1, [])
  (resWk.1, (so.2, (inT.2, resWk.2.reverse)))

private theorem poly_safeTmNegs {k : ℕ} :
    ComputableInPolyTime (fun p : Gates × StateW => safeTmNegs (k := k) p.1 p.2)
      (encPair encGates encStateW)
      (encPair encGates
        (encPair (encPair encNat encNat) (encPair (encList encNat) (encList encNat)))) := by
  set P := Gates × StateW
  set encP : P ↪ List Bool := encPair encGates encStateW
  have hg := ComputableInPolyTime.fst encGates encStateW
  have hsw22 : ComputableInPolyTime (fun p : P => p.2.2.2) encP (encList encTapeW) :=
    poly_snd (poly_snd (ComputableInPolyTime.snd _ _))
  have hin0 : ComputableInPolyTime (fun p : P => p.2.2.1.1.1) encP encNat :=
    poly_fst (poly_fst (poly_fst (poly_snd (ComputableInPolyTime.snd _ _))))
  have hin1 : ComputableInPolyTime (fun p : P => p.2.2.1.1.2) encP encNat :=
    poly_snd (poly_fst (poly_fst (poly_snd (ComputableInPolyTime.snd _ _))))
  have r1 := poly_gNot' hg hin0
  have r2 := poly_gNot' (poly_fst r1) hin1
  have hmap0 := poly_emitMap_const (List.finRange k)
    (fun (w : List TapeW) gc (r : Fin k) => Gates.gNot gc (w.getD r.val defaultTapeW).1.1)
    (fun r _ => poly_gNot' (ComputableInPolyTime.snd (encList encTapeW) encGates)
      (poly_fst (poly_fst (poly_getD_const
        (ComputableInPolyTime.fst (encList encTapeW) encGates) r.val defaultTapeW))))
  have r3 := @ComputableInPolyTime.comp' P (List TapeW × Gates) (Gates × List ℕ) encP
    (encPair (encList encTapeW) encGates) (encPair encGates (encList encNat)) _ _
    hmap0 (hsw22.prod (poly_fst r2))
  have hmap1 := poly_emitMap_const (List.finRange k)
    (fun (w : List TapeW) gc (r : Fin k) => Gates.gNot gc (w.getD r.val defaultTapeW).1.2)
    (fun r _ => poly_gNot' (ComputableInPolyTime.snd (encList encTapeW) encGates)
      (poly_snd (poly_fst (poly_getD_const
        (ComputableInPolyTime.fst (encList encTapeW) encGates) r.val defaultTapeW))))
  have r4 := @ComputableInPolyTime.comp' P (List TapeW × Gates) (Gates × List ℕ) encP
    (encPair (encList encTapeW) encGates) (encPair encGates (encList encNat)) _ _
    hmap1 (hsw22.prod (poly_fst r3))
  exact (poly_fst r4).prod
    (((poly_snd r1).prod (poly_snd r2)).prod ((poly_snd r3).prod (poly_snd r4)))

private theorem poly_safeTmStateOut {k numStates : ℕ} {State : Type}
    (e : State ≃ Fin numStates) (tm : MultiTapeTM k Bool State) :
    ComputableInPolyTime
      (fun p : ((ℕ × ℕ) × (List ℕ × List ℕ)) × Gates =>
        safeTmStateOut e tm p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2 p.2)
      (encPair (encPair (encPair encNat encNat) (encPair (encList encNat) (encList encNat)))
        encGates)
      (encPair encGates (encPair (encList encNat) (encList encNat))) := by
  set P := ((ℕ × ℕ) × (List ℕ × List ℕ)) × Gates
  set encP : P ↪ List Bool :=
    encPair (encPair (encPair encNat encNat) (encPair (encList encNat) (encList encNat))) encGates
  let sits := allActiveSits k numStates
  let act : ActiveSit k numStates → Action k Bool State := fun sit =>
    tm.tr (e.symm sit.1) sit.2.1.toOption (fun r => (sit.2.2 r).toOption)
  have hfls : ComputableInPolyTime (fun p : P => p.1.1.1) encP encNat :=
    poly_fst (poly_fst (ComputableInPolyTime.fst _ _))
  have hsH : ComputableInPolyTime (fun p : P => p.1.1.2) encP encNat :=
    poly_snd (poly_fst (ComputableInPolyTime.fst _ _))
  have hout : ComputableInPolyTime (fun p : P => p.1.2.1) encP (encList encNat) :=
    poly_fst (poly_snd (ComputableInPolyTime.fst _ _))
  have hinds : ComputableInPolyTime (fun p : P => p.1.2.2) encP (encList encNat) :=
    poly_snd (poly_snd (ComputableInPolyTime.fst _ _))
  have hg : ComputableInPolyTime (fun p : P => p.2) encP encGates :=
    ComputableInPolyTime.snd _ _
  have r6 := poly_pickWires_orList sits (fun sit => decide ((act sit).state = none))
    hg hsH hinds
  have hr7_aux := poly_emitMap_const (List.finRange numStates)
    (fun (par : ℕ × List ℕ) gc (q' : Fin numStates) =>
      Gates.gOrList gc par.1
        (pickWires sits par.2 fun sit => decide ((act sit).state.map e = some q')))
    (fun q' _ => poly_pickWires_orList sits (fun sit => decide ((act sit).state.map e = some q'))
      (ComputableInPolyTime.snd (encPair encNat (encList encNat)) encGates)
      (poly_fst (ComputableInPolyTime.fst (encPair encNat (encList encNat)) encGates))
      (poly_snd (ComputableInPolyTime.fst (encPair encNat (encList encNat)) encGates)))
  have r7 := @ComputableInPolyTime.comp' P ((ℕ × List ℕ) × Gates) (Gates × List ℕ) encP _ _ _ _
    hr7_aux ((hfls.prod hinds).prod (poly_fst r6))
  have r8 := poly_pickWires_orList sits (fun sit => decide ((act sit).output = none))
    (poly_fst r7) hfls hinds
  have r9 := poly_pickWires_orList sits (fun sit => decide ((act sit).output = some false))
    (poly_fst r8) hfls hinds
  have r10 := poly_pickWires_orList sits (fun sit => decide ((act sit).output = some true))
    (poly_fst r9) hfls hinds
  have r11 := @ComputableInPolyTime.comp' P _ _ encP _ _
    (fun q : (Gates × List ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)) =>
      emitOutUpdate q.1.1 q.2.1.1 q.2.1.2 q.2.2.1 q.2.2.2 q.1.2)
    _ poly_emitOutUpdate
    (((poly_fst r10).prod hout).prod
      ((hsH.prod (poly_snd r8)).prod ((poly_snd r9).prod (poly_snd r10))))
  exact (poly_fst r11).prod ((poly_cons' (poly_snd r6) (poly_snd r7)).prod (poly_snd r11))

private theorem poly_safeTmInTape {k numStates : ℕ} {State : Type}
    (e : State ≃ Fin numStates) (tm : MultiTapeTM k Bool State) :
    ComputableInPolyTime
      (fun p : (((ℕ × ℕ) × ℕ) × (ℕ × List ℕ)) × (Gates × TapeW) =>
        safeTmInTape e tm p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2.1 p.1.2.2 p.2.2 p.2.1)
      (encPair
        (encPair (encPair (encPair encUnary encNat) encUnary) (encPair encNat (encList encNat)))
        (encPair encGates encTapeW))
      (encPair encGates encTapeW) := by
  set P := (((ℕ × ℕ) × ℕ) × (ℕ × List ℕ)) × (Gates × TapeW)
  set encP : P ↪ List Bool :=
    encPair
      (encPair (encPair (encPair encUnary encNat) encUnary) (encPair encNat (encList encNat)))
      (encPair encGates encTapeW)
  let sits := allActiveSits k numStates
  let act : ActiveSit k numStates → Action k Bool State := fun sit =>
    tm.tr (e.symm sit.1) sit.2.1.toOption (fun r => (sit.2.2 r).toOption)
  have hL : ComputableInPolyTime (fun p : P => p.1.1.1.1) encP encUnary :=
    poly_fst (poly_fst (poly_fst (ComputableInPolyTime.fst _ _)))
  have hfls : ComputableInPolyTime (fun p : P => p.1.1.1.2) encP encNat :=
    poly_snd (poly_fst (poly_fst (ComputableInPolyTime.fst _ _)))
  have ht : ComputableInPolyTime (fun p : P => p.1.1.2) encP encUnary :=
    poly_snd (poly_fst (ComputableInPolyTime.fst _ _))
  have hsH : ComputableInPolyTime (fun p : P => p.1.2.1) encP encNat :=
    poly_fst (poly_snd (ComputableInPolyTime.fst _ _))
  have hinds : ComputableInPolyTime (fun p : P => p.1.2.2) encP (encList encNat) :=
    poly_snd (poly_snd (ComputableInPolyTime.fst _ _))
  have hg : ComputableInPolyTime (fun p : P => p.2.1) encP encGates :=
    poly_fst (ComputableInPolyTime.snd _ _)
  have htw : ComputableInPolyTime (fun p : P => p.2.2) encP encTapeW :=
    poly_snd (ComputableInPolyTime.snd _ _)
  have r12 := poly_pickWires_orList sits
    (fun sit => decide (ObliviousCfg.clampInputMove sit.2.1 (act sit).inputTape = .neg))
    hg hfls hinds
  have r13 := poly_pickWires_orList sits
    (fun sit => decide (ObliviousCfg.clampInputMove sit.2.1 (act sit).inputTape = .zero))
    (poly_fst r12) hsH hinds
  have r14 := poly_pickWires_orList sits
    (fun sit => decide (ObliviousCfg.clampInputMove sit.2.1 (act sit).inputTape = .pos))
    (poly_fst r13) hfls hinds
  have r15 := @ComputableInPolyTime.comp' P _ _ encP _ _
    (fun q : (Gates × ℕ) × ((ℕ × ℕ × ℕ) × (ℕ × ℕ) × TapeW) =>
      emitTapeStep0 q.1.1 q.1.2 q.2.1.1 q.2.1.2.1 q.2.1.2.2 q.2.2.1.1 q.2.2.1.2 q.2.2.2)
    _ poly_emitTapeStep0
    (((poly_fst r14).prod hfls).prod
      (((poly_snd r12).prod ((poly_snd r13).prod (poly_snd r14))).prod
        (((poly_fst (poly_fst htw)).prod (poly_snd (poly_fst htw))).prod htw)))
  have hfin := poly_safeDoubleSchedule.comp' (((hL.prod hfls).prod ht).prod r15)
  exact hfin.of_enc_eq fun _ => rfl

private abbrev IndPar : Type :=
  ((ℕ × List ℕ) × ((ℕ × ℕ) × List (ℕ × ℕ))) × ((ℕ × ℕ) × (List ℕ × List ℕ))

private def encIndPar : IndPar ↪ List Bool :=
  encPair (encPair (encPair encNat (encList encNat))
    (encPair (encPair encNat encNat) (encList (encPair encNat encNat))))
    (encPair (encPair encNat encNat) (encPair (encList encNat) (encList encNat)))

private def indicatorOneStep {k numStates : ℕ} (par : IndPar) (gc : Gates)
    (sit : ActiveSit k numStates) : Gates × ℕ :=
  Gates.gAndList gc par.1.1.1
    (par.1.1.2.getD (sit.1.val + 1) 0 ::
      litWire sit.2.1.1 par.1.2.1.1 par.2.1.1 ::
      litWire sit.2.1.2 par.1.2.1.2 par.2.1.2 ::
      (List.finRange k).flatMap fun r =>
        let tw := par.1.2.2.getD r.val (0, 0)
        [litWire (sit.2.2 r).1 tw.1 (par.2.2.1.getD r.val 0),
         litWire (sit.2.2 r).2 tw.2 (par.2.2.2.getD r.val 0)])

private theorem poly_emitIndicatorOne {k numStates : ℕ} (sit : ActiveSit k numStates) :
    ComputableInPolyTime (fun q : IndPar × Gates => indicatorOneStep q.1 q.2 sit)
      (encPair encIndPar encGates) (encPair encGates encNat) := by
  dsimp only [indicatorOneStep]
  have qPar := ComputableInPolyTime.fst encIndPar encGates
  have qG := ComputableInPolyTime.snd encIndPar encGates
  have q1 := poly_fst qPar
  have q2 := poly_snd qPar
  have qTru := poly_fst (poly_fst q1)
  have qSw11 := poly_snd (poly_fst q1)
  have qIn0 := poly_fst (poly_fst (poly_snd q1))
  have qIn1 := poly_snd (poly_fst (poly_snd q1))
  have qWk := poly_snd (poly_snd q1)
  have qN0 := poly_fst (poly_fst q2)
  have qN1 := poly_snd (poly_fst q2)
  have qW0 := poly_fst (poly_snd q2)
  have qW1 := poly_snd (poly_snd q2)
  have hr1 := poly_gAnd' qG qTru (poly_getD_const qSw11 (sit.1.val + 1) 0)
  have hlit0 : ComputableInPolyTime
      (fun q : IndPar × Gates => litWire sit.2.1.1 q.1.1.2.1.1 q.1.2.1.1)
      (encPair encIndPar encGates) encNat := by
    cases sit.2.1.1 <;> [exact qN0; exact qIn0]
  have hlit1 : ComputableInPolyTime
      (fun q : IndPar × Gates => litWire sit.2.1.2 q.1.1.2.1.2 q.1.2.1.2)
      (encPair encIndPar encGates) encNat := by
    cases sit.2.1.2 <;> [exact qN1; exact qIn1]
  have hr2 := poly_gAnd' (poly_fst hr1) (poly_snd hr1) hlit0
  have hr3 := poly_gAnd' (poly_fst hr2) (poly_snd hr2) hlit1
  have hfold := poly_foldl_const (List.finRange k)
    (fun q : IndPar × Gates =>
      let r1 := Gates.gAnd q.2 q.1.1.1.1 (q.1.1.1.2.getD (sit.1.val + 1) 0)
      let r2 := Gates.gAnd r1.1 r1.2 (litWire sit.2.1.1 q.1.1.2.1.1 q.1.2.1.1)
      Gates.gAnd r2.1 r2.2 (litWire sit.2.1.2 q.1.1.2.1.2 q.1.2.1.2))
    (fun q acc r =>
      let tw := q.1.1.2.2.getD r.val (0, 0)
      let a := Gates.gAnd acc.1 acc.2 (litWire (sit.2.2 r).1 tw.1 (q.1.2.2.1.getD r.val 0))
      Gates.gAnd a.1 a.2 (litWire (sit.2.2 r).2 tw.2 (q.1.2.2.2.getD r.val 0)))
    hr3
    (fun r _ => by
      have hA := ComputableInPolyTime.snd (encPair encIndPar encGates) (encPair encGates encNat)
      have hlitW0 : ComputableInPolyTime
          (fun p : (IndPar × Gates) × (Gates × ℕ) =>
            litWire (sit.2.2 r).1 (p.1.1.1.2.2.getD r.val (0, 0)).1
              (p.1.1.2.2.1.getD r.val 0))
          (encPair (encPair encIndPar encGates) (encPair encGates encNat)) encNat := by
        cases (sit.2.2 r).1
        · exact poly_comp_fst (poly_getD_const qW0 r.val 0)
        · exact poly_comp_fst (poly_fst (poly_getD_const qWk r.val (0, 0)))
      have hlitW1 : ComputableInPolyTime
          (fun p : (IndPar × Gates) × (Gates × ℕ) =>
            litWire (sit.2.2 r).2 (p.1.1.1.2.2.getD r.val (0, 0)).2
              (p.1.1.2.2.2.getD r.val 0))
          (encPair (encPair encIndPar encGates) (encPair encGates encNat)) encNat := by
        cases (sit.2.2 r).2
        · exact poly_comp_fst (poly_getD_const qW1 r.val 0)
        · exact poly_comp_fst (poly_snd (poly_getD_const qWk r.val (0, 0)))
      have ha := poly_gAnd' (poly_fst hA) (poly_snd hA) hlitW0
      exact poly_gAnd' (poly_fst ha) (poly_snd ha) hlitW1)
  exact hfold.of_enc_eq fun q => congrArg (encPair encGates encNat) (by
    simp only [Gates.gAndList_eq]
    rw [List.foldl_cons, List.foldl_cons, List.foldl_cons, List.foldl_flatMap]
    rfl)

private theorem poly_emitIndicators {k numStates : ℕ} (sits : List (ActiveSit k numStates)) :
    ComputableInPolyTime
      (fun q : IndPar × Gates => emitMap q.2 (indicatorOneStep q.1) sits)
      (encPair encIndPar encGates) (encPair encGates (encList encNat)) :=
  poly_emitMap_const (encIn := encIndPar) sits indicatorOneStep fun sit _ =>
    poly_emitIndicatorOne sit

/-- Polynomial-time computability of the guarded TM step `safeTmStep`. -/
theorem poly_safeTmStep {k numStates : ℕ} {State : Type}
    (e : State ≃ Fin numStates) (tm : MultiTapeTM k Bool State) :
    ComputableInPolyTime
      (fun q : (((ℕ × ℕ) × ℕ) × (Gates × StateW)) × ℕ =>
        safeTmStep e tm q.1.1.1.1 q.1.1.1.2 q.1.1.2 q.2 q.1.2.1 q.1.2.2)
      (encPair (encPair (encPair (encPair encUnary encNat) encNat)
        (encPair encGates encStateW)) encUnary)
      (encPair encGates encStateW) := by
  set P := (((ℕ × ℕ) × ℕ) × (Gates × StateW)) × ℕ
  set encP : P ↪ List Bool :=
    encPair (encPair (encPair (encPair encUnary encNat) encNat)
      (encPair encGates encStateW)) encUnary
  have h1 := ComputableInPolyTime.fst
    (encPair (encPair (encPair encUnary encNat) encNat) (encPair encGates encStateW)) encUnary
  have ht := ComputableInPolyTime.snd
    (encPair (encPair (encPair encUnary encNat) encNat) (encPair encGates encStateW)) encUnary
  have hL : ComputableInPolyTime (fun p : P => p.1.1.1.1) encP encUnary :=
    poly_fst (poly_fst (poly_fst h1))
  have hfls : ComputableInPolyTime (fun p : P => p.1.1.1.2) encP encNat :=
    poly_snd (poly_fst (poly_fst h1))
  have htru : ComputableInPolyTime (fun p : P => p.1.1.2) encP encNat :=
    poly_snd (poly_fst h1)
  have hgsw : ComputableInPolyTime (fun p : P => p.1.2) encP (encPair encGates encStateW) :=
    poly_snd h1
  have hsw := poly_snd hgsw
  have hsw11 : ComputableInPolyTime (fun p : P => p.1.2.2.1.1) encP (encList encNat) :=
    poly_fst (poly_fst hsw)
  have hsw12 : ComputableInPolyTime (fun p : P => p.1.2.2.1.2) encP (encList encNat) :=
    poly_snd (poly_fst hsw)
  have hsw21 : ComputableInPolyTime (fun p : P => p.1.2.2.2.1) encP encTapeW :=
    poly_fst (poly_snd hsw)
  have hsw22 : ComputableInPolyTime (fun p : P => p.1.2.2.2.2) encP (encList encTapeW) :=
    poly_snd (poly_snd hsw)
  have hsH := poly_getD_const hsw11 0 0
  have hNegs := (poly_safeTmNegs (k := k)).comp' hgsw
  have hwkHeads : ComputableInPolyTime (fun p : P => p.1.2.2.2.2.map Prod.fst) encP
      (encList (encPair encNat encNat)) :=
    ComputableInPolyTime.mapWithInput (f := fun (_ : P) (tw : TapeW) => tw.1) hsw22
      (poly_fst (ComputableInPolyTime.snd encP encTapeW))
  have hInd_raw := (poly_emitIndicators (allActiveSits k numStates)).comp'
    ((((htru.prod hsw11).prod ((poly_fst hsw21).prod hwkHeads)).prod (poly_snd hNegs)).prod
      (poly_fst hNegs))
  have hInd : ComputableInPolyTime
      (fun p : P =>
        let negs := safeTmNegs (k := k) p.1.2.1 p.1.2.2
        emitIndicators negs.1 p.1.1.2 p.1.2.2 negs.2.1.1 negs.2.1.2 negs.2.2.1 negs.2.2.2
          (allActiveSits k numStates))
      encP (encPair encGates (encList encNat)) :=
    hInd_raw.of_enc_eq fun p => congrArg (encPair encGates (encList encNat)) (by
      dsimp only [emitIndicators_eq, indicatorOneStep]
      congr 1; funext gc sit; congr 1; congr 1; congr 1; congr 1
      refine List.flatMap_congr fun r _ => ?_
      have hget : (p.1.2.2.2.2.map Prod.fst).getD r.val (0, 0) =
          (p.1.2.2.2.2.getD r.val defaultTapeW).1 := by
        by_cases hr : r.val < p.1.2.2.2.2.length
        · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hr]
        · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
            List.getElem?_eq_none (by omega : p.1.2.2.2.2.length ≤ r.val), defaultTapeW_eq]
      rw [hget])
  have hinds := poly_snd hInd
  have hSO := (poly_safeTmStateOut e tm).comp'
    (((hfls.prod hsH).prod (hsw12.prod hinds)).prod (poly_fst hInd))
  have hIn := (poly_safeTmInTape e tm).comp'
    (((((hL.prod hfls).prod ht).prod (hsH.prod hinds)).prod ((poly_fst hSO).prod hsw21)))
  set ParWk := ((((ℕ × ℕ) × ℕ) × (ℕ × List ℕ)) × List TapeW) × Gates
  set encParWk : ParWk ↪ List Bool :=
    encPair (encPair (encPair (encPair (encPair encUnary encNat) encUnary)
      (encPair encNat (encList encNat))) (encList encTapeW)) encGates
  have hresWk_aux : ComputableInPolyTime
      (fun par : ParWk =>
        (List.finRange k).foldl (fun (acc : Gates × List TapeW) (r : Fin k) =>
          let q := safeWorkTapeStep e tm par.1.1.1.1.1 par.1.1.1.1.2 par.1.1.1.2
            par.1.1.2.1 par.1.1.2.2 (par.1.2.getD r.val defaultTapeW) acc.1 r
          (q.1, q.2 :: acc.2)) (par.2, ([] : List TapeW)))
      encParWk (encPair encGates (encList encTapeW)) :=
    poly_foldl_const (List.finRange k)
      (fun par : ParWk => (par.2, ([] : List TapeW)))
      (fun par acc r =>
        let q := safeWorkTapeStep e tm par.1.1.1.1.1 par.1.1.1.1.2 par.1.1.1.2
          par.1.1.2.1 par.1.1.2.2 (par.1.2.getD r.val defaultTapeW) acc.1 r
        (q.1, q.2 :: acc.2))
      ((ComputableInPolyTime.snd _ _).prod (ComputableInPolyTime.const []))
      (fun r _ => by
        have qP := ComputableInPolyTime.fst encParWk (encPair encGates (encList encTapeW))
        have qA := ComputableInPolyTime.snd encParWk (encPair encGates (encList encTapeW))
        have hwk := (poly_safeWorkTapeStep e tm r).comp'
          ((poly_fst (poly_fst qP)).prod
            ((poly_fst qA).prod (poly_getD_const (poly_snd (poly_fst qP)) r.val defaultTapeW)))
        exact ((poly_fst hwk).prod (poly_cons' (poly_snd hwk) (poly_snd qA))).of_enc_eq
          fun _ => rfl)
  have hresWk := hresWk_aux.comp'
    (((((hL.prod hfls).prod ht).prod (hsH.prod hinds)).prod hsw22).prod (poly_fst hIn))
  have hfin := (poly_fst hresWk).prod
    ((poly_snd hSO).prod
      ((poly_snd hIn).prod (ComputableInPolyTime.listReverseWithInput (poly_snd hresWk))))
  exact hfin.of_enc_eq fun _ => rfl

theorem safeRebalanceStep_eq (fls t : ℕ) (acc : Gates × HalfW) (lvl : ℕ) :
    safeRebalanceStep fls t acc lvl =
      if (t + 1) % 2 ^ (lvl + 1) = 0 ∧ lvl + 1 < acc.2.length ∧
          (acc.2.getD (lvl + 1) ([], [])).2.length = 2 * (acc.2.getD lvl ([], [])).2.length then
        emitRebalanceHalfTape acc.1 fls acc.2 lvl
      else acc := rfl

theorem safeTmStep_eq_emitTmStep_of_pass {k L numStates : ℕ} {State : Type}
    (e : State ≃ Fin numStates) (tm : MultiTapeTM k Bool State)
    {g : Gates} {fls tru t : ℕ} {sw : StateW}
    (hin : ∀ ga mN mZ mP w0 w1,
      let t0 := emitTapeStep0 ga fls mN mZ mP w0 w1 sw.2.1
      safeDoubleSchedule L fls t t0.1 t0.2 =
        let rL := emitSchedulePass L fls t t0.1 t0.2.2.1
        let rR := emitSchedulePass L fls t rL.1 t0.2.2.2
        (rR.1, (t0.2.1, (rL.2, rR.2))))
    (hwk : ∀ r : Fin k, ∀ ga mN mZ mP w0 w1,
      let t0 := emitTapeStep0 ga fls mN mZ mP w0 w1 (sw.2.2.getD r.val defaultTapeW)
      safeDoubleSchedule L fls t t0.1 t0.2 =
        let rL := emitSchedulePass L fls t t0.1 t0.2.2.1
        let rR := emitSchedulePass L fls t rL.1 t0.2.2.2
        (rR.1, (t0.2.1, (rL.2, rR.2)))) :
    safeTmStep e tm L fls tru t g sw = emitTmStep e tm L fls tru t g sw := by
  dsimp only [safeTmStep, safeTmNegs, safeTmStateOut, safeTmInTape, emitTmStep_eq]
  rw [hin]
  have hwk_eq : ∀ (inds : List ℕ) (rs : List (Fin k)) (gc : Gates) (acc : List TapeW),
      rs.foldl (fun (q : Gates × List TapeW) r =>
        let p := safeWorkTapeStep e tm L fls t (sw.1.1.getD 0 0) inds
          (sw.2.2.getD r.val defaultTapeW) q.1 r
        (p.1, p.2 :: q.2)) (gc, acc) =
      rs.foldl (fun (q : Gates × List TapeW) r =>
        let p := emitWorkTapeStep e tm L fls t (sw.1.1.getD 0 0) inds
          (sw.2.2.getD r.val defaultTapeW) q.1 r
        (p.1, p.2 :: q.2)) (gc, acc) := by
    intro inds rs; induction rs with
    | nil => intro _ _; rfl
    | cons r tl ih =>
      intro gc acc; simp only [List.foldl_cons]
      have hstep :
          safeWorkTapeStep e tm L fls t (sw.1.1.getD 0 0) inds
            (sw.2.2.getD r.val defaultTapeW) gc r =
            emitWorkTapeStep e tm L fls t (sw.1.1.getD 0 0) inds
              (sw.2.2.getD r.val defaultTapeW) gc r := by
        dsimp only [safeWorkTapeStep, safeWkMoves, safeWkWrite, emitWorkTapeStep_eq]
        exact hwk r _ _ _ _ _ _
      rw [hstep, ih]
  rw [hwk_eq]

end CslibFrontier.Computability.Circuit.Oblivious
