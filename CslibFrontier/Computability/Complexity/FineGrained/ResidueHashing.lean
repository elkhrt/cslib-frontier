/-
Copyright (c) 2026 CslibFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CslibFrontier contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.RadixSort
public import CslibFrontier.Algorithms.ThreeSum.ChanHe.FromNumbers
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Prime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Sqrt
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.BinaryPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.ResourceFacts
import Mathlib.Data.List.Range
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Deterministic Prime-Modulus Residue Hashing on Multi-Tape Turing Machines

This module constructs multi-tape Turing machine algorithms with explicit `ComputableInO` bounds
for deterministic prime-modulus residue hashing.

## Main definitions

* `CslibFrontier.Complexity.fastRange`: binary-doubling construction of `List.range N`.
* `CslibFrontier.Complexity.isPrimeFast`,
  `CslibFrontier.Complexity.primesList`: trial-division primality
  and sorted prime list up to `m`.

## Main results

* `CslibFrontier.Complexity.computableInPolyTime_natLog2`,
  `CslibFrontier.Complexity.computableInPolyTime_natClog2`,
  `CslibFrontier.Complexity.computableInPolyTime_mPar`: polynomial-time parameter certificates.
* `CslibFrontier.Complexity.fastRange_eq_range`, `CslibFrontier.Complexity.computableInO_fastRange`:
  correctness and quasi-linear complexity of `fastRange`.
* `CslibFrontier.Complexity.primesList_toFinset`,
  `CslibFrontier.Complexity.computableInO_primesList`:
  sorted prime enumeration up to `m` in `O((m + 1)^2 * polylog m)` steps.
-/

public section

namespace CslibFrontier.Complexity

open Turing Turing.MultiTapeTM
open Cslib.Algorithms.ThreeSum
open Cslib.Algorithms.ThreeSum.ChanHe

private theorem length_encNat (n : ℕ) : (encNat n).length = n.size := by
  rw [encNat_apply, Nat.size_eq_bits_len]

attribute [local irreducible] encNat encIntBin encUnary

section Parameters

/-- `Nat.log 2 n` equals `n.size - 1` for every natural number `n`. -/
theorem natLog2_eq_size_sub_one (n : ℕ) : Nat.log 2 n = n.size - 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hle : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn.ne'
    have hlt : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by decide) n
    have hsz1 : n.size ≤ Nat.log 2 n + 1 := Nat.size_le.mpr hlt
    have hsz2 : ¬ n.size ≤ Nat.log 2 n := fun h =>
      not_lt_of_ge hle (Nat.size_le.mp h)
    omega

/-- `Nat.clog 2 n` equals `0` for `n ≤ 1` and `(n - 1).size` for `n ≥ 2`. -/
theorem natClog2_eq_size_pred (n : ℕ) :
    Nat.clog 2 n = if n ≤ 1 then 0 else (n - 1).size := by
  split_ifs with hn
  · rcases n with _ | _ | n
    · simp
    · simp
    · omega
  · set k := (n - 1).size
    have hk_pos : 1 ≤ k := Nat.size_pos.mpr (by omega)
    have hlt : n - 1 < 2 ^ k := Nat.lt_size_self (n - 1)
    have hge : ¬ n - 1 < 2 ^ (k - 1) := fun hc => by
      have := Nat.size_le.mpr hc
      omega
    have hle1 : Nat.clog 2 n ≤ k :=
      (Nat.clog_le_iff_le_pow (by decide)).mpr (by omega)
    have hle2 : ¬ Nat.clog 2 n ≤ k - 1 := by
      rw [Nat.clog_le_iff_le_pow (by decide)]
      omega
    omega

/-- Binary logarithm `Nat.log 2` is computable in polynomial time on `encNat`. -/
@[fun_prop]
theorem computableInPolyTime_natLog2 :
    ComputableInPolyTime (Nat.log 2) encNat encNat := by
  have hsize : ComputableInPolyTime Nat.size encNat encNat :=
    ComputableInPolyTime.unary_to_binary.comp ComputableInPolyTime.binary_size
  have h : ComputableInPolyTime (fun n : ℕ => n.size - 1) encNat encNat := by fun_prop
  exact h.of_enc_eq fun n => congrArg encNat (natLog2_eq_size_sub_one n)

/-- Ceiling binary logarithm `Nat.clog 2` is computable in polynomial time on `encNat`. -/
@[fun_prop]
theorem computableInPolyTime_natClog2 :
    ComputableInPolyTime (Nat.clog 2) encNat encNat := by
  have hsize : ComputableInPolyTime Nat.size encNat encNat :=
    ComputableInPolyTime.unary_to_binary.comp ComputableInPolyTime.binary_size
  have h : ComputableInPolyTime (fun n : ℕ => if decide (n ≤ 1) then 0 else (n - 1).size)
      encNat encNat := by fun_prop
  refine h.of_enc_eq fun n => congrArg encNat ?_
  rw [natClog2_eq_size_pred]
  by_cases hn : n ≤ 1 <;> simp [hn]

@[fun_prop]
theorem computableInPolyTime_labelBits :
    ComputableInPolyTime labelBits encNat encNat := by
  unfold labelBits
  fun_prop

@[fun_prop]
theorem computableInPolyTime_height :
    ComputableInPolyTime height encNat encNat := by
  unfold height
  fun_prop

@[fun_prop]
theorem computableInPolyTime_fuel :
    ComputableInPolyTime fuel encNat encNat := by
  unfold fuel
  fun_prop

@[fun_prop]
theorem computableInPolyTime_wPar :
    ComputableInPolyTime (fun p : ℕ × ℕ => wPar p.1 p.2) (encPair encNat encNat) encNat := by
  unfold wPar
  fun_prop

@[fun_prop]
theorem computableInPolyTime_mPar :
    ComputableInPolyTime (fun p : ℕ × ℕ => mPar p.1 p.2) (encPair encNat encNat) encNat := by
  unfold mPar
  fun_prop

end Parameters

section FastRangeAndPrimes

/-- Binary-doubling step `(P, l) ↦ (2 * P, l ++ l.map (P + ·))` building `List.range (2 ^ k)`. -/
def rangeDoubleStep (p : ℕ × List ℕ) : ℕ × List ℕ :=
  (2 * p.1, p.2 ++ p.2.map (fun u => p.1 + u))

theorem iterate_rangeDoubleStep (k : ℕ) :
    rangeDoubleStep^[k] (1, [0]) = (2 ^ k, List.range (2 ^ k)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, rangeDoubleStep, pow_succ', two_mul, ← List.range_add]

/-- Constructs `List.range N` in `N.size` doubling rounds followed by `< N` filtering. -/
def fastRange (N : ℕ) : List ℕ :=
  ((rangeDoubleStep^[N.size] (1, [0])).2).filter (fun u => decide (u < N))

theorem fastRange_eq_range (N : ℕ) : fastRange N = List.range N := by
  rw [fastRange, iterate_rangeDoubleStep]
  have hlt : N < 2 ^ N.size := Nat.lt_size_self N
  have hsplit : 2 ^ N.size = N + (2 ^ N.size - N) := by omega
  rw [hsplit, List.range_add, List.filter_append]
  have hleft : (List.range N).filter (fun u => decide (u < N)) = List.range N :=
    List.filter_eq_self.mpr fun u hu => decide_eq_true (List.mem_range.mp hu)
  have hright : ((List.range (2 ^ N.size - N)).map (fun u => N + u)).filter
      (fun u => decide (u < N)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro u hu
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hu
    simp
  rw [hleft, hright, List.append_nil]

theorem length_encList_range_le (M : ℕ) :
    (encList encNat (List.range M)).length ≤ M * (2 * M.size + 1) := by
  induction M with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, encList_append, List.length_append, encList_cons, encList_nil,
      List.append_nil, length_frame, length_encNat]
    have hsz : m.size ≤ (m + 1).size := Nat.size_le_size (Nat.le_succ m)
    have ih' : m * (2 * m.size + 1) ≤ m * (2 * (m + 1).size + 1) :=
      Nat.mul_le_mul_left m (by omega)
    nlinarith

/-- `fastRange` computes `List.range N` in quasi-linear time `O((N + 1) * (N.size + 1) ^ d)`. -/
theorem computableInO_fastRange :
    ∃ d, ComputableInO fastRange encNat (encList encNat)
      (fun N => (N + 1) * (N.size + 1) ^ d)
      (fun N => (N + 1) * (N.size + 1) ^ d) := by
  have haddPt : ComputableInPolyTime (fun q : ℕ × ℕ => q.1 + q.2)
      (encPair encNat encNat) encNat := by fun_prop
  let lMax : ℕ × List ℕ → ℕ :=
    fun p => max (encNat p.1).length (listMax (fun a => (encNat a).length) p.2)
  obtain ⟨dm, hmap⟩ := computableInO_streamMapWith (lMax := lMax) _ haddPt
    (fun _ => le_max_left _ _)
    (fun p j hj =>
      (le_listMax (f := fun a => (encNat a).length)
        (List.getElem_mem hj)).trans (le_max_right _ _))
  have hshift : ComputableInO (fun p : ℕ × List ℕ => p.2 ++ p.2.map (fun u => p.1 + u))
      (encPair encNat (encList encNat)) (encList encNat)
      (fun p => 2 * (encPair encNat (encList encNat) p).length +
        (p.2.length + 1) * (lMax p + 1) ^ dm)
      (fun p => 2 * (encPair encNat (encList encNat) p).length +
        (p.2.length + 1) * (lMax p + 1) ^ dm) := by
    refine ((ComputableInO.snd encNat (encList encNat)).append hmap
      (fun p => encList_append encNat p.2 (p.2.map fun u => p.1 + u))).mono_le
      (fun _ => by omega) (fun _ => by omega)
  have hmul2Pt : ComputableInPolyTime (fun n : ℕ => 2 * n) encNat encNat := by fun_prop
  obtain ⟨d2, _, hmul2Deg⟩ := hmul2Pt.exists_degree
  have hmul2 : ComputableInO (fun p : ℕ × List ℕ => 2 * p.1)
      (encPair encNat (encList encNat)) encNat
      (fun p => (encPair encNat (encList encNat) p).length + ((encNat p.1).length + 1) ^ d2)
      (fun p => (encPair encNat (encList encNat) p).length + ((encNat p.1).length + 1) ^ d2) :=
    hmul2Deg.inO.comp (ComputableInO.fst encNat (encList encNat))
  let ds := dm + d2 + 1
  have hstep : ComputableInO rangeDoubleStep
      (encPair encNat (encList encNat)) (encPair encNat (encList encNat))
      (fun p => 3 * (encPair encNat (encList encNat) p).length +
        (p.2.length + 1) * (lMax p + 1) ^ ds)
      (fun p => 3 * (encPair encNat (encList encNat) p).length +
        (p.2.length + 1) * (lMax p + 1) ^ ds) := by
    refine (hmul2.prod hshift).mono 2 (fun p => ?_) (fun p => ?_) <;>
    · have hp1 : ((encNat p.1).length + 1) ^ d2 ≤ (lMax p + 1) ^ ds :=
        (Nat.pow_le_pow_left (Nat.succ_le_succ (le_max_left _ _)) d2).trans
          (Nat.pow_le_pow_right (Nat.succ_pos _) (by dsimp [ds]; omega))
      have hp2 : (lMax p + 1) ^ dm ≤ (lMax p + 1) ^ ds :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (by dsimp [ds]; omega)
      have hm1 : (lMax p + 1) ^ ds ≤ (p.2.length + 1) * (lMax p + 1) ^ ds :=
        Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
      have hm2 := Nat.mul_le_mul_left (p.2.length + 1) hp2
      change (encPair encNat (encList encNat) p).length + ((encNat p.1).length + 1) ^ d2 +
          (2 * (encPair encNat (encList encNat) p).length +
            (p.2.length + 1) * (lMax p + 1) ^ dm) ≤
        2 * (3 * (encPair encNat (encList encNat) p).length +
          (p.2.length + 1) * (lMax p + 1) ^ ds + 1)
      omega
  have hsizePt : ComputableInPolyTime Nat.size encNat encNat :=
    ComputableInPolyTime.unary_to_binary.comp ComputableInPolyTime.binary_size
  obtain ⟨dz, _, hsizeDeg⟩ := hsizePt.exists_degree
  have hnIter := hsizeDeg.inO
  have hinit : ComputableInO (fun _ : ℕ => (1, [0])) encNat (encPair encNat (encList encNat))
      (fun N => (encNat N).length) (fun _ => 0) :=
    ComputableInO.constZero (1, [0])
  have hpow2_le (N : ℕ) : 2 ^ N.size ≤ 2 * N + 1 := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · have hsz : 1 ≤ N.size := Nat.size_pos.mpr hN
      have hge : 2 ^ (N.size - 1) ≤ N := by
        by_contra! hc
        have := Nat.size_le.mpr hc
        omega
      have : 2 ^ N.size = 2 * 2 ^ (N.size - 1) := by
        conv_lhs => rw [← Nat.sub_add_cancel hsz, pow_succ']
      omega
  let B : ℕ → ℕ := fun N => (2 * N + 2) * (2 * N.size + 5)
  let R : ℕ → ℕ := fun N => 3 * B N + (2 * N + 2) * (N.size + 2) ^ ds
  have hstate (N k : ℕ) (hk : k ≤ N.size) :
      (encPair encNat (encList encNat) (rangeDoubleStep^[k] (1, [0]))).length ≤ B N := by
    rw [iterate_rangeDoubleStep, length_encPair]
    have hkpow : 2 ^ k ≤ 2 * N + 1 :=
      (Nat.pow_le_pow_right (by decide) hk).trans (hpow2_le N)
    have hsz2k : (2 ^ k).size = k + 1 := by
      have h1 : (2 ^ k).size ≤ k + 1 := Nat.size_le.mpr (by
        rw [pow_succ']
        have := Nat.one_le_two_pow (n := k)
        omega)
      have h2 : ¬ (2 ^ k).size ≤ k := fun hc => not_lt_of_ge le_rfl (Nat.size_le.mp hc)
      omega
    have hlen1 : (encNat (2 ^ k)).length = k + 1 := by
      rw [length_encNat, hsz2k]
    have hlen2 := length_encList_range_le (2 ^ k)
    rw [hsz2k] at hlen2
    have hlen2' : 2 ^ k * (2 * (k + 1) + 1) ≤ (2 * N + 1) * (2 * N.size + 3) :=
      Nat.mul_le_mul hkpow (by omega)
    rw [hlen1]
    dsimp only [B]
    nlinarith
  have hround (N k : ℕ) (hk : k ≤ N.size) :
      3 * (encPair encNat (encList encNat) (rangeDoubleStep^[k] (1, [0]))).length +
        ((rangeDoubleStep^[k] (1, [0])).2.length + 1) *
          (lMax (rangeDoubleStep^[k] (1, [0])) + 1) ^ ds ≤ R N := by
    have hst := hstate N k hk
    rw [iterate_rangeDoubleStep] at hst ⊢
    have hkpow : 2 ^ k ≤ 2 * N + 1 :=
      (Nat.pow_le_pow_right (by decide) hk).trans (hpow2_le N)
    have hsz2k : (encNat (2 ^ k)).length ≤ N.size + 1 := by
      rw [length_encNat]
      exact Nat.size_le.mpr (by
        calc 2 ^ k ≤ 2 ^ N.size := Nat.pow_le_pow_right (by decide) hk
          _ < 2 ^ (N.size + 1) := Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))
    have hlMax : lMax (2 ^ k, List.range (2 ^ k)) ≤ N.size + 1 := by
      refine max_le hsz2k (listMax_le fun u hu => ?_)
      rw [length_encNat]
      have hu' : u < 2 ^ N.size :=
        (List.mem_range.mp hu).trans_le (Nat.pow_le_pow_right (by decide) hk)
      exact (Nat.size_le.mpr hu').trans (Nat.le_succ _)
    rw [List.length_range]
    have hpow : (lMax (2 ^ k, List.range (2 ^ k)) + 1) ^ ds ≤ (N.size + 2) ^ ds :=
      Nat.pow_le_pow_left (Nat.succ_le_succ hlMax) ds
    have hmul : (2 ^ k + 1) * (lMax (2 ^ k, List.range (2 ^ k)) + 1) ^ ds ≤
        (2 * N + 2) * (N.size + 2) ^ ds :=
      Nat.mul_le_mul (by omega) hpow
    exact Nat.add_le_add (Nat.mul_le_mul_left 3 hst) hmul
  have hiter := (ComputableInO.iterate hnIter hinit hstep hround hround hstate).snd'
  have hltPt : ComputableInPolyTime (fun q : ℕ × ℕ => decide (q.2 < q.1))
      (encPair encNat encNat) encBool := by fun_prop
  obtain ⟨df, hfilt⟩ := computableInO_streamFilterWith
    (lMax := fun p : ℕ × List ℕ =>
      max (encNat p.1).length (listMax (fun a => (encNat a).length) p.2))
    _ hltPt (fun _ => le_max_left _ _)
    (fun p j hj =>
      (le_listMax (f := fun a => (encNat a).length)
        (List.getElem_mem hj)).trans (le_max_right _ _))
  have hcomp := hfilt.comp ((ComputableInO.of_eq fun _ => rfl).prod hiter)
  let D := dz + ds + df + 4
  refine ⟨D, (hcomp.of_enc_eq fun _ => rfl).mono (64 * 2 ^ ds * 2 ^ df) (fun N => ?_)
    (fun N => ?_)⟩
  · dsimp only [Function.comp_apply, R, B]
    rw [iterate_rangeDoubleStep, List.length_range, length_encPair]
    set S := N.size + 1
    have hS1 : 1 ≤ S := Nat.succ_pos _
    have hencN : (encNat N).length = N.size := length_encNat N
    have hencSz : (encNat N.size).length ≤ N.size := by
      rw [length_encNat]; exact Nat.size_le_self _
    have hkpow := hpow2_le N
    have hlenR : (encList encNat (List.range (2 ^ N.size))).length ≤
        (2 * N + 1) * (2 * N.size + 3) := by
      have h1 := length_encList_range_le (2 ^ N.size)
      have hsz : (2 ^ N.size).size ≤ N.size + 1 := Nat.size_le.mpr
        (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))
      exact h1.trans (Nat.mul_le_mul hkpow (by omega))
    have hmaxRange : max N.size
        (listMax (fun a => (encNat a).length) (List.range (2 ^ N.size))) ≤ N.size := by
      refine max_le le_rfl (listMax_le fun u hu => ?_)
      rw [length_encNat]
      exact Nat.size_le.mpr (List.mem_range.mp hu)
    have hpow_ds : (N.size + 2) ^ ds ≤ 2 ^ ds * S ^ ds := by
      calc (N.size + 2) ^ ds ≤ (2 * S) ^ ds := Nat.pow_le_pow_left (by dsimp [S]; omega) ds
        _ = 2 ^ ds * S ^ ds := Nat.mul_pow 2 S ds
    rw [hencN]
    set Y := (N + 1) * S ^ D
    have hSD_dz : S ^ dz ≤ Y :=
      (Nat.pow_le_pow_right hS1 (by dsimp [D]; omega)).trans
        (Nat.le_mul_of_pos_left _ (Nat.succ_pos N))
    have hSD_1 : S ≤ Y :=
      (Nat.le_self_pow (by dsimp [D]; omega) S).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos N))
    have hSD_3 : (N + 1) * S ^ 3 ≤ Y :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hS1 (by dsimp [D]; omega))
    have hSD_ds : S * ((N + 1) * S ^ ds) ≤ Y := by
      calc S * ((N + 1) * S ^ ds) = (N + 1) * (S ^ (ds + 1)) := by rw [pow_succ']; ring
        _ ≤ Y := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hS1 (by dsimp [D]; omega))
    have hSD_df : (N + 1) * S ^ df ≤ Y :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hS1 (by dsimp [D]; omega))
    have hB_le : (2 * N + 2) * (2 * N.size + 5) ≤ 10 * ((N + 1) * S) := by
      calc (2 * N + 2) * (2 * N.size + 5) ≤ (2 * (N + 1)) * (5 * S) :=
            Nat.mul_le_mul (by omega) (by dsimp [S]; omega)
        _ = 10 * ((N + 1) * S) := by ring
    have hS_B : S * ((2 * N + 2) * (2 * N.size + 5)) ≤ 10 * Y := by
      calc S * ((2 * N + 2) * (2 * N.size + 5)) ≤ S * (10 * ((N + 1) * S)) :=
            Nat.mul_le_mul_left S hB_le
        _ = 10 * ((N + 1) * S ^ 2) := by ring
        _ ≤ 10 * ((N + 1) * S ^ 3) :=
            Nat.mul_le_mul_left 10 (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hS1 (by omega)))
        _ ≤ 10 * Y := Nat.mul_le_mul_left 10 hSD_3
    have hS_sq : S * ((encNat N.size).length + 1) ^ 2 ≤ Y := by
      have h1 : ((encNat N.size).length + 1) ^ 2 ≤ S ^ 2 :=
        Nat.pow_le_pow_left (Nat.succ_le_succ hencSz) 2
      calc S * ((encNat N.size).length + 1) ^ 2 ≤ S * S ^ 2 := Nat.mul_le_mul_left S h1
        _ = S ^ 3 := by ring
        _ ≤ (N + 1) * S ^ 3 := Nat.le_mul_of_pos_left _ (Nat.succ_pos N)
        _ ≤ Y := hSD_3
    have hS_ds_term : S * ((2 * N + 2) * (N.size + 2) ^ ds) ≤ 2 * 2 ^ ds * Y := by
      calc S * ((2 * N + 2) * (N.size + 2) ^ ds)
          ≤ S * ((2 * (N + 1)) * (2 ^ ds * S ^ ds)) :=
            Nat.mul_le_mul_left S (Nat.mul_le_mul (by omega) hpow_ds)
        _ = 2 * 2 ^ ds * (S * ((N + 1) * S ^ ds)) := by ring
        _ ≤ 2 * 2 ^ ds * Y := Nat.mul_le_mul_left _ hSD_ds
    have hfilt_term : 2 * N.size + 1 + (encList encNat (List.range (2 ^ N.size))).length +
        (2 ^ N.size + 1) * (max N.size
          (listMax (fun a => (encNat a).length) (List.range (2 ^ N.size))) + 1) ^ df ≤ 12 * Y := by
      have h1 : (encList encNat (List.range (2 ^ N.size))).length ≤ 6 * Y := by
        have : (2 * N + 1) * (2 * N.size + 3) ≤ 6 * ((N + 1) * S) := by
          calc (2 * N + 1) * (2 * N.size + 3) ≤ (2 * (N + 1)) * (3 * S) :=
                Nat.mul_le_mul (by omega) (by dsimp [S]; omega)
            _ = 6 * ((N + 1) * S) := by ring
        exact hlenR.trans (this.trans (Nat.mul_le_mul_left 6
          (Nat.mul_le_mul_left _ (Nat.le_self_pow (by omega) S) |>.trans hSD_3)))
      have h2 : (2 ^ N.size + 1) * (max N.size
          (listMax (fun a => (encNat a).length) (List.range (2 ^ N.size))) + 1) ^ df ≤ 3 * Y := by
        calc (2 ^ N.size + 1) * (max N.size
              (listMax (fun a => (encNat a).length) (List.range (2 ^ N.size))) + 1) ^ df
            ≤ (3 * (N + 1)) * S ^ df :=
              Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (Nat.succ_le_succ hmaxRange) df)
          _ = 3 * ((N + 1) * S ^ df) := by ring
          _ ≤ 3 * Y := Nat.mul_le_mul_left 3 hSD_df
      have h3 : 2 * N.size + 1 ≤ 3 * Y := by
        have : 2 * N.size + 1 ≤ 3 * S := by dsimp [S]; omega
        exact this.trans (Nat.mul_le_mul_left 3 hSD_1)
      exact (Nat.add_le_add (Nat.add_le_add h3 h1) h2).trans_eq (by ring)
    have h2ds1 : 1 ≤ 2 ^ ds := Nat.one_le_two_pow
    have h2df1 : 1 ≤ 2 ^ df := Nat.one_le_two_pow
    have hcoeff : 56 + 2 * 2 ^ ds ≤ 64 * 2 ^ ds * 2 ^ df := by nlinarith
    have hNsz : N.size ≤ Y := (Nat.le_succ _).trans hSD_1
    have hmid : S * (3 * ((2 * N + 2) * (2 * N.size + 5)) +
        (2 * N + 2) * (N.size + 2) ^ ds + (2 * N + 2) * (2 * N.size + 5) +
        ((encNat N.size).length + 1) ^ 2) =
        4 * (S * ((2 * N + 2) * (2 * N.size + 5))) +
          S * ((2 * N + 2) * (N.size + 2) ^ ds) +
          S * ((encNat N.size).length + 1) ^ 2 := by ring
    have hsum : N.size + (S ^ dz + N.size + (4 * (S * ((2 * N + 2) * (2 * N.size + 5))) +
        S * ((2 * N + 2) * (N.size + 2) ^ ds) + S * ((encNat N.size).length + 1) ^ 2)) +
        (2 * N.size + 1 + (encList encNat (List.range (2 ^ N.size))).length +
          (2 ^ N.size + 1) * (max N.size
            (listMax (fun a => (encNat a).length) (List.range (2 ^ N.size))) + 1) ^ df) ≤
        (56 + 2 * 2 ^ ds) * Y := by
      nlinarith [hS_B, hS_sq, hS_ds_term, hfilt_term, hSD_dz, hNsz]
    rw [hmid]
    exact hsum.trans ((Nat.mul_le_mul_right Y hcoeff).trans
      (Nat.mul_le_mul_left _ (Nat.le_succ Y)))
  · dsimp only [Function.comp_apply, R, B]
    rw [iterate_rangeDoubleStep, List.length_range, length_encPair]
    set S := N.size + 1
    have hS1 : 1 ≤ S := Nat.succ_pos _
    have hencN : (encNat N).length = N.size := length_encNat N
    have hencSz : (encNat N.size).length ≤ N.size := by
      rw [length_encNat]; exact Nat.size_le_self _
    have hkpow := hpow2_le N
    have hlenR : (encList encNat (List.range (2 ^ N.size))).length ≤
        (2 * N + 1) * (2 * N.size + 3) := by
      have h1 := length_encList_range_le (2 ^ N.size)
      have hsz : (2 ^ N.size).size ≤ N.size + 1 := Nat.size_le.mpr
        (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))
      exact h1.trans (Nat.mul_le_mul hkpow (by omega))
    have hmaxRange : max N.size
        (listMax (fun a => (encNat a).length) (List.range (2 ^ N.size))) ≤ N.size := by
      refine max_le le_rfl (listMax_le fun u hu => ?_)
      rw [length_encNat]
      exact Nat.size_le.mpr (List.mem_range.mp hu)
    have hpow_ds : (N.size + 2) ^ ds ≤ 2 ^ ds * S ^ ds := by
      calc (N.size + 2) ^ ds ≤ (2 * S) ^ ds := Nat.pow_le_pow_left (by dsimp [S]; omega) ds
        _ = 2 ^ ds * S ^ ds := Nat.mul_pow 2 S ds
    rw [hencN]
    set Y := (N + 1) * S ^ D
    have hSD_dz : S ^ dz ≤ Y :=
      (Nat.pow_le_pow_right hS1 (by dsimp [D]; omega)).trans
        (Nat.le_mul_of_pos_left _ (Nat.succ_pos N))
    have hSD_1 : S ≤ Y :=
      (Nat.le_self_pow (by dsimp [D]; omega) S).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos N))
    have hSD_ds : (N + 1) * S ^ ds ≤ Y :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hS1 (by dsimp [D]; omega))
    have hSD_df : (N + 1) * S ^ df ≤ Y :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hS1 (by dsimp [D]; omega))
    have hB_le : (2 * N + 2) * (2 * N.size + 5) ≤ 10 * Y := by
      have : (2 * N + 2) * (2 * N.size + 5) ≤ 10 * ((N + 1) * S) := by
        calc (2 * N + 2) * (2 * N.size + 5) ≤ (2 * (N + 1)) * (5 * S) :=
              Nat.mul_le_mul (by omega) (by dsimp [S]; omega)
          _ = 10 * ((N + 1) * S) := by ring
      exact this.trans (Nat.mul_le_mul_left 10
        (Nat.mul_le_mul_left _ (Nat.le_self_pow (by dsimp [D]; omega) S)))
    have hds_le : (2 * N + 2) * (N.size + 2) ^ ds ≤ 2 * 2 ^ ds * Y := by
      calc (2 * N + 2) * (N.size + 2) ^ ds ≤ (2 * (N + 1)) * (2 ^ ds * S ^ ds) :=
            Nat.mul_le_mul (by omega) hpow_ds
        _ = 2 * 2 ^ ds * ((N + 1) * S ^ ds) := by ring
        _ ≤ 2 * 2 ^ ds * Y := Nat.mul_le_mul_left _ hSD_ds
    have hfilt_le : 2 * N.size + 1 + (encList encNat (List.range (2 ^ N.size))).length +
        (2 ^ N.size + 1) * (max N.size
          (listMax (fun a => (encNat a).length) (List.range (2 ^ N.size))) + 1) ^ df ≤ 12 * Y := by
      have h1 : (encList encNat (List.range (2 ^ N.size))).length ≤ 6 * Y := by
        have : (2 * N + 1) * (2 * N.size + 3) ≤ 6 * ((N + 1) * S) := by
          calc (2 * N + 1) * (2 * N.size + 3) ≤ (2 * (N + 1)) * (3 * S) :=
                Nat.mul_le_mul (by omega) (by dsimp [S]; omega)
            _ = 6 * ((N + 1) * S) := by ring
        exact hlenR.trans (this.trans (Nat.mul_le_mul_left 6
          (Nat.mul_le_mul_left _ (Nat.le_self_pow (by dsimp [D]; omega) S))))
      have h2 : (2 ^ N.size + 1) * (max N.size
          (listMax (fun a => (encNat a).length) (List.range (2 ^ N.size))) + 1) ^ df ≤ 3 * Y := by
        calc (2 ^ N.size + 1) * (max N.size
              (listMax (fun a => (encNat a).length) (List.range (2 ^ N.size))) + 1) ^ df
            ≤ (3 * (N + 1)) * S ^ df :=
              Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (Nat.succ_le_succ hmaxRange) df)
          _ = 3 * ((N + 1) * S ^ df) := by ring
          _ ≤ 3 * Y := Nat.mul_le_mul_left 3 hSD_df
      have h3 : 2 * N.size + 1 ≤ 3 * Y := by
        have : 2 * N.size + 1 ≤ 3 * S := by dsimp [S]; omega
        exact this.trans (Nat.mul_le_mul_left 3 hSD_1)
      exact (Nat.add_le_add (Nat.add_le_add h3 h1) h2).trans_eq (by ring)
    have h2ds1 : 1 ≤ 2 ^ ds := Nat.one_le_two_pow
    have h2df1 : 1 ≤ 2 ^ df := Nat.one_le_two_pow
    have hcoeff : 56 + 2 * 2 ^ ds ≤ 64 * 2 ^ ds * 2 ^ df := by nlinarith
    have hNsz : N.size ≤ Y := (Nat.le_succ _).trans hSD_1
    have hencSz' : (encNat N.size).length ≤ Y := hencSz.trans hNsz
    have hsum : N.size + (S ^ dz + 0 + (3 * ((2 * N + 2) * (2 * N.size + 5)) +
        (2 * N + 2) * (N.size + 2) ^ ds) + (2 * N + 2) * (2 * N.size + 5) +
        (encNat N.size).length) +
        (2 * N.size + 1 + (encList encNat (List.range (2 ^ N.size))).length +
          (2 ^ N.size + 1) * (max N.size
            (listMax (fun a => (encNat a).length) (List.range (2 ^ N.size))) + 1) ^ df) ≤
        (56 + 2 * 2 ^ ds) * Y := by
      nlinarith [hSD_dz, hB_le, hds_le, hfilt_le, hNsz, hencSz']
    exact hsum.trans ((Nat.mul_le_mul_right Y hcoeff).trans
      (Nat.mul_le_mul_left _ (Nat.le_succ Y)))

/-- Streaming trial-division primality test over `fastRange p`. -/
def isPrimeFast (p : ℕ) : Bool :=
  ((fastRange p).foldl
    (fun s d => (s.1, s.2 && (decide (d < 2) || decide (s.1 % d ≠ 0))))
    (p, decide (2 ≤ p))).2

private theorem foldl_prime_step (p : ℕ) (l : List ℕ) (ok : Bool) :
    l.foldl (fun s d => (s.1, s.2 && (decide (d < 2) || decide (s.1 % d ≠ 0)))) (p, ok) =
      (p, ok && l.all fun d => decide (d < 2) || decide (p % d ≠ 0)) := by
  induction l generalizing ok with
  | nil => simp
  | cons d ds ih =>
    rw [List.foldl_cons, ih, List.all_cons, Bool.and_assoc]

theorem isPrimeFast_eq_decide_prime (p : ℕ) : isPrimeFast p = decide p.Prime := by
  rw [isPrimeFast, foldl_prime_step, fastRange_eq_range, ComputableInPolyTime.decide_prime_eq]

theorem computableInO_isPrimeFast :
    ∃ d, ComputableInO isPrimeFast encNat encBool
      (fun p => (p + 1) * (p.size + 1) ^ d)
      (fun p => (p + 1) * (p.size + 1) ^ d) := by
  obtain ⟨dr, hrange⟩ := computableInO_fastRange
  let encSt := encPair encNat encBool
  have hstepPt : ComputableInPolyTime
      (fun q : (ℕ × Bool) × ℕ =>
        (q.1.1, q.1.2 && (decide (q.2 < 2) || decide (q.1.1 % q.2 ≠ 0))))
      (encPair encSt encNat) encSt := by
    have hmod := ComputableInPolyTime.binary_mod' (α := (ℕ × Bool) × ℕ)
      (input := encPair encSt encNat) (left := fun q => q.1.1) (right := fun q => q.2)
      (by fun_prop) (by fun_prop)
    have hneq : ComputableInPolyTime (fun q : (ℕ × Bool) × ℕ => !(decide (q.1.1 % q.2 = 0)))
        (encPair encSt encNat) encBool := by fun_prop
    have h : ComputableInPolyTime
        (fun q : (ℕ × Bool) × ℕ =>
          (q.1.1, q.1.2 && (decide (q.2 < 2) || !(decide (q.1.1 % q.2 = 0)))))
        (encPair encSt encNat) encSt := by fun_prop
    exact h.of_enc_eq fun q => by simp
  obtain ⟨df, hfold⟩ := computableInO_streamFold
    (lMax := fun x : (ℕ × Bool) × List ℕ =>
      (encSt x.1).length + listMax (fun d => (encNat d).length) x.2)
    Prod.fst Prod.snd (fun _ => rfl) hstepPt
    (fun x j _ => by
      simp only [streamState]
      rw [foldl_prime_step]
      have h1 : (encSt (x.1.1, x.1.2 && (x.2.take j).all
          fun d => decide (d < 2) || decide (x.1.1 % d ≠ 0))).length = (encSt x.1).length := by
        simp only [encSt, length_encPair, encBool_apply, List.length_singleton]
      rw [h1]
      omega)
    (fun x j hj =>
      (le_listMax (f := fun d => (encNat d).length) (List.getElem_mem hj)).trans
        (Nat.le_add_left _ _))
  have hge2Pt : ComputableInPolyTime (fun p : ℕ => decide (2 ≤ p)) encNat encBool := by fun_prop
  obtain ⟨dg, _, hge2Deg⟩ := hge2Pt.exists_degree
  have hinitPair : ComputableInO (fun p : ℕ => ((p, decide (2 ≤ p)), fastRange p))
      encNat (encPair encSt (encList encNat))
      (fun p => (encNat p).length + ((encNat p).length + 1) ^ dg + (p + 1) * (p.size + 1) ^ dr)
      (fun p => (encNat p).length + ((encNat p).length + 1) ^ dg + (p + 1) * (p.size + 1) ^ dr) :=
    ((ComputableInO.of_eq fun _ => rfl).prod hge2Deg.inO).prod hrange
  have hcomp := (hfold.comp hinitPair).snd'
  let D := dr + df + dg + 3
  refine ⟨D, (hcomp.of_enc_eq fun _ => rfl).mono (32 * 6 ^ df) (fun p => ?_) (fun p => ?_)⟩
  · dsimp only [Function.comp_apply]
    rw [fastRange_eq_range, List.length_range, length_encPair]
    set S := p.size + 1
    have hS1 : 1 ≤ S := Nat.succ_pos _
    have hencP : (encNat p).length = p.size := length_encNat p
    have hstLen : (encSt (p, decide (2 ≤ p))).length = 2 * p.size + 2 := by
      simp only [encSt, length_encPair, hencP, encBool_apply, List.length_singleton]
    have hlMaxR : listMax (fun d => (encNat d).length) (List.range p) ≤ p.size := by
      refine listMax_le fun d hd => ?_
      rw [length_encNat]
      exact Nat.size_le_size (Nat.le_of_lt (List.mem_range.mp hd))
    have hlenR := length_encList_range_le p
    rw [hencP, hstLen]
    have hpow_df : (2 * p.size + 2 + listMax (fun d => (encNat d).length) (List.range p) + 1) ^ df ≤
        6 ^ df * S ^ df := by
      calc (2 * p.size + 2 + listMax (fun d => (encNat d).length) (List.range p) + 1) ^ df
          ≤ (6 * S) ^ df := Nat.pow_le_pow_left (by dsimp only [S]; omega) df
        _ = 6 ^ df * S ^ df := Nat.mul_pow 6 S df
    set Y := (p + 1) * S ^ D
    have h1 : S ≤ Y :=
      (Nat.le_self_pow (by dsimp [D]; omega) S).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos p))
    have h2 : S ^ dg ≤ Y :=
      (Nat.pow_le_pow_right hS1 (by dsimp [D]; omega)).trans
        (Nat.le_mul_of_pos_left _ (Nat.succ_pos p))
    have h3 : (p + 1) * S ^ dr ≤ Y :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hS1 (by dsimp [D]; omega))
    have h4 : (p + 1) * S ^ df ≤ Y :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hS1 (by dsimp [D]; omega))
    have h5 : (encList encNat (List.range p)).length ≤ 3 * Y := by
      have : p * (2 * p.size + 1) ≤ 3 * ((p + 1) * S) := by
        calc p * (2 * p.size + 1) ≤ (p + 1) * (3 * S) :=
              Nat.mul_le_mul (Nat.le_succ p) (by dsimp [S]; omega)
          _ = 3 * ((p + 1) * S) := by ring
      exact hlenR.trans (this.trans (Nat.mul_le_mul_left 3
        (Nat.mul_le_mul_left _ (Nat.le_self_pow (by dsimp [D]; omega) S))))
    have h6 : (p + 1) *
        (2 * p.size + 2 + listMax (fun d => (encNat d).length) (List.range p) + 1) ^ df ≤
        6 ^ df * Y := by
      calc (p + 1) *
            (2 * p.size + 2 + listMax (fun d => (encNat d).length) (List.range p) + 1) ^ df
          ≤ (p + 1) * (6 ^ df * S ^ df) := Nat.mul_le_mul_left _ hpow_df
        _ = 6 ^ df * ((p + 1) * S ^ df) := by ring
        _ ≤ 6 ^ df * Y := Nat.mul_le_mul_left _ h4
    have hpsz : p.size ≤ Y := (Nat.le_succ _).trans h1
    have h6_1 : 1 ≤ 6 ^ df := Nat.one_le_pow df 6 (by decide)
    have hsum : p.size + S ^ dg + (p + 1) * S ^ dr +
        (2 * (2 * p.size + 2) + 1 + (encList encNat (List.range p)).length +
          (p + 1) * (2 * p.size + 2 +
            listMax (fun d => (encNat d).length) (List.range p) + 1) ^ df) ≤
        (16 + 6 ^ df) * (Y + 1) := by
      nlinarith
    exact hsum.trans (Nat.mul_le_mul_right _ (by nlinarith))
  · dsimp only [Function.comp_apply]
    rw [fastRange_eq_range]
    set S := p.size + 1
    have hS1 : 1 ≤ S := Nat.succ_pos _
    have hencP : (encNat p).length = p.size := length_encNat p
    have hstLen : (encSt (p, decide (2 ≤ p))).length = 2 * p.size + 2 := by
      simp only [encSt, length_encPair, hencP, encBool_apply, List.length_singleton]
    have hlMaxR : listMax (fun d => (encNat d).length) (List.range p) ≤ p.size := by
      refine listMax_le fun d hd => ?_
      rw [length_encNat]
      exact Nat.size_le_size (Nat.le_of_lt (List.mem_range.mp hd))
    rw [hencP, hstLen]
    have hpow_df : (2 * p.size + 2 + listMax (fun d => (encNat d).length) (List.range p) + 1) ^ df ≤
        6 ^ df * S ^ df := by
      calc (2 * p.size + 2 + listMax (fun d => (encNat d).length) (List.range p) + 1) ^ df
          ≤ (6 * S) ^ df := Nat.pow_le_pow_left (by dsimp only [S]; omega) df
        _ = 6 ^ df * S ^ df := Nat.mul_pow 6 S df
    set Y := (p + 1) * S ^ D
    have h1 : S ≤ Y :=
      (Nat.le_self_pow (by dsimp [D]; omega) S).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos p))
    have h2 : S ^ dg ≤ Y :=
      (Nat.pow_le_pow_right hS1 (by dsimp [D]; omega)).trans
        (Nat.le_mul_of_pos_left _ (Nat.succ_pos p))
    have h3 : (p + 1) * S ^ dr ≤ Y :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hS1 (by dsimp [D]; omega))
    have h4 : S ^ df ≤ Y :=
      (Nat.pow_le_pow_right hS1 (by dsimp [D]; omega)).trans
        (Nat.le_mul_of_pos_left _ (Nat.succ_pos p))
    have hpsz : p.size ≤ Y := (Nat.le_succ _).trans h1
    have h6_1 : 1 ≤ 6 ^ df := Nat.one_le_pow df 6 (by decide)
    have h6 : (2 * p.size + 2 + listMax (fun d => (encNat d).length) (List.range p) + 1) ^ df ≤
        6 ^ df * Y := hpow_df.trans (Nat.mul_le_mul_left _ h4)
    have hsum : p.size + S ^ dg + (p + 1) * S ^ dr +
        (2 * p.size + 2 + listMax (fun d => (encNat d).length) (List.range p) + 1) ^ df ≤
        (16 + 6 ^ df) * (Y + 1) := by
      nlinarith
    exact hsum.trans (Nat.mul_le_mul_right _ (by nlinarith))

/-- One round `(k, acc) ↦ (k + 1, if isPrimeFast k then acc ++ [k] else acc)`. -/
def primeEnumStep (p : ℕ × List ℕ) : ℕ × List ℕ :=
  (p.1 + 1, if isPrimeFast p.1 then p.2 ++ [p.1] else p.2)

theorem iterate_primeEnumStep (k : ℕ) :
    primeEnumStep^[k] (0, []) = (k, (List.range k).filter fun p => decide p.Prime) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, primeEnumStep, List.range_succ, List.filter_append,
      isPrimeFast_eq_decide_prime]
    by_cases hp : k.Prime <;> simp [hp]

/-- Strictly increasing list of primes at most `m`. -/
def primesList (m : ℕ) : List ℕ :=
  (primeEnumStep^[m + 1] (0, [])).2

theorem primesList_eq_filter_range (m : ℕ) :
    primesList m = (List.range (m + 1)).filter fun p => decide p.Prime := by
  rw [primesList, iterate_primeEnumStep]

theorem pairwise_primesList (m : ℕ) : List.Pairwise (· < ·) (primesList m) := by
  rw [primesList_eq_filter_range]
  exact List.pairwise_lt_range.filter _

theorem primesList_nodup (m : ℕ) : (primesList m).Nodup :=
  (pairwise_primesList m).imp ne_of_lt

@[simp]
theorem primesList_toFinset (m : ℕ) : (primesList m).toFinset = Nat.primesLE m := by
  rw [Nat.primesLE_eq_filter_Icc_zero]
  ext p
  simp only [primesList_eq_filter_range, List.mem_toFinset, List.mem_filter, List.mem_range,
    decide_eq_true_eq, Finset.mem_filter, Finset.mem_Icc, Nat.zero_le, true_and]
  exact ⟨fun ⟨h1, h2⟩ => ⟨by omega, h2⟩, fun ⟨h1, h2⟩ => ⟨by omega, h2⟩⟩

theorem length_primesList_le (m : ℕ) : (primesList m).length ≤ m + 1 := by
  rw [primesList_eq_filter_range]
  exact (List.length_filter_le _ _).trans_eq List.length_range

/-- Enumerating `primesList m` runs in time `O((m + 1) ^ 2 * ((m + 1).size + 1) ^ d)` and space
`O((m + 1) * ((m + 1).size + 1) ^ d)`. -/
theorem computableInO_primesList :
    ∃ d, ComputableInO primesList encNat (encList encNat)
      (fun m => (m + 1) ^ 2 * ((m + 1).size + 1) ^ d)
      (fun m => (m + 1) * ((m + 1).size + 1) ^ d) := by
  obtain ⟨dp, hprime⟩ := computableInO_isPrimeFast
  have hinc : ComputableInO (fun p : ℕ × List ℕ => p.1 + 1)
      (encPair encNat (encList encNat)) encNat
      (fun p => (encPair encNat (encList encNat) p).length)
      (fun p => (encPair encNat (encList encNat) p).length) :=
    (ComputableInO.of_linear .natSucc).comp_linear (ComputableInO.fst encNat (encList encNat))
  have hsnoc : ComputableInO (fun p : ℕ × List ℕ => p.2 ++ [p.1])
      (encPair encNat (encList encNat)) (encList encNat)
      (fun p => (encPair encNat (encList encNat) p).length)
      (fun p => (encPair encNat (encList encNat) p).length) :=
    ((ComputableInDegree.snoc encNat).inO_one.comp_linear
      ((ComputableInO.snd encNat (encList encNat)).prod
        (ComputableInO.fst encNat (encList encNat)))).mono 2 (fun _ => by omega) (fun _ => by omega)
  have hcond : ComputableInO (fun p : ℕ × List ℕ => isPrimeFast p.1)
      (encPair encNat (encList encNat)) encBool
      (fun p => (encPair encNat (encList encNat) p).length + (p.1 + 1) * (p.1.size + 1) ^ dp)
      (fun p => (encPair encNat (encList encNat) p).length + (p.1 + 1) * (p.1.size + 1) ^ dp) :=
    hprime.comp (ComputableInO.fst encNat (encList encNat))
  have hstep : ComputableInO primeEnumStep
      (encPair encNat (encList encNat)) (encPair encNat (encList encNat))
      (fun p => 3 * (encPair encNat (encList encNat) p).length + (p.1 + 1) * (p.1.size + 1) ^ dp)
      (fun p => 3 * (encPair encNat (encList encNat) p).length + (p.1 + 1) * (p.1.size +
        1) ^ dp) := by
    refine (hinc.prod (hcond.ite hsnoc (ComputableInO.snd encNat (encList encNat)))).mono 2
      (fun _ => ?_) (fun _ => ?_) <;>
    · split_ifs <;> omega
  have hnIter : ComputableInO (fun m : ℕ => m + 1) encNat encNat
      (fun m => (encNat m).length) (fun m => (encNat m).length) :=
    ComputableInO.of_linear .natSucc
  have hinit : ComputableInO (fun _ : ℕ => (0, ([] : List ℕ)))
      encNat (encPair encNat (encList encNat))
      (fun m => (encNat m).length) (fun _ => 0) :=
    ComputableInO.constZero (0, [])
  let B : ℕ → ℕ := fun m => (m + 2) * (2 * (m + 1).size + 3)
  let R : ℕ → ℕ := fun m => 3 * B m + (m + 2) * ((m + 1).size + 1) ^ dp
  have hstate (m k : ℕ) (hk : k ≤ m + 1) :
      (encPair encNat (encList encNat) (primeEnumStep^[k] (0, []))).length ≤ B m := by
    rw [iterate_primeEnumStep, length_encPair]
    have hksz : (encNat k).length ≤ (m + 1).size := by
      rw [length_encNat]
      exact Nat.size_le_size hk
    have htk : List.range k = (List.range (m + 1)).take k := by
      rw [List.take_range, Nat.min_eq_left hk]
    have hfiltLen : (encList encNat ((List.range k).filter fun p => decide p.Prime)).length ≤
        (encList encNat (List.range (m + 1))).length := by
      refine (ComputableInDegree.length_encList_filter_le encNat _ _).trans ?_
      rw [htk]
      exact length_encList_take_le encNat (List.range (m + 1)) k
    have hlenR := length_encList_range_le (m + 1)
    dsimp only [B]
    nlinarith
  have hround (m k : ℕ) (hk : k ≤ m + 1) :
      3 * (encPair encNat (encList encNat) (primeEnumStep^[k] (0, []))).length +
        ((primeEnumStep^[k] (0, [])).1 + 1) * ((primeEnumStep^[k] (0, [])).1.size + 1) ^ dp ≤
        R m := by
    have hst := hstate m k hk
    rw [iterate_primeEnumStep] at hst ⊢
    have hksz : k.size ≤ (m + 1).size := Nat.size_le_size hk
    have hpow : (k.size + 1) ^ dp ≤ ((m + 1).size + 1) ^ dp :=
      Nat.pow_le_pow_left (Nat.succ_le_succ hksz) dp
    exact Nat.add_le_add (Nat.mul_le_mul_left 3 hst) (Nat.mul_le_mul (by omega) hpow)
  have hiter := (ComputableInO.iterate hnIter hinit hstep hround hround hstate).snd'
  let D := dp + 2
  refine ⟨D, hiter.mono 64 (fun m => ?_) (fun m => ?_)⟩
  · dsimp only [R, B]
    set S := (m + 1).size + 1
    have hS1 : 1 ≤ S := Nat.succ_pos _
    have hencM : (encNat m).length ≤ (m + 1).size := by
      rw [length_encNat]
      exact Nat.size_le_size (Nat.le_succ m)
    have hencM1 : (encNat (m + 1)).length = (m + 1).size := length_encNat (m + 1)
    rw [hencM1]
    set Y := (m + 1) ^ 2 * S ^ D
    have hSD_1 : S ^ 2 ≤ S ^ D := Nat.pow_le_pow_right hS1 (by dsimp [D]; omega)
    have hSD_dp : S ^ dp ≤ S ^ D := Nat.pow_le_pow_right hS1 (by dsimp [D]; omega)
    have hB_le : (m + 2) * (2 * (m + 1).size + 3) ≤ 6 * ((m + 1) * S) := by
      calc (m + 2) * (2 * (m + 1).size + 3) ≤ (2 * (m + 1)) * (3 * S) :=
            Nat.mul_le_mul (by omega) (by dsimp [S]; omega)
        _ = 6 * ((m + 1) * S) := by ring
    have hmul1 : (m + 2) * ((m + 2) * (2 * (m + 1).size + 3)) ≤ 12 * Y := by
      calc (m + 2) * ((m + 2) * (2 * (m + 1).size + 3))
          ≤ (2 * (m + 1)) * (6 * ((m + 1) * S)) := Nat.mul_le_mul (by omega) hB_le
        _ = 12 * ((m + 1) ^ 2 * S) := by ring
        _ ≤ 12 * Y := Nat.mul_le_mul_left 12 (Nat.mul_le_mul_left _
            (Nat.le_self_pow (by dsimp [D]; omega) S))
    have hmul2 : (m + 2) * ((m + 2) * S ^ dp) ≤ 4 * Y := by
      calc (m + 2) * ((m + 2) * S ^ dp) ≤ (2 * (m + 1)) * ((2 * (m + 1)) * S ^ D) :=
            Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) hSD_dp)
        _ = 4 * Y := by ring
    have hmul3 : (m + 2) * S ^ 2 ≤ 2 * Y := by
      calc (m + 2) * S ^ 2 ≤ (2 * (m + 1)) * S ^ D := Nat.mul_le_mul (by omega) hSD_1
        _ = 2 * ((m + 1) * S ^ D) := by ring
        _ ≤ 2 * Y := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _
            (by rw [sq]; exact Nat.le_mul_of_pos_left _ (Nat.succ_pos m)))
    have hMsz : (encNat m).length ≤ Y :=
      (hencM.trans (Nat.le_succ _)).trans
        ((Nat.le_self_pow (by dsimp [D]; omega) S).trans
          (Nat.le_mul_of_pos_left _ (Nat.pow_pos (Nat.succ_pos m))))
    have hmid : (m + 1 + 1) * (3 * ((m + 2) * (2 * (m + 1).size + 3)) +
        (m + 2) * S ^ dp + (m + 2) * (2 * (m + 1).size + 3) + S ^ 2) =
        4 * ((m + 2) * ((m + 2) * (2 * (m + 1).size + 3))) +
          (m + 2) * ((m + 2) * S ^ dp) + (m + 2) * S ^ 2 := by ring
    rw [hmid]
    nlinarith
  · dsimp only [R, B]
    set S := (m + 1).size + 1
    have hS1 : 1 ≤ S := Nat.succ_pos _
    have hencM : (encNat m).length ≤ (m + 1).size := by
      rw [length_encNat]
      exact Nat.size_le_size (Nat.le_succ m)
    have hencM1 : (encNat (m + 1)).length = (m + 1).size := length_encNat (m + 1)
    rw [hencM1]
    set Y := (m + 1) * S ^ D
    have hSD_1 : S ≤ S ^ D := Nat.le_self_pow (by dsimp [D]; omega) S
    have hSD_dp : S ^ dp ≤ S ^ D := Nat.pow_le_pow_right hS1 (by dsimp [D]; omega)
    have hB_le : (m + 2) * (2 * (m + 1).size + 3) ≤ 6 * Y := by
      calc (m + 2) * (2 * (m + 1).size + 3) ≤ (2 * (m + 1)) * (3 * S) :=
            Nat.mul_le_mul (by omega) (by dsimp [S]; omega)
        _ = 6 * ((m + 1) * S) := by ring
        _ ≤ 6 * Y := Nat.mul_le_mul_left 6 (Nat.mul_le_mul_left _ hSD_1)
    have hdp_le : (m + 2) * S ^ dp ≤ 2 * Y := by
      calc (m + 2) * S ^ dp ≤ (2 * (m + 1)) * S ^ D := Nat.mul_le_mul (by omega) hSD_dp
        _ = 2 * Y := by ring
    have hsz_le : (m + 1).size ≤ Y :=
      (Nat.le_succ _).trans (hSD_1.trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos m)))
    nlinarith [hencM]

end FastRangeAndPrimes

end CslibFrontier.Complexity
