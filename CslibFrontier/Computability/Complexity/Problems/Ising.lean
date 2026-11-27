/-
Copyright (c) 2026 Google DeepMind. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Google DeepMind
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.MaxCut
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Ising Spin-Glass Ground-State Energy Decision Problem

`IsingGroundState` is the decision problem for the classical Ising Hamiltonian on a weighted
interaction graph with signed binary integer couplings: given a list of couplings `(u, v, weight)`
and an integer energy threshold `threshold`, does there exist a spin configuration
`s : ℕ → Bool` (interpreting `true ↦ +1` and `false ↦ -1`) whose Ising Hamiltonian
`H_I(s) = - ∑_{e : u ≠ v} W_e s(u) s(v)` is at most `threshold` [Barahona; Lucas ]?

Self-loops (`u = v`) are ignored, matching the convention `H_I = - ∑_{i, j ≠ i} W_{ij} s_i s_j`
for spin-glass Hamiltonians without constant offsets and matching `Cslib.Complexity.MaxCut`.

Reducing `Cslib.Complexity.MaxCut` to `IsingGroundState` sends each weighted edge `(u, v, w)` to
the antiferromagnetic bond `(u, v, -(w : ℤ))` (if `u ≠ v`, and weight `0` if `u = v`) with energy
threshold `(nonLoopWeightSum edges : ℤ) - 2 * (bound : ℤ)`: for every spin assignment `s`, each
non-loop edge contributes `+w` when aligned and `-w = w - 2w` when crossing the cut, so
`H_I(s) = nonLoopWeightSum edges - 2 * cutWeight edges s`. Consequently `IsingGroundState` is
`NP`-complete.

## Main definitions

* `CslibFrontier.Complexity.Ising.Coupling`, `CslibFrontier.Complexity.Ising.encCoupling`: signed
  integer spin couplings and their binary encoding.
* `CslibFrontier.Complexity.Ising.spinSign`, `CslibFrontier.Complexity.Ising.bondEnergy`,
  `CslibFrontier.Complexity.Ising.energy`: spin value `±1`, single-bond interaction `-W s_u s_v`,
  and total Ising Hamiltonian.
* `CslibFrontier.Complexity.IsingInstance`, `CslibFrontier.Complexity.encIsing`,
  `CslibFrontier.Complexity.IsingGroundState`: problem instances, binary encoding, and decision
  set.
* `CslibFrontier.Complexity.Ising.verifier`: polynomial-time subset verifier.
* `CslibFrontier.Complexity.Ising.ofMaxCut`: polynomial-time reduction from `MaxCut`.

## Main results

* `CslibFrontier.Complexity.Ising.isVerifier`, `CslibFrontier.Complexity.Ising.mem_NP`:
  `IsingGroundState ∈ NP encIsing`.
* `CslibFrontier.Complexity.Ising.energy_ofMaxCutEdges`: exact identity
  `energy (ofMaxCutEdges E) s = nonLoopWeightSum E - 2 * cutWeight E s`.
* `CslibFrontier.Complexity.Ising.ofMaxCut_mem_iff`: correctness of the reduction from `MaxCut`.
* `CslibFrontier.Complexity.polyTimeReducible_MaxCut_IsingGroundState`,
  `CslibFrontier.Complexity.IsingGroundState_npHard`,
  `CslibFrontier.Complexity.IsingGroundState_npComplete`: `IsingGroundState` is `NP`-complete.
-/

public section

namespace CslibFrontier.Complexity

open Cslib.Complexity Turing.MultiTapeTM ComputableInPolyTime

namespace Ising

/-- A signed integer Ising coupling between vertices `u` and `v` with coupling strength `weight`
(positive for ferromagnetic, negative for antiferromagnetic). -/
structure Coupling where
  /-- First endpoint vertex. -/
  u : ℕ
  /-- Second endpoint vertex. -/
  v : ℕ
  /-- Signed integer coupling weight `W_{uv}`. -/
  weight : ℤ
  deriving DecidableEq, Repr

/-- Signed couplings are encoded as `(u, v, weight)` with endpoints in `encNat` and `weight` in
signed binary `encIntBin`. -/
enc_structure encCoupling : Coupling where
  u : encNat, v : encNat, weight : encIntBin

attribute [fun_prop] encCoupling_u_polyTime encCoupling_v_polyTime
  encCoupling_weight_polyTime encCoupling_mk_polyTime

/-- The `±1` spin value associated with a Boolean state (`true ↦ 1`, `false ↦ -1`). -/
@[expose] def spinSign (b : Bool) : ℤ :=
  if b then 1 else -1

/-- Single-bond Ising energy `-W_{uv} s_u s_v` for distinct endpoints (`0` on self-loops
`u = v`). -/
@[expose] def bondEnergy (side : ℕ → Bool) (e : Coupling) : ℤ :=
  if e.u == e.v then 0 else -e.weight * spinSign (side e.u) * spinSign (side e.v)

/-- Total Ising Hamiltonian `H_I(E, s) = - ∑_{e ∈ E, u ≠ v} W_e s_u s_v` of coupling list `E`. -/
@[expose] def energy (E : List Coupling) (side : ℕ → Bool) : ℤ :=
  (E.map (bondEnergy side)).sum

/-- Endpoints appearing in coupling list `E`, in order with repetitions. -/
@[expose] def endpoints (E : List Coupling) : List ℕ :=
  E.flatMap fun e => [e.u, e.v]

theorem energy_append (E F : List Coupling) (side : ℕ → Bool) :
    energy (E ++ F) side = energy E side + energy F side := by
  simp only [energy, List.map_append, List.sum_append]

/-- `energy E side` depends only on the spin values at `endpoints E`. -/
theorem energy_congr {E : List Coupling} {side side' : ℕ → Bool}
    (h : ∀ v ∈ endpoints E, side v = side' v) : energy E side = energy E side' := by
  unfold energy
  congr 1
  refine List.map_congr_left fun e he => ?_
  simp only [bondEnergy, h e.u (List.mem_flatMap.2 ⟨e, he, by simp⟩),
    h e.v (List.mem_flatMap.2 ⟨e, he, by simp⟩)]

theorem length_endpoints (E : List Coupling) : (endpoints E).length = 2 * E.length := by
  induction E with
  | nil => rfl
  | cons _ _ ih =>
    simp only [endpoints, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢
    omega

end Ising

/-- An instance of the **Ising ground-state energy decision problem**: a list of signed integer
couplings and an upper threshold `threshold` on the Hamiltonian energy. -/
structure IsingInstance where
  /-- Signed pairwise Ising couplings. -/
  couplings : List Ising.Coupling
  /-- Target upper bound on the Ising Hamiltonian energy. -/
  threshold : ℤ
  deriving DecidableEq, Repr

/-- Instances of `IsingGroundState` are encoded as the framed list of couplings followed by the
signed binary threshold `encIntBin`. -/
enc_structure encIsing : IsingInstance where
  couplings : (encList Ising.encCoupling), threshold : encIntBin

attribute [fun_prop] encIsing_couplings_polyTime encIsing_threshold_polyTime encIsing_mk_polyTime

/-- **Ising spin-glass ground-state decision problem** [Barahona; Lucas ]: there exists a
spin configuration whose Ising energy is at most `threshold`.
-/
@[expose] def IsingGroundState : Set IsingInstance :=
  {x | ∃ S : Finset ℕ, Ising.energy x.couplings (fun v => decide (v ∈ S)) ≤ x.threshold}

namespace Ising

/-- Check whether positive-spin subset `S` achieves Ising energy at most `x.threshold`. -/
@[expose] def check (x : IsingInstance) (S : List ℕ) : Bool :=
  decide (energy x.couplings (fun v => decide (v ∈ S)) ≤ x.threshold)

/-- Polynomial-time subset verifier for `IsingGroundState`, selecting positive-spin vertices among
`endpoints x.couplings`. -/
@[expose] def verifier : IsingInstance × List Bool → Bool :=
  subsetVerifier (fun x => endpoints x.couplings) (Function.uncurry check)

/-- Checking the Ising energy of a candidate spin subset runs in polynomial time. -/
theorem computableInPolyTime_check :
    ComputableInPolyTime (Function.uncurry check) (encPair encIsing (encList encNat))
      encBool := by
  unfold Function.uncurry check energy bondEnergy spinSign
  fun_prop

/-- The `IsingGroundState` verifier runs in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_verifier :
    ComputableInPolyTime verifier (encPair encIsing encBits) encBool :=
  computableInPolyTime_subsetVerifier (encγ := encNat)
    (by unfold endpoints; fun_prop) computableInPolyTime_check

/-- Restricting the positive-spin set `S` to `endpoints x.couplings` preserves membership. -/
theorem mem_IsingGroundState_iff_endpoints {x : IsingInstance} :
    x ∈ IsingGroundState ↔ ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ endpoints x.couplings) ∧
      energy x.couplings (fun v => decide (v ∈ S)) ≤ x.threshold := by
  classical
  refine ⟨fun ⟨S, hS⟩ => ⟨S.filter (· ∈ endpoints x.couplings),
    fun _ hv => (Finset.mem_filter.1 hv).2, ?_⟩, fun ⟨S, _, hS⟩ => ⟨S, hS⟩⟩
  rwa [energy_congr (side' := fun v => decide (v ∈ S)) fun _ hv => by
    simp [Finset.mem_filter, hv]]

/-- `Ising.verifier` verifies `IsingGroundState` with certificates of length `2 * |x|`. -/
theorem isVerifier : IsVerifier encIsing (2 * Polynomial.X) verifier IsingGroundState := by
  have hset : IsingGroundState = {x | ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ endpoints x.couplings) ∧
      energy x.couplings (fun v => decide (v ∈ S)) ≤ x.threshold} :=
    Set.ext fun _ => mem_IsingGroundState_iff_endpoints
  rw [hset]
  refine isVerifier_subsetVerifier (fun x => ?_) fun _ _ _ _ => by
    simp only [Function.uncurry_apply_pair, check, decide_eq_true_eq, List.mem_toFinset]
  rw [encIsing_apply]
  have := (length_le_length_encList encCoupling x.couplings).trans
    (length_le_encPair_left (encList encCoupling) encIntBin (x.couplings, x.threshold))
  simp only [encIsingFields, length_endpoints, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X]
  omega

/-- `IsingGroundState` belongs to `NP`. -/
theorem mem_NP : IsingGroundState ∈ NP encIsing :=
  ⟨2 * Polynomial.X, verifier, computableInPolyTime_verifier, isVerifier⟩

/-! ### Antiferromagnetic Reduction from `MaxCut` -/

/-- Convert each `MaxCut.WeightedEdge` `(u, v, w)` into an antiferromagnetic coupling
`(u, v, -(w : ℤ))`. -/
@[expose] def ofMaxCutEdges (E : List MaxCut.WeightedEdge) : List Coupling :=
  E.map fun e => ⟨e.u, e.v, -(e.weight : ℤ)⟩

/-- Total weight of non-self-loop edges in a `MaxCut` edge list. -/
@[expose] def nonLoopWeightSum (E : List MaxCut.WeightedEdge) : ℕ :=
  ((E.filter fun e => e.u != e.v).map MaxCut.WeightedEdge.weight).sum

/-- Polynomial-time reduction from `MaxCut` to `IsingGroundState`: antiferromagnetic couplings
`W_e = -w_e` and energy threshold `nonLoopWeightSum E - 2 * bound`. -/
@[expose] def ofMaxCut (x : MaxCutInstance) : IsingInstance :=
  ⟨ofMaxCutEdges x.edges, (nonLoopWeightSum x.edges : ℤ) - 2 * (x.bound : ℤ)⟩

/-- Fundamental identity relating antiferromagnetic Ising energy and cut weight:
`energy (ofMaxCutEdges E) side = nonLoopWeightSum E - 2 * cutWeight E side`. -/
theorem energy_ofMaxCutEdges (E : List MaxCut.WeightedEdge) (side : ℕ → Bool) :
    energy (ofMaxCutEdges E) side =
      (nonLoopWeightSum E : ℤ) - 2 * (MaxCut.cutWeight E side : ℤ) := by
  induction E with
  | nil => rfl
  | cons hd E ih =>
    have h_energy :
        energy (ofMaxCutEdges (hd :: E)) side =
          bondEnergy side ⟨hd.u, hd.v, -(hd.weight : ℤ)⟩ + energy (ofMaxCutEdges E) side := by
      simp [ofMaxCutEdges, energy]
    have h_nl :
        nonLoopWeightSum (hd :: E) =
          (if hd.u != hd.v then hd.weight else 0) + nonLoopWeightSum E := by
      unfold nonLoopWeightSum
      by_cases h : (hd.u != hd.v) = true <;> simp [h]
    have h_cw :
        MaxCut.cutWeight (hd :: E) side =
          (if MaxCut.crosses side hd then hd.weight else 0) + MaxCut.cutWeight E side := by
      unfold MaxCut.cutWeight
      by_cases h : MaxCut.crosses side hd = true <;> simp [h]
    rw [h_energy, ih, h_nl, h_cw]
    by_cases hloop : hd.u = hd.v
    · have hbeq : (hd.u == hd.v) = true := beq_iff_eq.mpr hloop
      have hbne : (hd.u != hd.v) = false := by
        rw [_root_.bne, hbeq]
        rfl
      have hcross : MaxCut.crosses side hd = false := by
        simp [MaxCut.crosses, hloop]
      simp only [bondEnergy, hbeq, hbne, hcross, Bool.false_eq_true, ite_true, ite_false,
        zero_add]
    · have hbeq : (hd.u == hd.v) = false := beq_false_of_ne hloop
      have hbne : (hd.u != hd.v) = true := by
        rw [_root_.bne, hbeq]
        rfl
      simp only [bondEnergy, hbeq, hbne, Bool.false_eq_true, ite_false, ite_true, MaxCut.crosses]
      rcases Bool.eq_false_or_eq_true (side hd.u) with hu | hu <;>
        rcases Bool.eq_false_or_eq_true (side hd.v) with hv | hv <;>
        simp [hu, hv, spinSign] <;> ring

/-- **Correctness of `ofMaxCut`**: `ofMaxCut x ∈ IsingGroundState ↔ x ∈ MaxCut`. -/
theorem ofMaxCut_mem_iff (x : MaxCutInstance) :
    ofMaxCut x ∈ IsingGroundState ↔ x ∈ MaxCut := by
  simp only [IsingGroundState, MaxCut, Set.mem_ofPred_eq, ofMaxCut]
  refine exists_congr fun S => ?_
  rw [energy_ofMaxCutEdges]
  omega

/-- `ofMaxCut` runs in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_ofMaxCut :
    ComputableInPolyTime ofMaxCut encMaxCut encIsing := by
  unfold ofMaxCut ofMaxCutEdges nonLoopWeightSum
  fun_prop

end Ising

/-- `MaxCut` reduces to `IsingGroundState` in polynomial time. -/
theorem polyTimeReducible_MaxCut_IsingGroundState :
    PolyTimeReducible encMaxCut encIsing MaxCut IsingGroundState :=
  ⟨Ising.ofMaxCut, Ising.computableInPolyTime_ofMaxCut, fun x => (Ising.ofMaxCut_mem_iff x).symm⟩

/-- `IsingGroundState` is `NP`-hard. -/
theorem IsingGroundState_npHard : NPHard encIsing IsingGroundState :=
  MaxCut_npHard.trans polyTimeReducible_MaxCut_IsingGroundState

/-- **Ising spin-glass ground-state energy is `NP`-complete** [Barahona; Lucas ]. -/
theorem IsingGroundState_npComplete : NPComplete encIsing IsingGroundState :=
  ⟨Ising.mem_NP, IsingGroundState_npHard⟩

end CslibFrontier.Complexity
