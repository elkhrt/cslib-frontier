module

public import CslibFrontier.Computability.Circuit.Boolean.DemiBit
public import CslibFrontier.Computability.Circuit.Boolean.OracleDerandomization
public import CslibFrontier.Computability.Complexity.ProofSystem.FregeReduction

import Cslib.Computability.Circuit.Composition
import Cslib.Foundations.Data.Polynomial.Monotone
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatPower
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListToBits
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.ResourceFacts
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Nat.Log
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Proof Complexity Generators, Uniform `NP` Equivalence, and Failure of Strong FDP

This module formalizes hardness (`IsHardFor`) and disjunction-hardness (`IsDisjunctionHardFor`) of
proof complexity generators against Cook–Reckhow propositional proof systems, nondeterministic De
Morgan circuits deciding short proofs of range-avoidance `τ`-formulas in proof systems with one bit
of advice, uniform polynomial-time stretching generators (`UniformPTimeGenerator`) together with
their characterization via infinite `NP` subsets avoiding the range, and a theorem
refuting the strong feasible disjunction property from `ENPHypothesis` and a uniform hard
generator (`UniformHardGeneratorConjecture`).

## Main definitions

* `CslibFrontier.ProofComplexity.IsHardFor`: hardness of a `P/poly` generator for a Cook–Reckhow
  proof system.
* `CslibFrontier.ProofComplexity.HardGeneratorConjecture`: existence of a `P/poly` generator hard
  for all Cook–Reckhow propositional proof systems.
* `CslibFrontier.ProofComplexity.tauDisjuncts`, `CslibFrontier.ProofComplexity.tauDisjunction`:
  pairwise atom-disjoint disjunctions of range-avoidance formulas `τ(c)_b`.
* `CslibFrontier.ProofComplexity.IsDisjunctionHardFor`: disjunction-hardness (`⋁`-hardness) of a
  generator for a propositional proof system.
* `CslibFrontier.ProofComplexity.natToBitsLen`, `CslibFrontier.ProofComplexity.bitStringToNat`,
  `CslibFrontier.ProofComplexity.allSeedStrings`: uniform polynomial-time logarithmic-seed
  enumeration.
* `CslibFrontier.ProofComplexity.circuitCastOut`: output-length cast on De Morgan circuits.
* `CslibFrontier.ProofComplexity.UniformPTimeGenerator`: uniform polynomial-time stretching Boolean
  circuit generator with strictly increasing output length `m(n) > n`.
* `CslibFrontier.ProofComplexity.UniformHardGeneratorConjecture`: existence of a uniform
  polynomial-time generator hard for all Cook–Reckhow propositional proof systems.

## Main results

* `CslibFrontier.ProofComplexity.exists_nondetCircuit_adviceProofLength_tauFormula`: polynomial-size
  nondeterministic circuits deciding short `pps/1` proofs of `τ(c)_a`.
* `CslibFrontier.ProofComplexity.isHardFor_iff_eventually`,
  `CslibFrontier.ProofComplexity.IsHardFor.of_simulates`: asymptotic characterization and simulation
  invariance of generator hardness.
* `CslibFrontier.ProofComplexity.IsDisjunctionHardFor.isHardFor`,
  `CslibFrontier.ProofComplexity.isDisjunctionHardFor_of_hasStrongFDPPoly`: relation between
  disjunction-hardness, hardness, and the strong feasible disjunction property.
* `CslibFrontier.ProofComplexity.UniformPTimeGenerator.forall_isHardFor_iff_np_inter`: a uniform
  polynomial-time generator is hard for all Cook–Reckhow proof systems iff its range intersects
  every infinite `NP` subset of its output slices.
* `CslibFrontier.ProofComplexity.exists_pps_not_hasStrongFDP_of_enp_and_uniformHard`: under
  `ENPHypothesis` and `UniformHardGeneratorConjecture`, there exists a strong proof system `Q`
  such that no proof system simulating `Q` has the strong feasible disjunction property.


-/

public section

namespace CslibFrontier.ProofComplexity

open CslibFrontier.Computability
open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Logic.PL Cslib.Complexity
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open Filter Finset

/-! ### Nondeterministic circuits deciding short `pps/1` proofs of `τ`-formulas -/

/-- Output bit-length bound for any polynomial-time computable function. -/
theorem exists_output_length_le {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {f : α → β} (hf : ComputableInPolyTime f encA encB) :
    ∃ c d : ℕ, ∀ a : α, (encB (f a)).length ≤ c * ((encA a).length + 1) ^ d := by
  obtain ⟨t, _, ht, -, _, _, _, tm, htm⟩ := hf
  obtain ⟨c, d, hle⟩ := polynomiallyBounded_iff_le.1 ht
  exact ⟨c, d, fun a => (htm a).length_output_le.trans (hle (encA a).length)⟩

/-- Program negating the first `k ≤ m` inputs of a `BitString (m + t)`. -/
private def negDupProg (m t : ℕ) : (k : ℕ) → k ≤ m → Program signature (m + t) k
  | 0, _ => .empty
  | k + 1, hk => (negDupProg m t k (by omega)).gate ⟨.not, fun _ => .input ⟨k, by omega⟩⟩

private theorem eval_negDupProg {m t : ℕ} (a : BitString m) (w : BitString t) :
    ∀ (k : ℕ) (hk : k ≤ m) (j : Fin k),
      (negDupProg m t k hk).eval interpretation (Fin.append a w) j = !a ⟨j.val, by omega⟩
  | 0, _, j => j.elim0
  | k + 1, hk, j => by
    refine Fin.lastCases ?_ (fun i => ?_) j
    · dsimp only [negDupProg]
      rw [Program.eval_gate_last]
      simp only [Line.eval, interpretation, Function.comp_apply, Wire.elim, Fin.val_last]
      exact congrArg Bool.not (Fin.append_left a w ⟨k, by omega⟩)
    · dsimp only [negDupProg]
      rw [Program.eval_gate_castSucc]
      exact eval_negDupProg a w k (by omega) i

/-- Preprocessing circuit `(a, w) ↦ ((a, ¬a), w)` of exact gate count `m`. -/
private def negDupPrepCircuit (m t : ℕ) : Circuit signature (m + t) ((m + m) + t) where
  size := m
  program := negDupProg m t m le_rfl
  outputs i :=
    if h1 : i.val < m then .input ⟨i.val, by omega⟩
    else if h2 : i.val < m + m then .gate ⟨i.val - m, by omega⟩
    else .input ⟨m + (i.val - (m + m)), by omega⟩

private theorem eval_negDupPrepCircuit {m t : ℕ} (a : BitString m) (w : BitString t) :
    (negDupPrepCircuit m t).eval interpretation (Fin.append a w) =
      Fin.append (Fin.append a (fun j : Fin m => !a j)) w := by
  set x := Fin.append a w
  have hgate (k : Fin m) : (negDupPrepCircuit m t).program.eval interpretation x k = !a k :=
    eval_negDupProg a w m le_rfl k
  funext i
  dsimp only [Circuit.eval, Program.trace, Function.comp_apply, negDupPrepCircuit]
  by_cases h1 : i.val < m
  · rw [dite_eq_left h1]; dsimp only [Wire.elim]
    have hl : x ⟨i.val, by omega⟩ = a ⟨i.val, h1⟩ := Fin.append_left a w ⟨i.val, h1⟩
    have hi1 : i = Fin.castAdd t ⟨i.val, by omega⟩ := Fin.ext rfl
    have hi2 : (⟨i.val, by omega⟩ : Fin (m + m)) = Fin.castAdd m ⟨i.val, h1⟩ := Fin.ext rfl
    have hr : Fin.append (Fin.append a (fun j : Fin m => !a j)) w i = a ⟨i.val, h1⟩ := by
      conv_lhs => rw [hi1]
      rw [Fin.append_left]
      conv_lhs => rw [hi2]
      exact Fin.append_left _ _ _
    exact hl.trans hr.symm
  · rw [dite_eq_right h1]
    by_cases h2 : i.val < m + m
    · rw [dite_eq_left h2]; dsimp only [Wire.elim]
      have hl := hgate ⟨i.val - m, by omega⟩
      have hi1 : i = Fin.castAdd t ⟨i.val, h2⟩ := Fin.ext rfl
      have hi2 : (⟨i.val, h2⟩ : Fin (m + m)) = Fin.natAdd m ⟨i.val - m, by omega⟩ :=
        Fin.ext (by dsimp; omega)
      have hr : Fin.append (Fin.append a (fun j : Fin m => !a j)) w i =
          !a ⟨i.val - m, by omega⟩ := by
        conv_lhs => rw [hi1]
        rw [Fin.append_left]
        conv_lhs => rw [hi2]
        exact Fin.append_right a (fun j : Fin m => !a j) ⟨i.val - m, by omega⟩
      exact hl.trans hr.symm
    · rw [dite_eq_right h2]; dsimp only [Wire.elim]
      have hl : x ⟨m + (i.val - (m + m)), by omega⟩ = w ⟨i.val - (m + m), by omega⟩ :=
        Fin.append_right a w ⟨i.val - (m + m), by omega⟩
      have hi1 : i = Fin.natAdd (m + m) ⟨i.val - (m + m), by omega⟩ :=
        Fin.ext (by dsimp; omega)
      have hr : Fin.append (Fin.append a (fun j : Fin m => !a j)) w i =
          w ⟨i.val - (m + m), by omega⟩ := by
        conv_lhs => rw [hi1]
        exact Fin.append_right _ w _
      exact hl.trans hr.symm

/-- **Polynomial-size nondeterministic circuits deciding short `pps/1` proofs of `τ`-formulas.**
For every propositional proof system `P` with `1` bit of advice, there exist constants `C, d ≥ 1`
such that for every De Morgan circuit `c : Circuit signature n m` and proof-length threshold
`t : ℕ`, the set `{a : BitString m | ∃ π, P.eval π = tauFormula 0 c a ∧ π.length ≤ t}` is
disjoint from `Set.range (c.eval interpretation)` and nondeterministically decided by a De Morgan
circuit `D` of size at most `C * ((n + c.size + m + 12) ^ 2 + t + 1) ^ d`. -/
theorem exists_nondetCircuit_adviceProofLength_tauFormula
    (P : PropProofSystemWithAdvice (fun _ => 1)) :
    ∃ C d : ℕ, 1 ≤ C ∧ 1 ≤ d ∧
      ∀ {n m : ℕ} (c : Circuit signature n m) (t : ℕ),
        let B : Set (BitString m) :=
          {a | ∃ π : List Bool, P.eval π = tauFormula 0 c a ∧ π.length ≤ t}
        ∃ D : Circuit signature (m + t) 1,
          D.size ≤ C * ((n + c.size + m + 12) ^ 2 + t + 1) ^ d ∧
          D.NondeterministicDecides interpretation {true} B ∧
          Disjoint B (Set.range (c.eval interpretation)) := by
  obtain ⟨C₀, d₀, hnd⟩ := exists_nondetCircuit_adviceProofLength_le P
  refine ⟨(C₀ + 2) * 20 ^ (d₀ + 1), d₀ + 1,
    Nat.mul_pos (by omega) (Nat.pow_pos (by decide)), by omega, fun {n m} c t => ?_⟩
  obtain ⟨L, ρ, hL, hρ⟩ := exists_substitute_encFormula_tauFormula c
  obtain ⟨D₀, hD₀sz, hD₀iff, hD₀taut⟩ :=
    hnd (tauFormula 0 c) (fun a => Fin.append a (fun j => !a j)) ρ hρ t
  refine ⟨D₀.comp (negDupPrepCircuit m t), ?_, fun a => ?_, Set.disjoint_left.2 fun a ha hmem => ?_⟩
  · set M := (n + c.size + m + 12) ^ 2 + t + 1
    have hM1 : 1 ≤ M := by dsimp only [M]; omega
    have hmM : m ≤ M := (show m ≤ n + c.size + m + 12 by omega).trans
      ((Nat.le_self_pow (by decide : 2 ≠ 0) (n + c.size + m + 12)).trans (by dsimp only [M]; omega))
    have hLM : L + t + 1 ≤ 20 * M := by dsimp only [M]; omega
    have hpow : (L + t + 1) ^ d₀ ≤ (20 * M) ^ (d₀ + 1) :=
      (Nat.pow_le_pow_left hLM d₀).trans (Nat.pow_le_pow_right (by omega) (by omega))
    have hP : 1 ≤ 20 ^ (d₀ + 1) * M ^ d₀ :=
      Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos hM1)
    rw [Circuit.size_comp, show (negDupPrepCircuit m t).size = m from rfl]
    calc m + D₀.size ≤ M + C₀ * (20 * M) ^ (d₀ + 1) :=
          Nat.add_le_add hmM (hD₀sz.trans (Nat.mul_le_mul_left C₀ hpow))
      _ = M * 1 + C₀ * (20 ^ (d₀ + 1) * M ^ (d₀ + 1)) := by rw [mul_one, Nat.mul_pow]
      _ ≤ M * (20 ^ (d₀ + 1) * M ^ d₀) + C₀ * (20 ^ (d₀ + 1) * M ^ (d₀ + 1)) :=
          Nat.add_le_add_right (Nat.mul_le_mul_left M hP) _
      _ = (C₀ + 1) * 20 ^ (d₀ + 1) * M ^ (d₀ + 1) := by rw [pow_succ]; ring
      _ ≤ (C₀ + 2) * 20 ^ (d₀ + 1) * M ^ (d₀ + 1) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
  · simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Circuit.eval_comp,
      eval_negDupPrepCircuit]
    exact hD₀iff a
  · exact (tauFormula_mem_taut_iff 0 c a).1 (hD₀taut a ha) hmem

/-! ### Hardness and disjunction-hardness of proof complexity generators -/

/-- A `P/poly` stretching generator `g` is **hard** for a Cook–Reckhow propositional proof system
`P` iff for every exponent `c ≥ 1`, only finitely many non-outputs `b ∉ Set.range (g.eval n)`
have a `P`-proof of `τ(g_n)_b` of length at most `|τ(g_n)_b| ^ c`. -/
@[expose]
def IsHardFor {m : ℕ → ℕ} (g : PPolyGenerator m) (P : PropProofSystem) : Prop :=
  ∀ c : ℕ, 1 ≤ c →
    {p : Σ n : ℕ, BitString (m n) |
      p.2 ∉ Set.range (g.eval p.1) ∧
      proofLength P (tauFormula 0 (g.circuit p.1) p.2) ≤
        (encFormula (tauFormula 0 (g.circuit p.1) p.2)).length ^ c}.Finite

/-- Equivalent asymptotic characterization of `IsHardFor`: for every `c ≥ 1` and all sufficiently
large input lengths `n`, every `b ∉ Set.range (g.eval n)` requires `P`-proofs of `τ(g_n)_b` of
length strictly greater than `|τ(g_n)_b| ^ c`. -/
theorem isHardFor_iff_eventually {m : ℕ → ℕ} (g : PPolyGenerator m) (P : PropProofSystem) :
    IsHardFor g P ↔
      ∀ c : ℕ, 1 ≤ c → ∀ᶠ n : ℕ in atTop, ∀ b : BitString (m n),
        b ∉ Set.range (g.eval n) →
        (encFormula (tauFormula 0 (g.circuit n) b)).length ^ c <
          proofLength P (tauFormula 0 (g.circuit n) b) := by
  constructor
  · intro hh c hc
    obtain ⟨N, hN⟩ := (hh c hc |>.image Sigma.fst).bddAbove
    filter_upwards [eventually_gt_atTop N] with n hn b hb
    by_contra hle
    exact not_le_of_gt hn (hN ⟨⟨n, b⟩, ⟨hb, le_of_not_gt hle⟩, rfl⟩)
  · intro hev c hc
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hev c hc)
    have hfin : (⋃ n ∈ Iio N, (Sigma.mk n '' (Set.univ : Set (BitString (m n))))).Finite :=
      (finite_toSet (Iio N)).biUnion fun n _ => Set.finite_univ.image (Sigma.mk n)
    refine hfin.subset fun ⟨n, b⟩ ⟨hb, hle⟩ => ?_
    have hlt : n < N := by
      by_contra hge
      exact not_lt_of_ge hle (hN n (le_of_not_gt hge) b hb)
    exact Set.mem_iUnion₂.2 ⟨n, mem_Iio.2 hlt, b, Set.mem_univ b, rfl⟩

/-- Every univariate polynomial over `ℕ` is bounded by `(x + 2) ^ e` for a constant `e ≥ 1`. -/
theorem exists_pow_bound_poly (p : Polynomial ℕ) :
    ∃ e : ℕ, 1 ≤ e ∧ ∀ x : ℕ, p.eval x ≤ (x + 2) ^ e := by
  let c := p.eval 1 + 1
  let d := p.natDegree + 1
  refine ⟨c + d, by dsimp only [c, d]; omega, fun x => ?_⟩
  have h1 : p.eval x ≤ p.eval 1 * (x + 2) ^ p.natDegree := by
    have hm : p.eval x ≤ p.eval (x + 2) := p.eval_mono (by omega)
    refine hm.trans ?_
    rw [Polynomial.eval_eq_sum_range]
    calc ∑ i ∈ range (p.natDegree + 1), p.coeff i * (x + 2) ^ i
        ≤ ∑ i ∈ range (p.natDegree + 1), p.coeff i * (x + 2) ^ p.natDegree :=
          sum_le_sum fun i hi => Nat.mul_le_mul_left _
            (Nat.pow_le_pow_right (by omega) (Nat.lt_succ_iff.1 (mem_range.1 hi)))
      _ = p.eval 1 * (x + 2) ^ p.natDegree := by
          rw [← sum_mul, Polynomial.eval_eq_sum_range]; simp
  have h2 : c ≤ (x + 2) ^ c := by
    have : c < 2 ^ c := Nat.lt_two_pow_self
    exact this.le.trans (Nat.pow_le_pow_left (by omega) c)
  calc p.eval x ≤ c * (x + 2) ^ d :=
        h1.trans (Nat.mul_le_mul (by dsimp only [c]; omega)
          (Nat.pow_le_pow_right (by omega) (by dsimp only [d]; omega)))
    _ ≤ (x + 2) ^ c * (x + 2) ^ d := Nat.mul_le_mul_right _ h2
    _ = (x + 2) ^ (c + d) := (pow_add _ c d).symm

/-- Hardness is downward-closed under proof-system simulation: if `P` simulates `Q` and `g` is
hard for `P`, then `g` is hard for `Q`. -/
theorem IsHardFor.of_simulates {m : ℕ → ℕ} {g : PPolyGenerator m} {P Q : PropProofSystem}
    (hsim : P.Simulates Q) (hh : IsHardFor g P) : IsHardFor g Q := by
  obtain ⟨p, hp⟩ := simulates_iff_proofLength.1 hsim
  obtain ⟨e, he1, hpe⟩ := exists_pow_bound_poly p
  rw [isHardFor_iff_eventually] at hh ⊢
  intro c hc
  filter_upwards [hh ((c + 2) * e) (Nat.mul_pos (by omega) he1), eventually_ge_atTop 2]
    with n hn hn2 b hb
  by_contra hle
  have htaut : tauFormula 0 (g.circuit n) b ∈ TAUT := (tauFormula_mem_taut_iff 0 _ b).2 hb
  set L := (encFormula (tauFormula 0 (g.circuit n) b)).length
  have hL2 : 2 ≤ L := by
    have := g.stretch n
    have := output_le_length_encFormula_tauFormula 0 (g.circuit n) b
    omega
  have hLpow : L ^ c + 2 ≤ L ^ (c + 2) := by
    have h1 : 1 ≤ L ^ c := Nat.pow_pos (by omega)
    calc L ^ c + 2 ≤ 3 * L ^ c := by omega
      _ ≤ L ^ 2 * L ^ c := Nat.mul_le_mul_right _ (by nlinarith)
      _ = L ^ (c + 2) := by rw [← pow_add, add_comm]
  have hP_le : proofLength P (tauFormula 0 (g.circuit n) b) ≤ L ^ ((c + 2) * e) :=
    calc proofLength P (tauFormula 0 (g.circuit n) b)
        ≤ p.eval (proofLength Q (tauFormula 0 (g.circuit n) b)) := hp _ htaut
      _ ≤ p.eval (L ^ c) := p.eval_mono (le_of_not_gt hle)
      _ ≤ (L ^ c + 2) ^ e := hpe (L ^ c)
      _ ≤ (L ^ (c + 2)) ^ e := Nat.pow_le_pow_left hLpow e
      _ = L ^ ((c + 2) * e) := (pow_mul L (c + 2) e).symm
  exact not_lt_of_ge hP_le (hn b hb)

/-- **Proof complexity generator conjecture (non-uniform form)**:
there exists a `P/poly` stretching generator simultaneously hard for every Cook–Reckhow
propositional proof system. -/
@[expose]
def HardGeneratorConjecture : Prop :=
  ∃ (m : ℕ → ℕ) (g : PPolyGenerator m), ∀ P : PropProofSystem, IsHardFor g P

/-- List of pairwise atom-disjoint `τ(c)_b` formulas across `bs : List (BitString m)`, placing
the `idx`-th copy on atoms `[idx * (n + c.size), (idx + 1) * (n + c.size))`. -/
def tauDisjuncts {n m : ℕ} (c : Circuit signature n m) (bs : List (BitString m)) :
    List Formula :=
  bs.mapIdx fun idx b => tauFormula (idx * (n + c.size)) c b

/-- Pairwise atom-disjoint disjunction `⋁_{b ∈ bs} τ(c)_b` of range-avoidance formulas. -/
def tauDisjunction {n m : ℕ} (c : Circuit signature n m) (bs : List (BitString m)) : Formula :=
  bigOr (tauDisjuncts c bs)

/-- No two disjuncts in `tauDisjuncts c bs` share a propositional atom. -/
theorem areAtomDisjoint_tauDisjuncts {n m : ℕ} (c : Circuit signature n m)
    (bs : List (BitString m)) : AreAtomDisjoint (tauDisjuncts c bs) := by
  change (tauDisjuncts c bs).Pairwise _
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hlt
  simp only [tauDisjuncts, List.length_mapIdx, List.getElem_mapIdx] at hi hj ⊢
  refine Finset.disjoint_left.2 fun a ha₁ ha₂ => ?_
  have h1 := mem_Ico.1 (formulaAtoms_tauFormula_subset _ c bs[i] ha₁)
  have h2 := mem_Ico.1 (formulaAtoms_tauFormula_subset _ c bs[j] ha₂)
  have hle : (i + 1) * (n + c.size) ≤ j * (n + c.size) := Nat.mul_le_mul_right _ hlt
  nlinarith

/-- A nonempty pairwise atom-disjoint disjunction `tauDisjunction c bs` is a tautology iff at least
one `b ∈ bs` lies outside `Set.range (c.eval interpretation)`. -/
theorem tauDisjunction_mem_taut_iff {n m : ℕ} (c : Circuit signature n m)
    (bs : List (BitString m)) :
    tauDisjunction c bs ∈ TAUT ↔ ∃ b ∈ bs, b ∉ Set.range (c.eval interpretation) := by
  rw [tauDisjunction, bigOr_mem_taut_iff_of_areAtomDisjoint (areAtomDisjoint_tauDisjuncts c bs)]
  constructor
  · rintro ⟨φ, hφ, ht⟩
    rw [tauDisjuncts, List.mem_iff_getElem] at hφ
    obtain ⟨i, hi, rfl⟩ := hφ
    simp only [List.length_mapIdx, List.getElem_mapIdx] at hi ht
    exact ⟨bs[i], List.getElem_mem hi, (tauFormula_mem_taut_iff _ c _).1 ht⟩
  · rintro ⟨b, hb, hnot⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hb
    refine ⟨(tauDisjuncts c bs)[i]'(by simp [tauDisjuncts, hi]), List.getElem_mem _, ?_⟩
    simpa only [tauDisjuncts, List.getElem_mapIdx, tauFormula_mem_taut_iff] using hnot

/-- **Disjunction-hardness (`⋁`-hardness)** of a generator `g` for a Cook–Reckhow propositional
proof system `P`: for every `c ≥ 1`, only finitely many finite subsets
`B ⊆ {0, 1}^{m(n)}` have a `P`-proof of the pairwise atom-disjoint disjunction
`⋁_{b ∈ B} τ(g_n)_b` of size at most `m(n) ^ c`. -/
@[expose]
def IsDisjunctionHardFor {m : ℕ → ℕ} (g : PPolyGenerator m) (P : PropProofSystem) : Prop :=
  ∀ c : ℕ, 1 ≤ c →
    {p : Σ n : ℕ, Finset (BitString (m n)) |
      ∃ (bs : List (BitString (m p.1))) (π : List Bool),
        bs.Nodup ∧ (∀ b, b ∈ bs ↔ b ∈ p.2) ∧
        P π = tauDisjunction (g.circuit p.1) bs ∧
        π.length ≤ (m p.1) ^ c}.Finite

/-- Disjunction-hardness implies ordinary generator hardness (via singleton subsets `B = {b}`). -/
theorem IsDisjunctionHardFor.isHardFor {m : ℕ → ℕ} {g : PPolyGenerator m} {P : PropProofSystem}
    (h : IsDisjunctionHardFor g P) : IsHardFor g P := by
  obtain ⟨pg, hpg⟩ := g.size_poly
  let pτ : Polynomial ℕ :=
    Polynomial.C 20 * (Polynomial.C 2 * Polynomial.X + pg + Polynomial.C 12) ^ 2
  obtain ⟨e, he1, hpe⟩ := exists_pow_bound_poly pτ
  rw [isHardFor_iff_eventually]
  intro c hc
  have hfin := h (2 * e * c) (Nat.mul_pos (Nat.mul_pos two_pos he1) hc)
  obtain ⟨N, hN⟩ := (hfin.image Sigma.fst).bddAbove
  filter_upwards [eventually_gt_atTop (max N 1)] with n hn b hb
  by_contra hle
  have hmn2 : 2 ≤ m n := by have := g.stretch n; omega
  have htaut : tauFormula 0 (g.circuit n) b ∈ TAUT := (tauFormula_mem_taut_iff 0 _ b).2 hb
  obtain ⟨π, hπ, hπlen⟩ := (proofLength_le_iff P htaut).1 (le_of_not_gt hle)
  have hτ_le : (encFormula (tauFormula 0 (g.circuit n) b)).length ≤ (m n) ^ (2 * e) := by
    have h0 := length_encFormula_tauFormula_zero_le (g.circuit n) b
    have hnm : n ≤ m n := (g.stretch n).le
    have hcs := hpg n
    have h1 : 20 * (n + (g.circuit n).size + m n + 12) ^ 2 ≤ pτ.eval (m n) := by
      simp only [pτ, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
        Polynomial.eval_C, Polynomial.eval_X]
      exact Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left (by omega) 2)
    have h2 : m n + 2 ≤ (m n) ^ 2 := by nlinarith
    calc (encFormula (tauFormula 0 (g.circuit n) b)).length
        ≤ pτ.eval (m n) := h0.trans h1
      _ ≤ (m n + 2) ^ e := hpe (m n)
      _ ≤ ((m n) ^ 2) ^ e := Nat.pow_le_pow_left h2 e
      _ = (m n) ^ (2 * e) := (pow_mul (m n) 2 e).symm
  have hπm : π.length ≤ (m n) ^ (2 * e * c) :=
    hπlen.trans ((Nat.pow_le_pow_left hτ_le c).trans_eq (pow_mul (m n) (2 * e) c).symm)
  refine not_le_of_gt ((le_max_left N 1).trans_lt hn) (hN ⟨⟨n, {b}⟩, ?_, rfl⟩)
  exact ⟨[b], π, List.nodup_singleton b, fun x => by simp,
    by simpa [tauDisjunction, tauDisjuncts] using hπ, hπm⟩

/-- Any proof system `P` with the strong feasible disjunction property promotes hardness of `g` for
`closeUnderSubstFrege P` directly to disjunction-hardness of `g` for `P`. -/
theorem isDisjunctionHardFor_of_hasStrongFDPPoly {m : ℕ → ℕ} {g : PPolyGenerator m}
    {P : PropProofSystem} (hfdp : HasStrongFDPPoly P)
    (hh : IsHardFor g (closeUnderSubstFrege P)) : IsDisjunctionHardFor g P := by
  have hfdp' : ∃ p : Polynomial ℕ, ∀ (αs : List Formula) (π : List Bool),
      αs ≠ [] → AreAtomDisjoint αs → P π = bigOr αs →
      ∃ α ∈ αs, ∃ π' : List Bool, P π' = α ∧ π'.length ≤ p.eval π.length := hfdp
  obtain ⟨pf, hpf⟩ := hfdp'
  obtain ⟨pg, hpg⟩ := g.size_poly
  obtain ⟨ef, hef1, hpef⟩ := exists_pow_bound_poly pf
  obtain ⟨eg, heg1, hpeg⟩ := exists_pow_bound_poly pg
  rw [isHardFor_iff_eventually] at hh
  intro c hc
  let d : ℕ := max (2 * c * ef + 4) (2 * eg + 8)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hh d (by dsimp only [d]; omega))
  let N₀ := max N 2
  have hfin : (⋃ n ∈ Iio N₀, (Sigma.mk n '' (Set.univ : Set (Finset (BitString (m n)))))).Finite :=
    (finite_toSet (Iio N₀)).biUnion fun n _ => Set.finite_univ.image (Sigma.mk n)
  refine hfin.subset fun ⟨n, B⟩ ⟨bs, π, hnodup, _, hπ, hπlen⟩ => ?_
  dsimp only at bs hπ hπlen
  by_contra hnot
  have hn_ge : N₀ ≤ n := by
    by_contra hlt
    exact hnot (Set.mem_iUnion₂.2 ⟨n, mem_Iio.2 (lt_of_not_ge hlt), B, Set.mem_univ B, rfl⟩)
  have hmn2 : 2 ≤ m n := by have := g.stretch n; dsimp only [N₀] at hn_ge; omega
  have hbs_ne : bs ≠ [] := by
    rintro rfl
    have ht : (Proposition.falsum : Formula) ∈ TAUT := by
      have hm := P.mem π; rwa [hπ, tauDisjunction, tauDisjuncts, List.mapIdx_nil, bigOr_nil] at hm
    exact Bool.false_ne_true (ht fun _ => false)
  have hdj_ne : tauDisjuncts (g.circuit n) bs ≠ [] := by
    intro he; apply hbs_ne; simpa [tauDisjuncts] using he
  obtain ⟨α, hα, π', hπ', hπ'len⟩ := hpf (tauDisjuncts (g.circuit n) bs) π hdj_ne
    (areAtomDisjoint_tauDisjuncts _ bs) hπ
  obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.1 hα
  simp only [tauDisjuncts, List.length_mapIdx, List.getElem_mapIdx] at hidx hπ' ⊢
  set b := bs[idx]
  set base := idx * (n + (g.circuit n).size)
  have hb_not : b ∉ Set.range (g.eval n) :=
    (tauFormula_mem_taut_iff base (g.circuit n) b).1 (hπ' ▸ P.mem π')
  obtain ⟨π'', hπ'', hπ''len⟩ := closeUnderSubstFrege_shift P π' base
  rw [hπ', renameAtoms_sub_tauFormula] at hπ''
  have hbs_len : bs.length ≤ 2 ^ m n := by
    simpa [BitString.card] using hnodup.length_le_card
  have hbase_le : base ≤ 2 ^ (m n + 2 * eg * m n) := by
    have hidx_le : idx ≤ 2 ^ m n := (le_of_lt hidx).trans hbs_len
    have hsz : n + (g.circuit n).size ≤ (m n + 2) ^ (eg + 1) := by
      have h1 : (g.circuit n).size ≤ (m n + 2) ^ eg := (hpg n).trans (hpeg (m n))
      have h2 : n ≤ m n := (g.stretch n).le
      calc n + (g.circuit n).size ≤ m n + (m n + 2) ^ eg := Nat.add_le_add h2 h1
        _ ≤ (m n + 2) ^ eg + (m n + 2) ^ eg :=
            Nat.add_le_add_right
              ((show m n ≤ m n + 2 by omega).trans (Nat.le_self_pow (by omega) _)) _
        _ ≤ (m n + 2) * (m n + 2) ^ eg := by nlinarith
        _ = (m n + 2) ^ (eg + 1) := by rw [pow_succ, mul_comm]
    have hpow2 : m n + 2 ≤ 2 ^ m n := by
      have aux : ∀ k : ℕ, 2 ≤ k → k + 2 ≤ 2 ^ k := by
        intro k hk
        induction k with
        | zero => omega
        | succ k ih =>
          by_cases hk2 : 2 ≤ k
          · have h1 := ih hk2
            have h2 : 4 ≤ 2 ^ k := (show 4 = 2 ^ 2 by norm_num) ▸ Nat.pow_le_pow_right two_pos hk2
            rw [pow_succ]; omega
          · have : k = 1 := by omega
            subst this; norm_num
      exact aux (m n) hmn2
    have hsz2 : n + (g.circuit n).size ≤ 2 ^ (2 * eg * m n) :=
      calc n + (g.circuit n).size ≤ (2 ^ m n) ^ (eg + 1) :=
            hsz.trans (Nat.pow_le_pow_left hpow2 (eg + 1))
        _ = 2 ^ (m n * (eg + 1)) := (pow_mul 2 (m n) (eg + 1)).symm
        _ ≤ 2 ^ (2 * eg * m n) := Nat.pow_le_pow_right two_pos (by nlinarith)
    calc base ≤ 2 ^ m n * 2 ^ (2 * eg * m n) := Nat.mul_le_mul hidx_le hsz2
      _ = 2 ^ (m n + 2 * eg * m n) := (pow_add 2 _ _).symm
  have henc_base : (encNat base).length ≤ (2 * eg + 2) * m n := by
    have := length_encNat_le_of_le_two_pow hbase_le
    nlinarith
  have hπ'_bd : π'.length ≤ (m n) ^ (2 * c * ef) := by
    have h1 : (m n) ^ c + 2 ≤ (m n) ^ (2 * c) := by
      have : 2 ≤ (m n) ^ c :=
        hmn2.trans (Nat.le_self_pow (by omega) (m n))
      calc (m n) ^ c + 2 ≤ (m n) ^ c * (m n) ^ c := by nlinarith
        _ = (m n) ^ (2 * c) := by rw [← pow_add, two_mul]
    calc π'.length ≤ pf.eval π.length := hπ'len
      _ ≤ pf.eval ((m n) ^ c) := pf.eval_mono hπlen
      _ ≤ ((m n) ^ c + 2) ^ ef := hpef _
      _ ≤ ((m n) ^ (2 * c)) ^ ef := Nat.pow_le_pow_left h1 ef
      _ = (m n) ^ (2 * c * ef) := (pow_mul (m n) (2 * c) ef).symm
  have hπ''_bd : π''.length ≤ (encFormula (tauFormula 0 (g.circuit n) b)).length ^ d := by
    have h16 : 16 ≤ (m n) ^ 4 :=
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ (m n) ^ 4 := Nat.pow_le_pow_left hmn2 4
    have ht1 : 8 * π'.length ≤ 8 * (m n) ^ (d - 4) :=
      Nat.mul_le_mul_left 8 (hπ'_bd.trans
        (Nat.pow_le_pow_right (by omega) (by dsimp only [d]; omega)))
    have ht2 : 8 * (encNat base).length + 32 ≤ 8 * (m n) ^ (d - 4) := by
      have hle2 : 2 * eg + 6 ≤ 2 ^ (2 * eg + 3) := by
        clear * -
        induction eg with
        | zero => decide
        | succ k ih =>
          rw [show 2 * (k + 1) + 3 = (2 * k + 3) + 2 by omega, pow_add]; omega
      have hstep : 2 * eg + 6 ≤ (m n) ^ (2 * eg + 3) :=
        hle2.trans (Nat.pow_le_pow_left hmn2 _)
      have hprod : (2 * eg + 2) * m n + 4 ≤ (m n) ^ (2 * eg + 4) :=
        calc (2 * eg + 2) * m n + 4 ≤ (2 * eg + 6) * m n := by nlinarith
          _ ≤ (m n) ^ (2 * eg + 3) * m n := Nat.mul_le_mul_right _ hstep
          _ = (m n) ^ (2 * eg + 4) := (pow_succ _ _).symm
      exact (show 8 * (encNat base).length + 32 ≤ 8 * ((2 * eg + 2) * m n + 4) by omega).trans
        (Nat.mul_le_mul_left 8 (hprod.trans
          (Nat.pow_le_pow_right (by omega) (by dsimp only [d]; omega))))
    have hsum : π''.length ≤ (m n) ^ d :=
      calc π''.length ≤ 16 * (m n) ^ (d - 4) := by omega
        _ ≤ (m n) ^ 4 * (m n) ^ (d - 4) := Nat.mul_le_mul_right _ h16
        _ = (m n) ^ d := by rw [← pow_add]; congr 1; dsimp only [d]; omega
    exact hsum.trans
      (Nat.pow_le_pow_left (output_le_length_encFormula_tauFormula 0 (g.circuit n) b) d)
  exact not_lt_of_ge ((proofLength_le _ hπ'').trans hπ''_bd)
    (hN n ((le_max_left N 2).trans hn_ge) b hb_not)

/-! ### Uniform logarithmic-seed enumeration for Nisan–Wigderson range avoidance -/

/-- Little-endian `r`-bit binary representation of `t : ℕ`. -/
def natToBitsLen (r t : ℕ) : List Bool :=
  (List.range r).map t.testBit

/-- Exact length of `natToBitsLen r t`. -/
@[simp]
theorem length_natToBitsLen (r t : ℕ) : (natToBitsLen r t).length = r := by
  simp [natToBitsLen]

/-- Convert a finite bitstring `z : BitString r` to its little-endian natural number `< 2 ^ r`. -/
def bitStringToNat : {r : ℕ} → BitString r → ℕ
  | 0, _ => 0
  | _ + 1, z => (if z 0 then 1 else 0) + 2 * bitStringToNat (fun i => z i.succ)

/-- `bitStringToNat z < 2 ^ r`. -/
theorem bitStringToNat_lt {r : ℕ} (z : BitString r) : bitStringToNat z < 2 ^ r := by
  induction r with
  | zero => simp [bitStringToNat]
  | succ r ih =>
    have := ih (fun i => z i.succ)
    rw [bitStringToNat, pow_succ]
    cases z 0 <;> simp only [↓reduceIte, Bool.false_eq_true] <;> omega

/-- Testing bit `i < r` of `bitStringToNat z` recovers `z ⟨i, hi⟩`. -/
@[simp]
theorem testBit_bitStringToNat {r : ℕ} (z : BitString r) (i : Fin r) :
    (bitStringToNat z).testBit i.val = z i := by
  induction r with
  | zero => exact i.elim0
  | succ r ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · dsimp only [bitStringToNat, Fin.val_zero]
      cases z 0 <;> simp [Nat.testBit_zero]
    · dsimp only [bitStringToNat, Fin.val_succ]
      rw [Nat.testBit_add_one]
      have hdiv : ((if z 0 then 1 else 0) + 2 * bitStringToNat (fun k => z k.succ)) / 2 =
          bitStringToNat (fun k => z k.succ) := by
        cases z 0 <;> simp only [↓reduceIte, Bool.false_eq_true] <;> omega
      rw [hdiv, ih]

/-- `natToBitsLen r (bitStringToNat z) = List.ofFn z`. -/
@[simp]
theorem natToBitsLen_bitStringToNat {r : ℕ} (z : BitString r) :
    natToBitsLen r (bitStringToNat z) = List.ofFn z :=
  List.ext_getElem (by simp) fun i h₁ h₂ => by
    simp only [List.length_ofFn] at h₂
    simp [natToBitsLen, testBit_bitStringToNat z ⟨i, h₂⟩]

/-- Two natural numbers `< 2 ^ r` with identical first `r` bits are equal. -/
theorem eq_of_lt_two_pow_of_testBit_eq {r a b : ℕ} (ha : a < 2 ^ r) (hb : b < 2 ^ r)
    (h : ∀ i : Fin r, a.testBit i.val = b.testBit i.val) : a = b := by
  apply Nat.eq_of_testBit_eq; intro k
  by_cases hk : k < r
  · exact h ⟨k, hk⟩
  · have h2 : 2 ^ r ≤ 2 ^ k := Nat.pow_le_pow_right two_pos (by omega)
    rw [Nat.testBit_lt_two_pow (ha.trans_le h2), Nat.testBit_lt_two_pow (hb.trans_le h2)]

/-- `natToBitsLen` is computable in polynomial time (with length in unary and value in binary). -/
theorem computableInPolyTime_natToBitsLen :
    ComputableInPolyTime (fun p : ℕ × ℕ => natToBitsLen p.1 p.2)
      (encPair encUnary encNat) encBits := by
  have htb : ComputableInPolyTime (fun q : ℕ × ℕ => q.1.testBit q.2)
      (encPair encNat encUnary) encBool :=
    (binary_pos.comp (binary_and'
      (binary_shiftRight' (fst encNat encUnary) (unary_to_binary.comp (snd encNat encUnary)))
      (const 1))).of_enc_eq fun ⟨t, i⟩ => by
        congr 1; dsimp only [Function.comp_apply]
        simp only [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow,
          Nat.testBit_eq_decide_div_mod_eq]
        have : (t / 2 ^ i) % 2 < 2 := Nat.mod_lt _ two_pos
        by_cases h : (t / 2 ^ i) % 2 = 1 <;>
          simp [h, show 0 < (t / 2 ^ i) % 2 ↔ (t / 2 ^ i) % 2 = 1 by omega]
  let E := encPair encUnary encNat
  exact listToBits.comp (mapWithInput (range.comp (fst encUnary encNat))
    (htb.comp (((snd encUnary encNat).comp (fst E encUnary)).prod (snd E encUnary))))

/-- Canonical polynomial-size list of `(c * ⌊log₂ M⌋)`-bit seed strings covering every
`z : BitString (c * Nat.log 2 M)` when `1 ≤ M`. -/
def allSeedStrings (c M : ℕ) : List (List Bool) :=
  (List.range (M ^ c)).map (natToBitsLen (c * Nat.log 2 M))

/-- Length of `allSeedStrings c M` is `M ^ c`. -/
@[simp]
theorem length_allSeedStrings (c M : ℕ) : (allSeedStrings c M).length = M ^ c := by
  simp [allSeedStrings]

/-- Every `z : BitString (c * Nat.log 2 M)` appears as `List.ofFn z` in `allSeedStrings c M`
whenever `1 ≤ M`. -/
theorem ofFn_mem_allSeedStrings (c : ℕ) {M : ℕ} (hM : 1 ≤ M)
    (z : BitString (c * Nat.log 2 M)) : List.ofFn z ∈ allSeedStrings c M := by
  refine List.mem_map.2 ⟨bitStringToNat z, List.mem_range.2 ?_, natToBitsLen_bitStringToNat z⟩
  calc bitStringToNat z < 2 ^ (c * Nat.log 2 M) := bitStringToNat_lt z
    _ = (2 ^ Nat.log 2 M) ^ c := by rw [mul_comm, pow_mul]
    _ ≤ M ^ c := Nat.pow_le_pow_left (Nat.pow_log_le_self 2 (by omega)) c

/-- `M ↦ allSeedStrings c M` is computable in uniform polynomial time from `M` in unary. -/
theorem computableInPolyTime_allSeedStrings (c : ℕ) :
    ComputableInPolyTime (allSeedStrings c) encUnary (encList encBits) := by
  have hlog : ComputableInPolyTime (fun M : ℕ => c * Nat.log 2 M) encUnary encUnary :=
    unary_mul' (const c) (binary_log_two.comp unary_to_binary)
  refine mapWithInput (range.comp (unary_pow c)) ?_
  exact computableInPolyTime_natToBitsLen.comp
    ((hlog.comp (fst encUnary encUnary)).prod (unary_to_binary.comp (snd encUnary encUnary)))

/-! ### Uniform polynomial-time generators and failure of strong FDP -/

/-- A **uniform polynomial-time stretching generator** with strictly increasing output length
`m(n) > n`: specified by uniform polynomial-time `RawGate` circuit descriptions mapping `n` input
bits to `m(n)` output bits. -/
structure UniformPTimeGenerator (m : ℕ → ℕ) where
  /-- Strict stretching `n < m(n)` at every input length. -/
  stretch : ∀ n, n < m n
  /-- Strictly increasing output length `m`. -/
  m_mono : StrictMono m
  /-- `m` is computable in unary polynomial time. -/
  m_poly : ComputableInPolyTime m encUnary encUnary
  /-- Uniform gate list for input length `n`. -/
  gates : ℕ → List RawGate
  /-- Uniform output wire list for input length `n`. -/
  outs : ℕ → List ℕ
  /-- `gates` is computable in uniform polynomial time from unary `n`. -/
  gates_poly : ComputableInPolyTime gates encUnary (encList encRawGate)
  /-- `outs` is computable in uniform polynomial time from unary `n`. -/
  outs_poly : ComputableInPolyTime outs encUnary (encList encUnary)
  /-- Exact output count `(outs n).length = m n`. -/
  length_outs : ∀ n, (outs n).length = m n
  /-- Every output wire index is in bounds `< n + (gates n).length`. -/
  outs_lt : ∀ n (j : Fin (outs n).length), (outs n)[j.val] < n + (gates n).length

/-- Cast the output count of a `Circuit` along an equality `m₁ = m₂`. -/
@[expose] def circuitCastOut {n m₁ m₂ : ℕ} (h : m₁ = m₂) (c : Circuit signature n m₁) :
    Circuit signature n m₂ where
  size := c.size
  program := c.program
  outputs j := c.outputs (j.cast h.symm)

/-- `circuitCastOut` preserves gate count. -/
@[simp]
theorem size_circuitCastOut {n m₁ m₂ : ℕ} (h : m₁ = m₂) (c : Circuit signature n m₁) :
    (circuitCastOut h c).size = c.size := rfl

/-- Evaluating `circuitCastOut` reindexes the output vector along `h.symm`. -/
@[simp]
theorem eval_circuitCastOut {n m₁ m₂ : ℕ} (h : m₁ = m₂) (c : Circuit signature n m₁)
    (x : BitString n) (j : Fin m₂) :
    (circuitCastOut h c).eval interpretation x j = c.eval interpretation x (j.cast h.symm) := rfl

/-- `tauFormulaWith` of `circuitCastOut` reindexes the target bitstring along `h`. -/
@[simp]
theorem tauFormulaWith_circuitCastOut {n m₁ m₂ : ℕ} (h : m₁ = m₂) (c : Circuit signature n m₁)
    (wAtom : Wire n c.size → ℕ) (b : BitString m₂) :
    tauFormulaWith (circuitCastOut h c) wAtom b =
      tauFormulaWith c wAtom (fun i => b (i.cast h)) := by
  subst h; rfl

/-- Underlying `n`-input De Morgan circuit of a `UniformPTimeGenerator`. -/
@[expose] def UniformPTimeGenerator.circuit {m : ℕ → ℕ} (g : UniformPTimeGenerator m) (n : ℕ) :
    Circuit signature n (m n) :=
  if hn : 0 < n then
    circuitCastOut (g.length_outs n) (buildRawCircuit n hn (g.gates n) (g.outs n))
  else
    { size := 1
      program := Program.empty.gate ⟨.const false, Fin.elim0⟩
      outputs := fun _ => .gate 0 }

/-- Every `UniformPTimeGenerator m` induces a `PPolyGenerator m`. -/
@[expose] def UniformPTimeGenerator.toPPolyGenerator {m : ℕ → ℕ} (g : UniformPTimeGenerator m) :
    PPolyGenerator m where
  circuit := g.circuit
  stretch := g.stretch
  size_poly := by
    obtain ⟨c₀, d₀, hbd⟩ := exists_output_length_le g.gates_poly
    have hlist_len : ∀ l : List RawGate, l.length ≤ (encList encRawGate l).length := by
      intro l; induction l with
      | nil => simp
      | cons _ _ ih =>
        simp only [encList_cons, List.length_cons, List.length_append, length_frame]; omega
    let p : Polynomial ℕ := Polynomial.C (c₀ + 1) * (Polynomial.X + Polynomial.C 1) ^ d₀
    refine ⟨p, fun n => ?_⟩
    have hp1 : 1 ≤ p.eval (m n) := by
      simp only [p, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
        Polynomial.eval_C, Polynomial.eval_X]
      exact Nat.mul_pos (by omega) (Nat.pow_pos (by omega))
    dsimp only [UniformPTimeGenerator.circuit]
    split_ifs with hn
    · simp only [size_circuitCastOut, size_buildRawCircuit]
      have h1 : (g.gates n).length ≤ c₀ * (n + 1) ^ d₀ :=
        (hlist_len _).trans ((hbd n).trans_eq (by simp [encUnary_apply]))
      have h2 : n ≤ m n := (g.stretch n).le
      simp only [p, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
        Polynomial.eval_C, Polynomial.eval_X]
      exact h1.trans (Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) d₀))
    · exact hp1

/-- First-order evaluation map `(n, xs) ↦ g_n(xs)` of a `UniformPTimeGenerator`. -/
def UniformPTimeGenerator.evalList {m : ℕ → ℕ} (g : UniformPTimeGenerator m)
    (p : ℕ × List Bool) : List Bool :=
  if p.1 = 0 then List.replicate (m 0) false
  else
    let vals := evalRawGates p.2 (g.gates p.1)
    (List.range (m p.1)).map fun j => vals.getD ((g.outs p.1).getD j 0) false

/-- `g.evalList` agrees with `g.toPPolyGenerator.eval n` on every `x : BitString n`. -/
theorem UniformPTimeGenerator.evalList_ofFn {m : ℕ → ℕ} (g : UniformPTimeGenerator m) (n : ℕ)
    (x : BitString n) :
    g.evalList (n, List.ofFn x) = List.ofFn (g.toPPolyGenerator.eval n x) := by
  rw [← g.toPPolyGenerator.eval_circuit]
  dsimp only [evalList, toPPolyGenerator, circuit]
  by_cases hn : n = 0
  · subst hn
    refine List.ext_getElem (by simp) fun j _ h₂ => ?_
    simp only [List.length_ofFn] at h₂
    simp only [List.getElem_ofFn, Circuit.eval, Program.trace, Function.comp_apply, Wire.elim]
    simpa [Line.eval, interpretation_const] using
      (Program.eval_gate_last (Program.empty : Program signature 0 0) ⟨.const false, Fin.elim0⟩
        interpretation x).symm
  · have hpos : 0 < n := by omega
    simp only [hn, ↓reduceIte, hpos, dite_true]
    refine List.ext_getElem (by simp) fun j _ h₂ => ?_
    simp only [List.length_ofFn] at h₂
    have hjo : j < (g.outs n).length := by rw [g.length_outs]; exact h₂
    have hgd : (g.outs n).getD j 0 = (g.outs n)[j] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjo, Option.getD_some]
    rw [List.getElem_map, List.getElem_range, hgd, List.getElem_ofFn, eval_circuitCastOut]
    exact (eval_buildRawCircuit n hpos (g.gates n) (g.outs n) (g.outs_lt n) x ⟨j, hjo⟩).symm

/-- Exact output length of `g.evalList`. -/
@[simp]
theorem UniformPTimeGenerator.length_evalList {m : ℕ → ℕ} (g : UniformPTimeGenerator m)
    (n : ℕ) (xs : List Bool) : (g.evalList (n, xs)).length = m n := by
  by_cases hn : n = 0 <;> simp [evalList, hn]

/-- `g.evalList` is computable in uniform polynomial time. -/
theorem UniformPTimeGenerator.computableInPolyTime_evalList {m : ℕ → ℕ}
    (g : UniformPTimeGenerator m) :
    ComputableInPolyTime g.evalList (encPair encUnary encBits) encBits := by
  let E := encPair encUnary encBits
  have hn := fst encUnary encBits
  have hxs := snd encUnary encBits
  have hvals := computableInPolyTime_evalRawGates.comp (hxs.prod (g.gates_poly.comp hn))
  have houts := g.outs_poly.comp hn
  have hbody : ComputableInPolyTime
      (fun p : ℕ × List Bool => (List.range (m p.1)).map fun j =>
        (evalRawGates p.2 (g.gates p.1)).getD ((g.outs p.1).getD j 0) false) E encBits :=
    listToBits.comp (mapWithInput (range.comp (g.m_poly.comp hn))
      (bitsGetDWithInput (hvals.comp (fst E encUnary))
        (listGetDWithInput (houts.comp (fst E encUnary)) (snd E encUnary) 0) false))
  exact (ite_decide (unary_beq hn (const 0))
    ((bitsReplicate false).comp (const (m 0))) hbody).of_enc_eq fun ⟨n, _⟩ => by
      dsimp only [evalList]; by_cases h : n = 0 <;> simp [h]

/-- Uniform first-order constructor for `tauFormula base (g.circuit n) b` when `1 ≤ n`. -/
def UniformPTimeGenerator.buildTau {m : ℕ → ℕ} (g : UniformPTimeGenerator m)
    (n base : ℕ) (bs : List Bool) : Formula :=
  let gs := g.gates n
  let atoms := (List.range (n + gs.length)).map (base + ·)
  buildTauFormulaRaw atoms n gs (g.outs n) bs

/-- For `1 ≤ n` and `b : BitString (m n)`, `g.buildTau n base (List.ofFn b)` equals
`tauFormula base (g.circuit n) b`. -/
theorem UniformPTimeGenerator.buildTau_eq {m : ℕ → ℕ} (g : UniformPTimeGenerator m) {n : ℕ}
    (hn : 1 ≤ n) (base : ℕ) (b : BitString (m n)) :
    g.buildTau n base (List.ofFn b) = tauFormula base (g.circuit n) b := by
  have hpos : 0 < n := by omega
  have hatoms : (List.range (n + (g.gates n).length)).map (base + ·) =
      (List.ofFn fun i : Fin n => stdWireAtom base n (g := (g.gates n).length) (.input i)) ++
      (List.ofFn fun k : Fin (g.gates n).length => stdWireAtom base n (.gate k)) :=
    List.ext_getElem (by simp) fun i h₁ _ => by
      simp only [List.length_map, List.length_range] at h₁
      rw [List.getElem_map, List.getElem_range]
      by_cases hin : i < n
      · rw [List.getElem_append_left (by simp [hin]), List.getElem_ofFn, stdWireAtom_input]
      · rw [List.getElem_append_right (by simp; omega)]; simp [stdWireAtom_gate]; omega
  let b' : BitString (g.outs n).length := fun j => b (j.cast (g.length_outs n))
  have hb' : List.ofFn b = List.ofFn b' :=
    List.ext_getElem (by simp [g.length_outs]) fun _ _ _ => by simp [b']
  dsimp only [buildTau, circuit]
  rw [dite_eq_left hpos, hatoms, hb',
    buildTauFormulaRaw_eq n hpos (g.gates n) (g.outs n) (stdWireAtom base n) b']
  exact (tauFormulaWith_circuitCastOut (g.length_outs n)
    (buildRawCircuit n hpos (g.gates n) (g.outs n)) (stdWireAtom base n) b).symm

/-- `g.buildTau` is computable in uniform polynomial time. -/
theorem UniformPTimeGenerator.computableInPolyTime_buildTau {m : ℕ → ℕ}
    (g : UniformPTimeGenerator m) :
    ComputableInPolyTime (fun p : ℕ × (ℕ × List Bool) => g.buildTau p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encNat encBits)) encFormula := by
  let E2 := encPair encNat encBits
  let E := encPair encUnary E2
  have hn := fst encUnary E2
  have hbase := (fst encNat encBits).comp (snd encUnary E2)
  have hbs := (snd encNat encBits).comp (snd encUnary E2)
  have hgs := g.gates_poly.comp hn
  have htot := unary_add' hn ((length encRawGate).comp hgs)
  have hatoms : ComputableInPolyTime
      (fun p : ℕ × (ℕ × List Bool) =>
        (List.range (p.1 + (g.gates p.1).length)).map (p.2.1 + ·))
      E (encList encNat) :=
    mapWithInput (range.comp htot)
      (binary_add' (hbase.comp (fst E encUnary)) (unary_to_binary.comp (snd E encUnary)))
  exact computableInPolyTime_tauFormulaRaw.comp
    (hatoms.prod (hn.prod (hgs.prod ((g.outs_poly.comp hn).prod hbs))))

/-- Union of all output slices `{0, 1}^{m(n)}` of a uniform generator `g`. -/
def UniformPTimeGenerator.outputSlices {m : ℕ → ℕ} (_g : UniformPTimeGenerator m) :
    Set (List Bool) :=
  {y : List Bool | ∃ n : ℕ, y.length = m n}

/-- Combined range `⋃ n, g_n({0, 1}^n) ⊆ {0, 1}^*` of a uniform generator `g`. -/
def UniformPTimeGenerator.fullRange {m : ℕ → ℕ} (g : UniformPTimeGenerator m) :
    Set (List Bool) :=
  {y : List Bool | ∃ (n : ℕ) (x : BitString n), List.ofFn (g.toPPolyGenerator.eval n x) = y}

/-- **Equivalence between universal proof-system hardness and `NP` range intersection**: a uniform
polynomial-time generator `g` is hard for every Cook–Reckhow propositional proof system iff its
range intersects every infinite `NP` subset of its output slices `⋃_n {0, 1}^{m(n)}`. -/
theorem UniformPTimeGenerator.forall_isHardFor_iff_np_inter {m : ℕ → ℕ}
    (g : UniformPTimeGenerator m) :
    (∀ P : PropProofSystem, IsHardFor g.toPPolyGenerator P) ↔
      ∀ A : Set (List Bool), A ∈ Complexity.NP encBits → A ⊆ g.outputSlices →
        A.Infinite → (A ∩ g.fullRange).Nonempty := by
  constructor
  · intro hhard A hA hsub hinf
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    obtain ⟨q, V, hV, hVspec⟩ := hA
    let certEnc := encSum encBits (encPair encUnary (encPair encBits encBits))
    let certDec : Decoder certEnc :=
      Decoder.sum Decoder.bits (Decoder.pair Decoder.unary (Decoder.pair Decoder.bits Decoder.bits))
    let evalR' (r : ℕ × (List Bool × List Bool)) : Formula :=
      if decide (1 ≤ r.1) && decide (r.2.1.length = m r.1) &&
          decide (r.2.2.length = q.eval r.2.1.length) && V r.2 then
        g.buildTau r.1 0 r.2.1
      else .imp .falsum .falsum
    have hevalR' : ComputableInPolyTime evalR'
        (encPair encUnary (encPair encBits encBits)) encFormula := by
      let ER2 := encPair encBits encBits
      let ER := encPair encUnary ER2
      have hn := fst encUnary ER2
      have hy := (fst encBits encBits).comp (snd encUnary ER2)
      have hw := (snd encBits encBits).comp (snd encUnary ER2)
      have hwbd := unary_beq (length_bits.comp hw) ((unary_eval q).comp (length_bits.comp hy))
      have hcond := bool_and'
        (bool_and'
          (bool_and' (unary_lt.comp ((const 0).prod hn))
            (unary_beq (length_bits.comp hy) (g.m_poly.comp hn)))
          hwbd)
        (hV.comp (snd encUnary ER2))
      exact (ite_decide hcond
        (g.computableInPolyTime_buildTau.comp (hn.prod ((const 0).prod hy)))
        (const (Proposition.imp .falsum .falsum : Formula))).of_enc_eq fun _ => rfl
    let P' : PropProofSystem :=
      { toFun := fun π => Sum.elim extendedFrege evalR' (certDec.decode π)
        computable := by
          obtain ⟨_, _, hD⟩ := certDec.computable
          let ES := encSum encBits (encPair encUnary (encPair encBits encBits))
          exact (sumElimWithInput (eg := ES) (ea := encBits)
            (eb := encPair encUnary (encPair encBits encBits))
            (left := fun _ x => extendedFrege x) (right := fun _ r => evalR' r)
            id' (extendedFrege.computable.comp (snd _ _)) (hevalR'.comp (snd _ _))).comp
            hD.computableInPolyTime
        range_eq := by
          refine Set.Subset.antisymm ?_ fun φ hφ => ?_
          · rintro _ ⟨π, rfl⟩
            dsimp only
            cases certDec.decode π with
            | inl π₀ => exact extendedFrege.mem π₀
            | inr r =>
              rcases r with ⟨n, y, w⟩
              dsimp only [Sum.elim_inr, evalR']
              split_ifs with hc
              · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
                rcases hc with ⟨⟨⟨hn1, hylen⟩, hwle⟩, hVw⟩
                have hyA : y ∈ A := (hVspec y).2 ⟨w, by simpa using hwle, hVw⟩
                let b : BitString (m n) := fun i => y[i.val]'(by omega)
                have hyb : List.ofFn b = y :=
                  List.ext_getElem (by simp [hylen]) fun _ _ _ => by simp [b]
                rw [← hyb, g.buildTau_eq hn1 0 b, tauFormula_mem_taut_iff]
                rintro ⟨x, hxb⟩
                exact Set.eq_empty_iff_forall_notMem.1 hempty y
                  ⟨hyA, n, x, (congrArg List.ofFn hxb).trans hyb⟩
              · exact fun _ => rfl
          · obtain ⟨π₀, rfl⟩ := extendedFrege.exists_eq hφ
            exact ⟨certEnc (.inl π₀), by
              change Sum.elim extendedFrege evalR' (certDec.decode (certEnc (.inl π₀))) = _
              rw [certDec.decode_enc]; rfl⟩ }
    obtain ⟨eq, heq1, hq_bd⟩ := exists_pow_bound_poly q
    let c : ℕ := 2 * eq + 4
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((isHardFor_iff_eventually _ P').1 (hhard P') c (by omega))
    let N₁ := max N 2
    have hAfin : (A ∩ {y : List Bool | y.length ≤ m N₁}).Finite := by
      have hbi : (⋃ k ∈ Iic (m N₁), {y : List Bool | y.length = k}).Finite :=
        (finite_toSet (Iic (m N₁))).biUnion fun k _ => by
          have heq_s : {y : List Bool | y.length = k} =
              Set.range (fun z : BitString k => List.ofFn z) := by
            ext y; refine ⟨fun (hy : y.length = k) => ⟨fun i => y[i.val]'(by omega),
              List.ext_getElem (by simp [hy]) fun _ _ _ => by simp⟩, ?_⟩
            rintro ⟨z, rfl⟩; exact List.length_ofFn
          rw [heq_s]; exact Set.finite_range _
      exact hbi.subset fun y ⟨_, hy⟩ => Set.mem_iUnion₂.2 ⟨y.length, mem_Iic.2 hy, rfl⟩
    obtain ⟨y, hyA, hy_gt⟩ := (hinf.sdiff hAfin).nonempty
    obtain ⟨n, hylen⟩ := hsub hyA
    have hn_gt : N₁ < n := by
      by_contra hle
      exact hy_gt ⟨hyA, hylen.le.trans (g.m_mono.monotone (le_of_not_gt hle))⟩
    have hn1 : 1 ≤ n := by dsimp only [N₁] at hn_gt; omega
    have hmn2 : 2 ≤ m n := by have := g.stretch n; dsimp only [N₁] at hn_gt; omega
    obtain ⟨w, hwlen, hVw⟩ := (hVspec y).1 hyA
    simp only [encBits_apply] at hwlen
    let b : BitString (m n) := fun i => y[i.val]'(by omega)
    have hyb : List.ofFn b = y :=
      List.ext_getElem (by simp [hylen]) fun _ _ _ => by simp [b]
    have hb_not : b ∉ Set.range (g.toPPolyGenerator.eval n) := by
      rintro ⟨x, hxb⟩
      exact Set.eq_empty_iff_forall_notMem.1 hempty y
        ⟨hyA, n, x, (congrArg List.ofFn hxb).trans hyb⟩
    let π := certEnc (.inr (n, (y, w)))
    have hPπ : P' π = tauFormula 0 (g.circuit n) b := by
      change Sum.elim extendedFrege evalR' (certDec.decode π) = _
      rw [certDec.decode_enc]
      dsimp only [Sum.elim_inr, evalR']
      rw [ite_eq_left (by simp [hn1, hylen, hwlen, hVw]), ← hyb, g.buildTau_eq hn1 0 b]
    have hπ_le : π.length ≤ (encFormula (tauFormula 0 (g.circuit n) b)).length ^ c := by
      have h1 : π.length ≤ 4 * m n + 2 * (m n + 2) ^ eq + 16 := by
        have hnm : n ≤ m n := (g.stretch n).le
        have hwl : w.length ≤ (m n + 2) ^ eq := by rw [hwlen, hylen]; exact hq_bd (m n)
        simp only [π, certEnc, encSum_inr, List.length_cons, length_encPair,
          encUnary_apply, List.length_replicate, encBits_apply, hylen]
        omega
      have h2 : m n + 2 ≤ (m n) ^ 2 := by nlinarith
      have h3 : (m n + 2) ^ eq ≤ (m n) ^ (2 * eq) :=
        (Nat.pow_le_pow_left h2 eq).trans_eq (pow_mul (m n) 2 eq).symm
      have h4 : 16 ≤ (m n) ^ 4 :=
        (show 16 = 2 ^ 4 by norm_num) ▸ Nat.pow_le_pow_left hmn2 4
      have h5 : m n ≤ (m n) ^ (2 * eq) := Nat.le_self_pow (by omega) (m n)
      have h6 : π.length ≤ (m n) ^ c :=
        calc π.length ≤ 16 * (m n) ^ (2 * eq) := by
              have : 1 ≤ (m n) ^ (2 * eq) := Nat.pow_pos (by omega); omega
          _ ≤ (m n) ^ 4 * (m n) ^ (2 * eq) := Nat.mul_le_mul_right _ h4
          _ = (m n) ^ c := by rw [← pow_add]; dsimp only [c]; ring_nf
      exact h6.trans
        (Nat.pow_le_pow_left (output_le_length_encFormula_tauFormula 0 (g.circuit n) b) c)
    exact not_lt_of_ge ((proofLength_le P' hPπ).trans hπ_le)
      (hN n ((le_max_left N 2).trans hn_gt.le) b hb_not)
  · intro hNP P c hc
    obtain ⟨pg, hpg⟩ := g.toPPolyGenerator.size_poly
    let pτ : Polynomial ℕ :=
      (Polynomial.C 20 * (Polynomial.C 2 * Polynomial.X + pg + Polynomial.C 12) ^ 2) ^ c
    let q : Polynomial ℕ := pτ + Polynomial.C 1
    let findN (y : List Bool) : Option ℕ :=
      (List.range y.length).find? fun n => decide (1 ≤ n) && (m n == y.length)
    let firstTrue (u : List Bool) : ℕ :=
      (((List.range u.length).find? fun i => u.getD i false).getD u.length) + 1
    let unpad (u : List Bool) : List Bool := u.drop (firstTrue u)
    let V (p : List Bool × List Bool) : Bool :=
      match findN p.1 with
      | none => false
      | some n =>
        let π := unpad p.2
        decide (P π = g.buildTau n 0 p.1)
    have hV : ComputableInPolyTime V (encPair encBits encBits) encBool := by
      let EP := encPair encBits encBits
      have hy := fst encBits encBits
      have hu := snd encBits encBits
      have hfindN : ComputableInPolyTime (fun p : List Bool × List Bool => findN p.1)
          EP (encOption encUnary) := by
        refine findWithInput (range.comp (length_bits.comp hy)) ?_
        have hn := snd EP encUnary
        exact (bool_and' (unary_lt.comp ((const 0).prod hn))
          (unary_beq (g.m_poly.comp hn)
            ((length_bits.comp hy).comp (fst EP encUnary)))).of_enc_eq fun q => by
          have : decide (0 < q.2) = decide (1 ≤ q.2) := by
            by_cases h : 1 ≤ q.2 <;> simp [h, show 0 < q.2 ↔ 1 ≤ q.2 by omega]
          dsimp only [Function.comp_apply]; rw [this]
      have hft := unary_add'
        (optionGetDWithInput (findWithInput
          (test := fun (p : List Bool × List Bool) i => p.2.getD i false)
          (range.comp (length_bits.comp hu))
          ((bitsGetDWithInput (hu.comp (fst EP encUnary)) (snd EP encUnary) false).of_enc_eq
            fun _ => rfl))
          (length_bits.comp hu)) (const 1)
      have hπ := bitsDropWithInput hu hft
      exact (optionElimWithInput
        (body := fun (p : List Bool × List Bool) (n : ℕ) =>
          P (unpad p.2) == g.buildTau n 0 p.1)
        hfindN (const false)
        (ComputableInPolyTime.beq (P.computable.comp (hπ.comp (fst EP encUnary)))
          (g.computableInPolyTime_buildTau.comp
            ((snd EP encUnary).prod
              ((const 0).prod (hy.comp (fst EP encUnary))))))).of_enc_eq fun p => by
        dsimp only [V, Function.comp_apply]
        cases findN p.1 with
        | none => rfl
        | some n => by_cases h : P (unpad p.2) = g.buildTau n 0 p.1 <;> simp [h]
    have hunpad (k : ℕ) (w : List Bool) :
        unpad (List.replicate k false ++ (true :: w)) = w := by
      set u := List.replicate k false ++ (true :: w)
      have hk_lt : k < u.length := by simp [u]
      have hf : ((List.range u.length).find? fun i => u.getD i false) = some k := by
        rw [List.find?_eq_some_iff_append]
        refine ⟨by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk_lt, Option.getD_some,
            List.getElem_append_right (by simp)]; simp,
          List.range k, (List.range u.length).drop (k + 1), ?_, fun j hj => ?_⟩
        · refine List.ext_getElem (by simp; omega) fun j h₁ _ => ?_
          rw [List.getElem_range]
          by_cases hjk : j < k
          · rw [List.getElem_append_left (by simp [hjk]), List.getElem_range]
          · rw [List.getElem_append_right (by simp; omega)]
            by_cases hje : j = k
            · subst hje; simp
            · have hs : j - (List.range k).length = (j - k - 1) + 1 := by simp; omega
              simp only [hs, List.getElem_cons_succ, List.getElem_drop, List.getElem_range]; omega
        · have hjk : j < k := List.mem_range.1 hj
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some,
            List.getElem_append_left (by simp [hjk]), List.getElem_replicate]; simp
      simp only [unpad, firstTrue, hf, Option.getD_some]
      rw [show u = (List.replicate k false ++ [true]) ++ w by simp [u],
        List.drop_left' (by simp)]
    let A : Set (List Bool) :=
      {y | ∃ u : List Bool, u.length = q.eval y.length ∧ V (y, u) = true}
    have hA_NP : A ∈ Complexity.NP encBits :=
      ⟨q, V, hV, fun y => by simp only [A, Set.mem_ofPred_eq, encBits_apply]⟩
    have hA_sub : A ⊆ g.outputSlices := by
      rintro y ⟨u, -, hVu⟩
      dsimp only [V] at hVu
      cases hf : findN y with
      | none => rw [hf] at hVu; cases hVu
      | some n =>
        have hpred := List.find?_some hf
        simp only [Bool.and_eq_true, beq_iff_eq] at hpred
        exact ⟨n, hpred.2.symm⟩
    have hA_disj : A ∩ g.fullRange = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 ?_
      rintro y ⟨⟨u, -, hVu⟩, ⟨n', x, hx⟩⟩
      dsimp only [V] at hVu
      cases hf : findN y with
      | none => rw [hf] at hVu; cases hVu
      | some n =>
        rw [hf, decide_eq_true_eq] at hVu
        have hpred := List.find?_some hf
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hpred
        have hnn : n' = n := g.m_mono.injective (by
          have := congrArg List.length hx; rw [List.length_ofFn] at this; omega)
        subst hnn
        rw [← hx, g.buildTau_eq hpred.1 0] at hVu
        exact (tauFormula_mem_taut_iff 0 (g.circuit n') _).1 (hVu ▸ P.mem _) ⟨x, rfl⟩
    have hA_fin : A.Finite := by
      by_contra hinf
      obtain ⟨y, hy⟩ := hNP A hA_NP hA_sub hinf
      exact Set.eq_empty_iff_forall_notMem.1 hA_disj y hy
    let S0 : Set (Σ n : ℕ, BitString (m n)) := Sigma.mk 0 '' Set.univ
    let toList (p : Σ n : ℕ, BitString (m n)) : List Bool := List.ofFn p.2
    have hto_inj : Function.Injective toList := by
      rintro ⟨n₁, b₁⟩ ⟨n₂, b₂⟩ h
      have hn : n₁ = n₂ := g.m_mono.injective (by
        have := congrArg List.length h; simpa [toList] using this)
      subst hn
      exact Sigma.ext rfl (heq_of_eq (funext fun i => by
        have := congrArg (fun l => l[i.val]?) h; simpa [toList] using this))
    refine (S0.finite_coe_iff.1 (by
      have := Set.finite_univ.image (Sigma.mk (β := fun n => BitString (m n)) 0)
      exact this.to_subtype) |>.union (hA_fin.preimage hto_inj.injOn)).subset ?_
    rintro ⟨n, b⟩ ⟨hb, hle⟩
    by_cases hn0 : n = 0
    · subst hn0; exact Or.inl ⟨b, Set.mem_univ b, rfl⟩
    · refine Or.inr ?_
      have hn1 : 1 ≤ n := by omega
      have htaut : tauFormula 0 (g.circuit n) b ∈ TAUT :=
        (tauFormula_mem_taut_iff 0 _ b).2 hb
      obtain ⟨π, hπ, hπlen⟩ := (proofLength_le_iff P htaut).1 hle
      have hπ_pτ : π.length ≤ pτ.eval (m n) := by
        refine hπlen.trans ?_
        simp only [pτ, Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_add,
          Polynomial.eval_C, Polynomial.eval_X]
        refine Nat.pow_le_pow_left
          ((length_encFormula_tauFormula_zero_le (g.circuit n) b).trans ?_) c
        have h1 : n ≤ m n := (g.stretch n).le
        have h2 : (g.circuit n).size ≤ pg.eval (m n) := hpg n
        exact Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left (by omega) 2)
      set y := List.ofFn b
      have hfN : findN y = some n := by
        dsimp only [findN]; rw [List.find?_eq_some_iff_append]
        have hnm : n < y.length := by simp [y, g.stretch n]
        refine ⟨by simp [y, hn1], List.range n, (List.range y.length).drop (n + 1), ?_,
          fun k hk => ?_⟩
        · refine List.ext_getElem (by simp; omega) fun j h₁ _ => ?_
          rw [List.getElem_range]
          by_cases hjn : j < n
          · rw [List.getElem_append_left (by simp [hjn]), List.getElem_range]
          · rw [List.getElem_append_right (by simp; omega)]
            by_cases hje : j = n
            · subst hje; simp
            · have hs : j - (List.range n).length = (j - n - 1) + 1 := by simp; omega
              simp only [hs, List.getElem_cons_succ, List.getElem_drop, List.getElem_range]; omega
        · have hkn : k < n := List.mem_range.1 hk
          have hne : m k ≠ m n := (g.m_mono hkn).ne
          simp [y, hne]
      let u := List.replicate (pτ.eval (m n) - π.length) false ++ (true :: π)
      change y ∈ A
      refine ⟨u, ?_, ?_⟩
      · have hyl : y.length = m n := List.length_ofFn
        simp only [u, hyl, q, Polynomial.eval_add, Polynomial.eval_C, List.length_append,
          List.length_replicate, List.length_cons]; omega
      · simp only [V, hfN, u, hunpad, y, g.buildTau_eq hn1 0 b, decide_eq_true_eq]
        exact hπ

/-- **Proof complexity generator conjecture (uniform polynomial-time form)**: there exists a uniform
polynomial-time stretching generator simultaneously hard for every Cook–Reckhow propositional proof
system. -/
@[expose]
def UniformHardGeneratorConjecture : Prop :=
  ∃ (m : ℕ → ℕ) (g : UniformPTimeGenerator m),
    ∀ P : PropProofSystem, IsHardFor g.toPPolyGenerator P

/-- `UniformHardGeneratorConjecture` implies `HardGeneratorConjecture`. -/
theorem UniformHardGeneratorConjecture.toHardGeneratorConjecture
    (h : UniformHardGeneratorConjecture) : HardGeneratorConjecture :=
  let ⟨m, g, hg⟩ := h
  ⟨m, g.toPPolyGenerator, hg⟩

/-- **Krajíček's theorem on the failure of the strong feasible disjunction property from a uniform
hard generator**: assuming `ENPHypothesis` and
`UniformHardGeneratorConjecture`, there exists a strong Cook–Reckhow propositional proof system
`Q` such that no Cook–Reckhow propositional proof system `P` simulating `Q` has
`HasStrongFDPPoly` (and in particular none has `HasStrongFDP`). -/
theorem exists_pps_not_hasStrongFDP_of_enp_and_uniformHard
    (hENP : ENPHypothesis) (hConj : UniformHardGeneratorConjecture) :
    ∃ Q : PropProofSystem, IsStrongPPS Q ∧
      ∀ P : PropProofSystem, P.Simulates Q → ¬ HasStrongFDPPoly P := by
  obtain ⟨m, g, hg_hard⟩ := hConj
  obtain ⟨c, H, hc1, hH_poly, hH_len, hH_avoid⟩ :=
    exists_polyTime_avoid_polyStretch_of_enp hENP g.m_poly g.m_mono g.stretch
      g.computableInPolyTime_evalList (fun n x => g.length_evalList n (List.ofFn x))
  let stride (n : ℕ) : ℕ := n + (g.gates n).length
  let extra (n : ℕ) : Formula :=
    let seeds := allSeedStrings c (m n)
    bigOr ((List.range seeds.length).map fun idx =>
      g.buildTau n (idx * stride n) (H (n, seeds.getD idx [])))
  have hextra_eq (n : ℕ) (hn1 : 1 ≤ n) :
      extra n = tauDisjunction (g.circuit n)
        ((allSeedStrings c (m n)).map fun s => BitString.ofList (m n) (H (n, s))) := by
    have hpos : 0 < n := by omega
    have hcsz : (g.circuit n).size = (g.gates n).length := by
      simp [UniformPTimeGenerator.circuit, hpos]
    dsimp only [extra, tauDisjunction, tauDisjuncts]; congr 1
    refine List.ext_getElem (by simp) fun idx h₁ _ => ?_
    simp only [List.length_map, List.length_range] at h₁
    simp only [List.getElem_map, List.getElem_range, List.getElem_mapIdx]
    have hsd : (allSeedStrings c (m n)).getD idx [] = (allSeedStrings c (m n))[idx] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁, Option.getD_some]
    set y := H (n, (allSeedStrings c (m n))[idx])
    have hof : List.ofFn (BitString.ofList (m n) y) = y := by
      have hyl : y.length = m n := hH_len n _
      rw [BitString.ofFn_ofList_eq_take, List.take_append_of_le_length (by omega),
        List.take_of_length_le (by omega)]
    rw [hsd]
    change g.buildTau n (idx * stride n) y =
      tauFormula (idx * (n + (g.circuit n).size)) (g.circuit n) (BitString.ofList (m n) y)
    have htau := g.buildTau_eq hn1 (idx * stride n) (BitString.ofList (m n) y)
    rw [hof] at htau
    rw [htau, hcsz]
  have hextra_taut (n : ℕ) (hn1 : 1 ≤ n) : extra n ∈ TAUT := by
    rw [hextra_eq n hn1]
    have hmn1 : 1 ≤ m n := by have := g.stretch n; omega
    obtain ⟨z, hz⟩ := hH_avoid n hn1
    have hz_mem : List.ofFn z ∈ allSeedStrings c (m n) := ofFn_mem_allSeedStrings c hmn1 z
    let bz : BitString (m n) := BitString.ofList (m n) (H (n, List.ofFn z))
    rw [tauDisjunction_mem_taut_iff]
    refine ⟨bz, List.mem_map.2 ⟨List.ofFn z, hz_mem, rfl⟩, ?_⟩
    rintro ⟨x, hx⟩
    have hof : List.ofFn bz = H (n, List.ofFn z) := by
      have hyl := hH_len n (List.ofFn z)
      rw [BitString.ofFn_ofList_eq_take, List.take_append_of_le_length (by omega),
        List.take_of_length_le (by omega)]
    exact hz x (hof.symm.trans ((congrArg List.ofFn hx.symm).trans (g.evalList_ofFn n x).symm))
  have hextra_len_ge (n : ℕ) (hn1 : 1 ≤ n) : n ≤ (encFormula (extra n)).length := by
    rw [hextra_eq n hn1, tauDisjunction]
    have hmn1 : 1 ≤ m n := by have := g.stretch n; omega
    have hpos : 1 ≤ (m n) ^ c := Nat.pow_pos hmn1
    set djs := tauDisjuncts (g.circuit n)
      ((allSeedStrings c (m n)).map fun s => BitString.ofList (m n) (H (n, s)))
    have hdjl : djs.length = (m n) ^ c := by simp [djs, tauDisjuncts]
    cases hd : djs with
    | nil => rw [hd] at hdjl; simp at hdjl; omega
    | cons φ rest =>
      have hφ_eq : φ = djs[0]'(by omega) := by simp [hd]
      have hφ_len : m n ≤ (encFormula φ).length := by
        rw [hφ_eq]; simp only [djs, tauDisjuncts, List.getElem_mapIdx]
        exact output_le_length_encFormula_tauFormula _ _ _
      have hge : (encFormula φ).length ≤ (encFormula (bigOr (φ :: rest))).length := by
        cases rest with
        | nil => exact le_rfl
        | cons ψ tail => simp only [bigOr_cons_cons, encFormula_or, List.length_append]; omega
      exact (g.stretch n).le.trans (hφ_len.trans hge)
  have hextra_poly : ComputableInPolyTime extra encUnary encFormula := by
    have hseeds := (computableInPolyTime_allSeedStrings c).comp g.m_poly
    have hstr := unary_add' id' ((length encRawGate).comp g.gates_poly)
    refine computableInPolyTime_bigOr.comp
      (mapWithInput (range.comp ((length encBits).comp hseeds)) ?_)
    let EI := encPair encUnary encUnary
    have hn := fst encUnary encUnary
    have hidx := snd encUnary encUnary
    have hbase := unary_to_binary.comp (unary_mul' hidx (hstr.comp hn))
    have hsd := listGetDWithInput (hseeds.comp hn) hidx []
    exact g.computableInPolyTime_buildTau.comp (hn.prod (hbase.prod (hH_poly.comp (hn.prod hsd))))
  let A : Set Formula := {φ | ∃ n : ℕ, 1 ≤ n ∧ extra n = φ}
  have hA_sub : A ⊆ TAUT := by rintro _ ⟨n, hn1, rfl⟩; exact hextra_taut n hn1
  have hA_P : A ∈ Complexity.P encFormula := by
    rw [mem_P]
    let dec (φ : Formula) : Bool :=
      (List.range (encFormula φ).length).any fun k => decide (extra (k + 1) = φ)
    have hlen_f : ComputableInPolyTime (fun φ : Formula => (encFormula φ).length)
        encFormula encUnary := length_bits.comp (id'.of_enc_eq fun _ => rfl)
    have hdec : ComputableInPolyTime dec encFormula encBool :=
      anyWithInput (range.comp hlen_f)
        (ComputableInPolyTime.beq
          (hextra_poly.comp (unary_add' (snd encFormula encUnary) (const 1)))
          (fst encFormula encUnary))
    refine ⟨dec, hdec, fun φ => ?_⟩
    simp only [dec, List.any_eq_true, List.mem_range, decide_eq_true_eq, A, Set.mem_ofPred_eq]
    refine ⟨fun ⟨n, hn1, hφ⟩ => ?_, fun ⟨k, _, hk⟩ => ⟨k + 1, by omega, hk⟩⟩
    refine ⟨n - 1, ?_, by rwa [show n - 1 + 1 = n by omega]⟩
    have := hφ ▸ hextra_len_ge n hn1; omega
  let Q := extendedFregeWith A hA_P hA_sub
  refine ⟨Q, isStrongPPS_extendedFregeWith A hA_P hA_sub, fun P hsim hfdp => ?_⟩
  obtain ⟨psim, hpsim⟩ := hsim
  obtain ⟨cex, dex, hcex⟩ := exists_output_length_le hextra_poly
  let qQ : Polynomial ℕ :=
    Polynomial.C (4 * cex + 28) * (Polynomial.X + Polynomial.C 1) ^ dex
  obtain ⟨ed, hed1, hped⟩ := exists_pow_bound_poly (psim.comp qQ)
  have hproof_all (n : ℕ) (hn2 : 2 ≤ n) :
      ∃ πP : List Bool, P πP = extra n ∧ πP.length ≤ (m n) ^ (2 * ed) := by
    have hn1 : 1 ≤ n := by omega
    have hax := extendedFregeWith_extraAx_proof A hA_P hA_sub ⟨n, hn1, rfl⟩ []
    have hsub0 : (extra n).subst (listSubst []) = extra n := by
      have : listSubst [] = Proposition.atom := funext fun _ => rfl
      rw [this, subst_atom]
    rw [hsub0] at hax
    obtain ⟨πP, hπP, hπPlen⟩ := hpsim (encList encEFStep [.extraAx (extra n) []])
    refine ⟨πP, hπP.trans hax.1, ?_⟩
    have hQlen : (encList encEFStep [.extraAx (extra n) []]).length ≤ qQ.eval (m n) := by
      have h1 : (encFormula (extra n)).length ≤ cex * (n + 1) ^ dex :=
        (hcex n).trans_eq (by simp [encUnary_apply])
      have hnil : (encList (encPair encNat encFormula) []).length = 0 := by simp [encList_nil]
      rw [hnil] at hax
      have hnm : n ≤ m n := (g.stretch n).le
      have h2 : 4 * (cex * (n + 1) ^ dex) + 20 ≤
          (4 * cex + 28) * (m n + 1) ^ dex := by
        have hp : 1 ≤ (m n + 1) ^ dex := Nat.pow_pos (by omega)
        calc 4 * (cex * (n + 1) ^ dex) + 20
            ≤ 4 * cex * (m n + 1) ^ dex + 24 * (m n + 1) ^ dex :=
              Nat.add_le_add
                (by rw [mul_assoc]
                    exact Nat.mul_le_mul_left 4
                      (Nat.mul_le_mul_left cex (Nat.pow_le_pow_left (by omega) dex)))
                (by omega)
          _ ≤ (4 * cex + 28) * (m n + 1) ^ dex := by nlinarith
      simp only [qQ, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
        Polynomial.eval_C, Polynomial.eval_X]
      exact hax.2.trans ((Nat.add_le_add_right (Nat.mul_le_mul_left 4 h1) 20).trans h2)
    have hmn2 : 2 ≤ m n := by have := g.stretch n; omega
    have hsq : m n + 2 ≤ (m n) ^ 2 := by nlinarith
    calc πP.length ≤ psim.eval (qQ.eval (m n)) := hπPlen.trans (psim.eval_mono hQlen)
      _ = (psim.comp qQ).eval (m n) := Polynomial.eval_comp.symm
      _ ≤ (m n + 2) ^ ed := hped (m n)
      _ ≤ ((m n) ^ 2) ^ ed := Nat.pow_le_pow_left hsq ed
      _ = (m n) ^ (2 * ed) := (pow_mul (m n) 2 ed).symm
  have hfdp' : ∃ p : Polynomial ℕ, ∀ (αs : List Formula) (π : List Bool),
      αs ≠ [] → AreAtomDisjoint αs → P π = bigOr αs →
      ∃ α ∈ αs, ∃ π' : List Bool, P π' = α ∧ π'.length ≤ p.eval π.length := hfdp
  obtain ⟨pf, hpf⟩ := hfdp'
  obtain ⟨epf, hepf1, hpepf⟩ := exists_pow_bound_poly pf
  obtain ⟨pg, hpg⟩ := g.toPPolyGenerator.size_poly
  obtain ⟨epg, hepg1, hpepg⟩ := exists_pow_bound_poly pg
  let d_fin : ℕ := 4 * ed * epf + 2 * (c + epg) + 10
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((isHardFor_iff_eventually _ (closeUnderSubstFrege P)).1
      (hg_hard (closeUnderSubstFrege P)) d_fin (by dsimp only [d_fin]; omega))
  let n := max N 2
  have hn2 : 2 ≤ n := le_max_right N 2
  have hmn2 : 2 ≤ m n := by have := g.stretch n; omega
  obtain ⟨πP, hπP, hπPlen⟩ := hproof_all n hn2
  set bs := (allSeedStrings c (m n)).map fun s => BitString.ofList (m n) (H (n, s))
  rw [hextra_eq n (by omega), tauDisjunction] at hπP
  have hdne : tauDisjuncts (g.circuit n) bs ≠ [] := by
    intro h
    have : (m n) ^ c = 0 := by simpa [tauDisjuncts, bs] using congrArg List.length h
    exact absurd this (Nat.pow_pos (by omega)).ne'
  obtain ⟨α, hα, π', hπ', hπ'len⟩ := hpf _ πP hdne (areAtomDisjoint_tauDisjuncts _ bs) hπP
  obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.1 hα
  simp only [tauDisjuncts, List.length_mapIdx, List.getElem_mapIdx] at hidx hπ'
  set b := bs[idx]
  set base := idx * (n + (g.circuit n).size)
  have hb_not : b ∉ Set.range (g.toPPolyGenerator.eval n) :=
    (tauFormula_mem_taut_iff base (g.circuit n) b).1 (hπ' ▸ P.mem π')
  obtain ⟨π'', hπ'', hπ''len⟩ := closeUnderSubstFrege_shift P π' base
  rw [hπ', renameAtoms_sub_tauFormula] at hπ''
  have hπ'_bd : π'.length ≤ (m n) ^ (4 * ed * epf) := by
    have h1 : (m n) ^ (2 * ed) + 2 ≤ (m n) ^ (4 * ed) := by
      have : 2 ≤ (m n) ^ (2 * ed) := hmn2.trans (Nat.le_self_pow (by positivity) _)
      calc (m n) ^ (2 * ed) + 2 ≤ (m n) ^ (2 * ed) * (m n) ^ (2 * ed) := by nlinarith
        _ = (m n) ^ (4 * ed) := by rw [← pow_add]; ring_nf
    calc π'.length ≤ pf.eval ((m n) ^ (2 * ed)) := hπ'len.trans (pf.eval_mono hπPlen)
      _ ≤ ((m n) ^ (2 * ed) + 2) ^ epf := hpepf _
      _ ≤ ((m n) ^ (4 * ed)) ^ epf := Nat.pow_le_pow_left h1 epf
      _ = (m n) ^ (4 * ed * epf) := (pow_mul _ _ _).symm
  have hbase_bd : (encNat base).length ≤ (m n) ^ (2 * (c + epg) + 4) := by
    have hidx_le : idx ≤ (m n) ^ c := by
      have : bs.length = (m n) ^ c := by simp [bs]
      omega
    have hsz_le : n + (g.circuit n).size ≤ (m n) ^ (2 * epg + 2) := by
      have h1 : (g.circuit n).size ≤ (m n + 2) ^ epg := (hpg n).trans (hpepg (m n))
      have hsq : m n + 2 ≤ (m n) ^ 2 := by nlinarith
      have h2 : (m n + 2) ^ epg ≤ (m n) ^ (2 * epg) :=
        (Nat.pow_le_pow_left hsq epg).trans_eq (pow_mul _ _ _).symm
      have h3 : n ≤ (m n) ^ (2 * epg) :=
        (g.stretch n).le.trans (Nat.le_self_pow (by positivity) _)
      calc n + (g.circuit n).size ≤ 2 * (m n) ^ (2 * epg) := by omega
        _ ≤ (m n) ^ 2 * (m n) ^ (2 * epg) := Nat.mul_le_mul_right _ (by nlinarith)
        _ = (m n) ^ (2 * epg + 2) := by rw [← pow_add, add_comm]
    have hprod : base ≤ (m n) ^ (2 * (c + epg) + 4) :=
      calc base ≤ (m n) ^ c * (m n) ^ (2 * epg + 2) := Nat.mul_le_mul hidx_le hsz_le
        _ = (m n) ^ (c + (2 * epg + 2)) := (pow_add _ _ _).symm
        _ ≤ (m n) ^ (2 * (c + epg) + 4) := Nat.pow_le_pow_right (by omega) (by omega)
    exact (length_encNat_mono hprod).trans (length_encNat_le_self _)
  have hπ''_bd : π''.length ≤ (encFormula (tauFormula 0 (g.circuit n) b)).length ^ d_fin := by
    have h1 : π'.length ≤ (m n) ^ (d_fin - 4) :=
      hπ'_bd.trans (Nat.pow_le_pow_right (by omega) (by dsimp only [d_fin]; omega))
    have h2 : (encNat base).length ≤ (m n) ^ (d_fin - 4) :=
      hbase_bd.trans (Nat.pow_le_pow_right (by omega) (by dsimp only [d_fin]; omega))
    have h3 : 1 ≤ (m n) ^ (d_fin - 4) := Nat.pow_pos (by omega)
    have h4 : 48 ≤ (m n) ^ 6 :=
      (show 48 ≤ 2 ^ 6 by norm_num).trans (Nat.pow_le_pow_left hmn2 6)
    have h1' : π'.length ≤ (m n) ^ (d_fin - 6) :=
      hπ'_bd.trans (Nat.pow_le_pow_right (by omega) (by dsimp only [d_fin]; omega))
    have h2' : (encNat base).length ≤ (m n) ^ (d_fin - 6) :=
      hbase_bd.trans (Nat.pow_le_pow_right (by omega) (by dsimp only [d_fin]; omega))
    have h3' : 1 ≤ (m n) ^ (d_fin - 6) := Nat.pow_pos (by omega)
    have hsum : π''.length ≤ (m n) ^ d_fin :=
      calc π''.length ≤ 48 * (m n) ^ (d_fin - 6) := by linarith only [hπ''len, h1', h2', h3']
        _ ≤ (m n) ^ 6 * (m n) ^ (d_fin - 6) := Nat.mul_le_mul_right _ h4
        _ = (m n) ^ d_fin := by rw [← pow_add]; congr 1; dsimp only [d_fin]; omega
    exact hsum.trans
      (Nat.pow_le_pow_left (output_le_length_encFormula_tauFormula 0 (g.circuit n) b) d_fin)
  exact not_lt_of_ge ((proofLength_le _ hπ'').trans hπ''_bd) (hN n (le_max_left N 2) b hb_not)

end CslibFrontier.ProofComplexity
