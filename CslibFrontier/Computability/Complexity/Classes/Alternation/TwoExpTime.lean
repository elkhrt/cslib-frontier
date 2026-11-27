module

public import CslibFrontier.Computability.Complexity.Classes.Alternation
public import CslibFrontier.Computability.Complexity.Classes.Alternation.Space
public import CslibFrontier.Computability.Complexity.Classes.EXP
public import CslibFrontier.Computability.Complexity.Reduction

import CslibFrontier.Computability.Circuit.Boolean.Tableau.ValueGame
import CslibFrontier.Computability.Complexity.Classes.Alternation.DeterministicTime
import CslibFrontier.Computability.Complexity.Classes.TimeSpace.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.WordGame
import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.StreamFold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.NatPow
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.KernelOnWords
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimePrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Computability.Machines.Turing.MultiTape.Run
import CslibFrontier.Foundations.Data.Fin.Embedding
import Mathlib.Data.Set.Finite.List
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Double-exponential time and alternating exponential space

We define deterministic double-exponential time `Cslib.Complexity.TwoExpTime` (`2EXPTIME`),
alternating exponential space `Cslib.Complexity.AEXPSPACE`, and the associated polynomial-time
hardness and completeness notions, and prove the Chandra–Kozen–Stockmeyer characterization
`AEXPSPACE = 2EXPTIME` under standard Lean axioms.

## Main definitions

* `Cslib.Complexity.TwoExpTime`: deterministic double-exponential time
  `⋃ k, DTIME (2 ^ (2 ^ (n ^ k)))`.
* `Cslib.Complexity.AEXPSPACE`: alternating exponential space `⋃ k, ASPACE (2 ^ (n ^ k))`.
* `Cslib.Complexity.TwoExpTimeHard`, `Cslib.Complexity.TwoExpTimeComplete`:
  polynomial-time many-one hardness and completeness for `TwoExpTime`.

## Main results

* `Cslib.Complexity.EXP_subset_TwoExpTime`: `EXP ⊆ 2EXPTIME`.
* `Cslib.Complexity.APSPACE_subset_AEXPSPACE`: `APSPACE ⊆ AEXPSPACE`.
* `Cslib.Complexity.compl_mem_TwoExpTime`: `2EXPTIME` is closed under complement.
* `Cslib.Complexity.PolyTimeReducible.mem_TwoExpTime`: `2EXPTIME` is closed under
  polynomial-time many-one reductions.
* `Cslib.Complexity.AEXPSPACE_subset_TwoExpTime`: `AEXPSPACE ⊆ 2EXPTIME`.
* `Cslib.Complexity.TwoExpTime_subset_AEXPSPACE`: `2EXPTIME ⊆ AEXPSPACE`.
* `Cslib.Complexity.AEXPSPACE_eq_TwoExpTime`: `AEXPSPACE = 2EXPTIME`.
-/

public section

namespace Cslib.Complexity

open Cslib Cslib.Complexity Filter _root_.Turing _root_.Turing.MultiTapeTM
open _root_.Turing.MultiTapeATM

/-! ### Definitions -/

/-- Deterministic double-exponential time (`2EXPTIME`): problems decidable in deterministic
time `O(2 ^ (2 ^ (n ^ k)))` for some `k`, where `n` is the length of the encoded instance. -/
def TwoExpTime {α : Type*} (enc : α ↪ List Bool) : Set (Set α) :=
  ⋃ k, DTIME enc fun n => 2 ^ (2 ^ (n ^ k))

/-- Alternating exponential space (`AEXPSPACE`): problems decided by an alternating machine
in space `O(2 ^ (n ^ k))` for some `k`, where `n` is the length of the encoded instance. -/
def AEXPSPACE {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  ⋃ k, ASPACE enc fun n => 2 ^ (n ^ k)

/-- Every problem in `TwoExpTime`, with any encoding of its instances, reduces to `B` in
polynomial time. -/
abbrev TwoExpTimeHard {β : Type*} (encB : β ↪ List Bool) (B : Set β) : Prop :=
  PolyTimeHard @TwoExpTime encB B

/-- `B` belongs to `TwoExpTime` and every problem in `TwoExpTime` reduces to `B` in polynomial
time. -/
abbrev TwoExpTimeComplete {β : Type} (encB : β ↪ List Bool) (B : Set β) : Prop :=
  PolyTimeComplete @TwoExpTime encB B

/-- Characterization of membership in `TwoExpTime`. -/
theorem mem_TwoExpTime_iff {α : Type*} {enc : α ↪ List Bool} {A : Set α} :
    A ∈ TwoExpTime enc ↔ ∃ k, A ∈ DTIME enc fun n => 2 ^ (2 ^ (n ^ k)) :=
  Set.mem_iUnion

/-- Characterization of membership in `AEXPSPACE`. -/
theorem mem_AEXPSPACE_iff {α : Type} {enc : α ↪ List Bool} {A : Set α} :
    A ∈ AEXPSPACE enc ↔ ∃ k, A ∈ ASPACE enc fun n => 2 ^ (n ^ k) :=
  Set.mem_iUnion

/-! ### Basic inclusions and closure properties -/

/-- Deterministic time `2 ^ (2 ^ h n)` for a polynomially bounded exponent `h` lies in
`TwoExpTime`. -/
theorem DTIME_two_pow_two_pow_subset_TwoExpTime {α : Type*} {enc : α ↪ List Bool}
    {h : ℕ → ℕ} (hh : PolynomiallyBounded h) :
    DTIME enc (fun n => 2 ^ (2 ^ h n)) ⊆ TwoExpTime enc := fun _ hA =>
  let ⟨k, hk⟩ := hh
  mem_TwoExpTime_iff.mpr ⟨k, DTIME_mono_of_eventually_le
    (hk.mono fun _ hn => Nat.pow_le_pow_right (by norm_num)
      (Nat.pow_le_pow_right (by norm_num) hn)) hA⟩

/-- Alternating space `2 ^ h n` for a polynomially bounded exponent `h` lies in `AEXPSPACE`. -/
theorem ASPACE_two_pow_subset_AEXPSPACE {α : Type} {enc : α ↪ List Bool}
    {h : ℕ → ℕ} (hh : PolynomiallyBounded h) :
    ASPACE enc (fun n => 2 ^ h n) ⊆ AEXPSPACE enc := fun _ hA =>
  let ⟨k, hk⟩ := hh
  mem_AEXPSPACE_iff.mpr ⟨k, ASPACE_mono_of_eventually_le
    (hk.mono fun _ hn => Nat.pow_le_pow_right (by norm_num) hn) hA⟩

/-- `EXP ⊆ 2EXPTIME`. -/
theorem EXP_subset_TwoExpTime {α : Type*} {enc : α ↪ List Bool} :
    EXP enc ⊆ TwoExpTime enc := fun _ hA =>
  let ⟨k, hk⟩ := mem_EXP_iff.mp hA
  mem_TwoExpTime_iff.mpr ⟨k, DTIME_mono (fun n =>
    Nat.pow_le_pow_right (by norm_num) Nat.lt_two_pow_self.le) hk⟩

/-- `APSPACE ⊆ AEXPSPACE`. -/
theorem APSPACE_subset_AEXPSPACE {α : Type} {enc : α ↪ List Bool} :
    APSPACE enc ⊆ AEXPSPACE enc := fun _ hA =>
  let ⟨k, hk⟩ := mem_APSPACE_iff_exists_mem_ASPACE.mp hA
  mem_AEXPSPACE_iff.mpr ⟨k, ASPACE_mono (fun _ => Nat.lt_two_pow_self.le) hk⟩

/-- `2EXPTIME` is closed under complement. -/
theorem compl_mem_TwoExpTime {α : Type} {enc : α ↪ List Bool} {A : Set α}
    (h : A ∈ TwoExpTime enc) : Aᶜ ∈ TwoExpTime enc :=
  let ⟨k, hk⟩ := mem_TwoExpTime_iff.mp h
  mem_TwoExpTime_iff.mpr ⟨k, compl_mem_DTIME hk⟩

/-- Complement membership in `2EXPTIME` is involutive. -/
@[simp]
theorem compl_mem_TwoExpTime_iff {α : Type} {enc : α ↪ List Bool} {A : Set α} :
    Aᶜ ∈ TwoExpTime enc ↔ A ∈ TwoExpTime enc :=
  ⟨fun h => compl_compl A ▸ compl_mem_TwoExpTime h, compl_mem_TwoExpTime⟩

/-- `2EXPTIME` is closed under polynomial-time many-one reductions. -/
theorem PolyTimeReducible.mem_TwoExpTime {α β : Type} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {A : Set α} {B : Set β}
    (hAB : PolyTimeReducible encA encB A B) (hB : B ∈ TwoExpTime encB) :
    A ∈ TwoExpTime encA := by
  obtain ⟨f, hf, hred⟩ := hAB
  obtain ⟨k, hk⟩ := mem_TwoExpTime_iff.mp hB
  obtain ⟨T, S, hT, -, hfO⟩ := ComputableInPolyTime.exists_computableInO hf
  obtain ⟨c, d, hcd⟩ := (hT.add (ComputableInPolyTime.polyBounded_length hf)).exists_le
  have hpre : f ⁻¹' B ∈ DTIME encA
      (fun n => c * (n + 1) ^ d + 2 ^ (2 ^ ((c * (n + 1) ^ d) ^ k))) := by
    refine preimage_mem_DTIME (C := 1) hk hfO fun a => ?_
    have hca := hcd a
    have hpow : 2 ^ (2 ^ ((encB (f a)).length ^ k)) ≤
        2 ^ (2 ^ ((c * ((encA a).length + 1) ^ d) ^ k)) :=
      Nat.pow_le_pow_right (by norm_num)
        (Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_left (by omega) k))
    omega
  have hA_eq : A = f ⁻¹' B := Set.ext hred
  rw [hA_eq]
  refine DTIME_two_pow_two_pow_subset_TwoExpTime
    (h := fun n => (c * (n + 1) ^ d) ^ k + c * (n + 1) ^ d + 1) (by fun_prop)
    (DTIME_mono (fun n => ?_) hpre)
  set P := c * (n + 1) ^ d
  have h1 : P ≤ 2 ^ (2 ^ (P ^ k + P)) := by
    have hP1 : P ≤ 2 ^ (P ^ k + P) :=
      (Nat.le_add_left P (P ^ k)).trans Nat.lt_two_pow_self.le
    exact hP1.trans Nat.lt_two_pow_self.le
  have h2 : 2 ^ (2 ^ (P ^ k)) ≤ 2 ^ (2 ^ (P ^ k + P)) :=
    Nat.pow_le_pow_right (by norm_num)
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right _ _))
  calc
    P + 2 ^ (2 ^ (P ^ k)) ≤ 2 ^ (2 ^ (P ^ k + P)) + 2 ^ (2 ^ (P ^ k + P)) :=
      Nat.add_le_add h1 h2
    _ = 2 ^ (2 ^ (P ^ k + P) + 1) := by rw [← two_mul, pow_succ']
    _ ≤ 2 ^ (2 ^ (P ^ k + P + 1)) := by
      refine Nat.pow_le_pow_right (by norm_num) ?_
      rw [pow_succ']
      have : 1 ≤ 2 ^ (P ^ k + P) := Nat.one_le_two_pow
      omega

/-! ### `AEXPSPACE ⊆ 2EXPTIME` -/

/-- **`AEXPSPACE ⊆ 2EXPTIME`** [Chandra, Kozen and Stockmeyer, ]: an alternating machine
using exponential space `2 ^ (n ^ k)` is simulated deterministically in double-exponential
time `2 ^ (2 ^ poly(n))`.
-/
theorem AEXPSPACE_subset_TwoExpTime {α : Type} {enc : α ↪ List Bool} :
    AEXPSPACE enc ⊆ TwoExpTime enc := by
  intro A hA
  obtain ⟨k, hk⟩ := mem_AEXPSPACE_iff.mp hA
  obtain ⟨c, hc⟩ := exists_mem_DTIME_of_mem_ASPACE hk
  have hpoly : PolynomiallyBounded (fun n => c + (n + 1) + (n ^ k + 1)) := by fun_prop
  refine DTIME_two_pow_two_pow_subset_TwoExpTime hpoly (DTIME_mono (fun n => ?_) hc)
  refine Nat.pow_le_pow_right (by norm_num) ?_
  have hlog : Nat.log2 n ≤ n := by
    by_cases hn : n = 0
    · simp [hn]
    · exact Nat.lt_two_pow_self.le.trans (Nat.log2_self_le hn)
  have hlin : c * (Nat.log2 n + 2 ^ (n ^ k) + 1) ≤ 2 ^ c * (2 ^ (n + 1) * 2 ^ (n ^ k + 1)) := by
    have hc2 : c ≤ 2 ^ c := Nat.lt_two_pow_self.le
    have hsum : Nat.log2 n + 2 ^ (n ^ k) + 1 ≤ 2 ^ (n + 1) * 2 ^ (n ^ k + 1) := by
      have hn1 : Nat.log2 n + 1 ≤ 2 ^ (n + 1) := by
        have := Nat.lt_two_pow_self (n := n + 1)
        omega
      have h1 : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
      have h2 : 1 ≤ 2 ^ (n ^ k + 1) := Nat.one_le_two_pow
      have hpow : 2 ^ (n ^ k) + 2 ^ (n ^ k) = 2 ^ (n ^ k + 1) := by
        rw [pow_succ']
        ring
      have hpow_le : 2 ^ (n ^ k) ≤ 2 ^ (n ^ k + 1) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _)
      nlinarith
    exact Nat.mul_le_mul hc2 hsum
  calc
    c * (Nat.log2 n + 2 ^ (n ^ k) + 1)
        ≤ 2 ^ c * (2 ^ (n + 1) * 2 ^ (n ^ k + 1)) := hlin
    _ = 2 ^ (c + (n + 1) + (n ^ k + 1)) := by
      rw [pow_add, pow_add]
      ring

/-! ### `2EXPTIME ⊆ AEXPSPACE` -/

private theorem two_pow_bound (c₁ c₂ m n : ℕ) :
    c₁ * 2 ^ m + c₂ ≤ 2 ^ (m + c₁ + c₂ + n) := by
  have h₁ : c₁ < 2 ^ c₁ := Nat.lt_two_pow_self
  have h₂ : c₂ < 2 ^ c₂ := Nat.lt_two_pow_self
  have hX : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hR : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  rw [pow_add, pow_add, pow_add]
  have hPQ : 2 ^ c₁ + 2 ^ c₂ ≤ 2 ^ c₁ * 2 ^ c₂ + 1 := by nlinarith
  nlinarith [Nat.mul_le_mul_left (2 ^ m * 2 ^ c₁ * 2 ^ c₂) hR]

/-- A `ComputableInSpace` certificate gives a single tidy machine whose space is bounded by
`c * (B a + 1)`. -/
private theorem tidy_of_inSpace {α β : Type} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    {f : α → β} {B : α → ℕ} (h : ComputableInSpace f encIn encOut B) :
    ∃ (c : ℕ) (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State)
      (t : α → ℕ), ∀ a, tm.ComputesTidilyInTimeAndSpace (encIn a) (encOut (f a)) (t a)
        (c * (B a + 1)) := by
  obtain ⟨T, c₀, hc₀, -⟩ := h.exists_inO
  obtain ⟨c₁, k, State, hfin, tm, htm⟩ := hc₀.exists_computableTidilyInTimeAndSpace
  exact ⟨c₁ * (c₀ + 1), k, State, hfin, tm, _, fun a =>
    (htm a).mono le_rfl (by
      have : c₁ * (c₀ * (B a + 1) + 1) ≤ c₁ * (c₀ + 1) * (B a + 1) := by nlinarith
      exact this)⟩

/-- Word games whose initial position, linear-space update, and reachable position length stay
within a space bound `Bs` (with `∀ a, Bs a ≤ s (enc a).length`) are decided in `ASPACE s`. -/
private theorem mem_ASPACE_of_wins_inSpace {α π : Type} {enc : α ↪ List Bool}
    {encPos : π ↪ List Bool} {A : Set α} {I : α → List Bool} {U : List Bool → List Bool}
    {F : π → List Bool} {Bs ℓ : α → ℕ} {s : ℕ → ℕ}
    (hI : ComputableInSpace I enc encBits Bs)
    (hF : ComputableInSpace F encPos encBits fun p => (encPos p).length)
    (hℓ : ∀ a, ℓ a ≤ Bs a)
    (hBs : ∀ a, Bs a ≤ s (enc a).length)
    (hpos : ∀ a u x r b, WordGame.Reach U (I a) (u :: x :: r) →
      ∃ p, encPos p = u :: b :: r ∧ F p = U (u :: b :: r))
    (hlen : ∀ a w, WordGame.Reach U (I a) w → w.length ≤ ℓ a)
    (hends : ∀ a, ∃ n, WordGame.Ends U n (I a))
    (hA : ∀ a, a ∈ A ↔ WordGame.Wins U (I a)) : A ∈ ASPACE enc s := by
  classical
  obtain ⟨cI, kI, SI, _, TI, tI, hTI⟩ := tidy_of_inSpace hI
  obtain ⟨cU, kU, SU, _, TU, tU, hTU⟩ := tidy_of_inSpace hF
  set K := kI + kU + 3 with hK
  let N : Fin K := ⟨0, by omega⟩
  let O : Fin K := ⟨1, by omega⟩
  let M : Fin K := ⟨2, by omega⟩
  have hNO : N ≠ O := by simp [N, O]
  have hNM : N ≠ M := by simp [N, M]
  have hOM : O ≠ M := by simp [O, M]
  obtain ⟨eI, heI⟩ := Fin.exists_embedding_eq (show kI + 1 ≤ K by omega) (Fin.last kI) N
  obtain ⟨eU, heUi, heUo⟩ := Fin.exists_embedding_eq₂
    (show kU + 1 + 2 ≤ K by omega)
    (i := Fin.natAdd (kU + 1) 0) (o := (Fin.last kU).castAdd 2) (by simp [Fin.ext_iff]) hNO
  let Pm := TI.outputToWord.extendTapes eI
  let R := frozenRound (nop K Bool) ((TU.onWords true).extendTapes eU) N O M hNO hNM hOM
  let sR : α → ℕ := fun a => cU * (ℓ a + 1) + 10 * ℓ a + 5 * K + 3 * kU + 40
  have hround (p : π) : ∃ t, TransformsTapes R
      (fun _ ws => ws = Function.update (fun _ => []) N (encPos p))
      (fun _ _ ws' em => ws' = Function.update (fun _ => []) N (F p) ∧ em = []) t
      (cU * ((encPos p).length + 1) + 3 * (encPos p).length + 7 * (F p).length + 5 * K +
        3 * kU + 40) := by
    have hE := (transformsTapes_nop K Bool).imp
      (P' := fun _ ws => ws = Function.update (fun _ => []) N (encPos p))
      (Q' := fun _ ws ws' em => ws' = ws ∧ em = []) (fun _ _ _ => trivial)
      (fun _ _ _ _ _ h => h) le_rfl le_rfl
    have hNm := (hTU p).onWords_extendTapes true heUi heUo
    simp only [encBits_apply] at hNm
    exact ⟨_, (transformsTapes_frozenRound hNO hNM hOM hE hNm).mono le_rfl (by omega)⟩
  choose tp htp using hround
  let tRw : List Bool → ℕ := fun w => if h : ∃ p, encPos p = w then tp h.choose else 0
  let tR : α → ℕ := fun a => (List.finite_length_le Bool (ℓ a)).toFinset.sup tRw
  have htR (a : α) (p : π) (hp : (encPos p).length ≤ ℓ a) : tp p ≤ tR a := by
    have hmem : encPos p ∈ (List.finite_length_le Bool (ℓ a)).toFinset := by simpa using hp
    have h1 : tRw (encPos p) = tp p := by
      have hex : ∃ q, encPos q = encPos p := ⟨p, rfl⟩
      simp only [tRw, hex, ↓reduceDIte]
      exact congrArg tp (encPos.injective hex.choose_spec)
    exact h1 ▸ Finset.le_sup (f := tRw) hmem
  let tP : α → ℕ := fun a => tI a + (I a).length + 2
  let sP : α → ℕ := fun a => cI * (Bs a + 1) + 2 * (I a).length + kI + 4 + (K - (kI + 1))
  have hP (a : α) : WordGame.PrepSpec Pm N (enc a) (I a) (tP a) (sP a) := by
    obtain ⟨ws, em, hrun, ⟨rfl, rfl⟩, hsp⟩ := transformsTapes_iff_runFrom.mp
      ((hTI a).outputToWord_onTape heI) (enc a) (fun _ => []) [] ⟨rfl, rfl⟩
    unfold WordGame.PrepSpec
    rw [Cfg.init_eq_wordsCfg]
    exact ⟨hrun, hsp⟩
  have hR (a : α) : WordGame.RoundSpec R N (enc a) U (I a) (tR a) (sR a) := by
    intro u x r hreach b
    obtain ⟨p, hp, hFp⟩ := hpos a u x r b hreach
    have hw : (u :: b :: r).length ≤ ℓ a := by simpa using hlen a _ hreach
    have hUw : (U (u :: b :: r)).length ≤ ℓ a := hlen a _ (WordGame.Reach.move b hreach)
    rw [← hFp] at hUw ⊢
    rw [← hp] at hw ⊢
    have hmul : cU * ((encPos p).length + 1) ≤ cU * (ℓ a + 1) :=
      Nat.mul_le_mul_left cU (Nat.add_le_add_right hw 1)
    have h := (htp p).mono (t' := tR a) (s' := sR a) (htR a p hw) (by simp only [sR]; omega)
    obtain ⟨ws, em, hrun, ⟨rfl, rfl⟩, hsp⟩ := transformsTapes_iff_runFrom.mp h (enc a) _ [] rfl
    exact ⟨hrun, hsp⟩
  have hspec (a : α) := wordGame_spec (hP a) (hR a)
  have hIlen : ∀ a, (I a).length ≤ ℓ a := fun a => hlen a (I a) .start
  let C1 : ℕ := K * (2 * (cI + 2 + cU + 10) + 1)
  let C2 : ℕ := K * (2 * (cI + kI + 4 + (K - (kI + 1)) + cU + 5 * K + 3 * kU + 40) + 2) + K
  refine ⟨K, _, inferInstance, wordGame Pm R N, C1, C2,
    ⟨fun a => ⟨(hspec a).1.mono ?_, ?_⟩, fun a => ?_⟩⟩
  · have h1 := hℓ a
    have h2 := hBs a
    have h3 := hIlen a
    have hsP_le : sP a ≤ (cI + 2) * Bs a + (cI + kI + 4 + (K - (kI + 1))) := by
      simp only [sP]
      nlinarith
    have hsR_le : sR a ≤ (cU + 10) * Bs a + (cU + 5 * K + 3 * kU + 40) := by
      simp only [sR]
      nlinarith
    have hmax : max (max (sP a) (sR a)) 1 ≤
        (cI + 2 + cU + 10) * Bs a + (cI + kI + 4 + (K - (kI + 1)) + cU + 5 * K + 3 * kU + 40) +
        1 := by
      refine max_le (max_le ?_ ?_) ?_ <;> nlinarith
    have hmul : K * (2 * max (max (sP a) (sR a)) 1 + 1) ≤ C1 * Bs a + C2 := by
      simp only [C1, C2]
      have := Nat.mul_le_mul_left K (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hmax) 1)
      nlinarith
    exact hmul.trans (Nat.add_le_add_right (Nat.mul_le_mul_left C1 h2) C2)
  · rw [hA a, (hspec a).2.1]
  · obtain ⟨n, hn⟩ := hends a
    exact ⟨_, (hspec a).2.2 n hn⟩

section TwoExp

open Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.Tableau
  Cslib.Circuits.Boolean.Tableau.ValueGame
open Turing.MultiTapeTM.ComputableInSpace

/-- **`2EXPTIME ⊆ AEXPSPACE`** [Chandra, Kozen and Stockmeyer, ]: the circuit-value game on
the tableau of a double-exponential-time decider is played in alternating exponential space.
-/
theorem TwoExpTime_subset_AEXPSPACE {α : Type} {enc : α ↪ List Bool} :
    TwoExpTime enc ⊆ AEXPSPACE enc := by
  intro A hA
  obtain ⟨d, c₁, c₂, s, k, State, hfin, tm, htm⟩ := mem_TwoExpTime_iff.mp hA
  have := Fintype.ofFinite State
  classical
  set n : α → ℕ := fun a => (enc a).length
  set E : α → ℕ := fun a => n a ^ d + c₁ + c₂ + n a + 1
  set F : α → ℕ := fun a => 2 ^ E a
  set T : α → ℕ := fun a => 2 ^ F a
  set N : α → ℕ := fun a => outWire k State (n a) (T a)
  set M : α → ℕ := fun a => n a + numGates k State (T a)
  set Bs : α → ℕ := fun a => n a + F a
  have hin : (fun a => (enc a).length) ≼ Bs := .of_le fun a => by simp [Bs, n]
  have hx : ComputableInSpace (fun a => enc a) enc (encList encBool) Bs :=
    ((budget_comp_linear (of_inO ComputableInDegree.bitsToList.inO_one)
      ((of_inO ComputableInDegree.id'.inO_one).of_enc_eq
        (encB := encBits) (g := fun a => enc a) fun _ => rfl)).weaken hin)
  have hn : ComputableInSpace n enc encNat Bs := budget_length hx
  have hE : ComputableInSpace E enc encNat Bs :=
    budget_natAdd
      (budget_natAdd (budget_natAdd (budget_natAdd (budget_natPow hn d) (budget_const c₁))
        (budget_const c₂)) hn)
      (budget_const 1)
  have hF : ComputableInSpace F enc encNat Bs := by
    refine budget_natPow_variable (budget_const 2) hE (.of_le_linear 3 3 fun a => ?_)
    have h2 : (encNat 2).length = 2 := rfl
    have hEl : (encNat (E a)).length ≤ E a :=
      length_encNat_le_of_lt_two_pow Nat.lt_two_pow_self
    have hEF : E a ≤ F a := Nat.lt_two_pow_self.le
    simp only [h2, Bs]
    nlinarith
  have hT : ComputableInSpace T enc encNat Bs := by
    refine budget_natPow_variable (budget_const 2) hF (.of_le_linear 3 3 fun a => ?_)
    have h2 : (encNat 2).length = 2 := rfl
    have hFl : (encNat (F a)).length ≤ F a :=
      length_encNat_le_of_lt_two_pow Nat.lt_two_pow_self
    simp only [h2, Bs]
    nlinarith
  have hN : ComputableInSpace N enc encNat Bs :=
    outWire_inSpace (k := k) (State := State) hT hn
  have hM : ComputableInSpace M enc encNat Bs :=
    budget_natAdd hn (budget_natAdd (budget_const 2)
      (budget_natMul (budget_natAdd hT (budget_const 1))
        (blockSize_inSpace (k := k) (State := State) hT)))
  have hJ := encClaim_mk_budget hx hT hN (budget_const (encB := encBool) true)
  have hJM := encClaim_mk_budget hx hT hM (budget_const (encB := encBool) true)
  have hI : ComputableInSpace (fun a => position tm encClaim ⟨enc a, T a, N a, true⟩)
      enc encBits Bs :=
    budget_comp_linear (position_inSpace tm) hJ
  have hJM_len : (fun a => (encClaim ⟨enc a, T a, M a, true⟩).length) ≼ Bs := hJM.length_le
  obtain ⟨cL, hcL⟩ := hJM_len
  set Bs' : α → ℕ := fun a => max (Bs a) (cL * (Bs a + 1) + 2)
  have hBs_le : ∀ a, Bs a ≤ Bs' a := fun a => le_max_left _ _
  have hI' : ComputableInSpace (fun a => position tm encClaim ⟨enc a, T a, N a, true⟩)
      enc encBits Bs' := hI.mono_le hBs_le
  have hNM (a : α) : N a < M a := outWire_lt (k := k) (State := State) _ _
  have hpolyExp : PolynomiallyBounded (fun m => m ^ d + c₁ + c₂ + m + 1 + 1) := by fun_prop
  have hBs'_bound : ∀ a, Bs' a ≤ (cL + 1) * 2 ^ (n a ^ d + c₁ + c₂ + n a + 1 + 1) + (cL + 2) := by
    intro a
    have h1 : n a ≤ F a :=
      (by simp only [E]; omega : n a ≤ E a).trans Nat.lt_two_pow_self.le
    have h2 : Bs a ≤ 2 ^ (E a + 1) := by
      change n a + F a ≤ 2 ^ (E a + 1)
      rw [pow_succ']
      have : F a = 2 ^ E a := rfl
      omega
    have h3 : Bs' a ≤ cL * (Bs a + 1) + 2 + Bs a := by
      simp only [Bs']
      omega
    have h4 : cL * (Bs a + 1) + 2 + Bs a ≤ (cL + 1) * 2 ^ (E a + 1) + (cL + 2) := by
      nlinarith
    exact h3.trans h4
  have hmem : A ∈ ASPACE enc
      (fun m => (cL + 1) * 2 ^ (m ^ d + c₁ + c₂ + m + 1 + 1) + (cL + 2)) := by
    refine mem_ASPACE_of_wins_inSpace (π := Pos) (encPos := encPos) (F := step tm)
      (U := update tm encClaim) (Bs := Bs') (ℓ := fun a => cL * (Bs a + 1) + 2)
      hI' (step_inSpace tm) (fun a => le_max_right _ _) hBs'_bound ?_ ?_ ?_ ?_
    · intro a u x r b hr
      obtain ⟨w', v, -, he⟩ := reach_position (tm := tm) encClaim (hNM a) hr
      obtain ⟨-, rfl⟩ := position_eq_cons he.symm
      exact ⟨pos u b ⟨enc a, T a, w', v⟩, encPos_pos _ _ _, by rw [step_pos, update_position_cons]⟩
    · intro a w hr
      obtain ⟨w', v, hw', rfl⟩ := reach_position (tm := tm) encClaim (hNM a) hr
      exact (length_position_le _).trans
        (Nat.add_le_add_right ((length_encClaim_mono hw'.le).trans (hcL a)) 2)
    · exact fun a => ⟨N a, ends_position (tm := tm) encClaim (enc a) (T a) (N a) (hNM a) true⟩
    · intro a
      have hnT : (enc a).length < 2 * T a := by
        have h1 : n a < F a :=
          (by simp only [E]; omega : n a ≤ E a).trans_lt Nat.lt_two_pow_self
        have h2 : F a < T a := Nat.lt_two_pow_self
        simp only [n] at h1
        omega
      have hle : c₁ * 2 ^ (2 ^ ((enc a).length ^ d)) + c₂ ≤ T a := by
        have hbase : 2 ^ ((enc a).length ^ d) + c₁ + c₂ + 0 ≤ F a := by
          have h1 : 2 ^ ((enc a).length ^ d) ≤ 2 ^ ((enc a).length ^ d + c₁ + c₂) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
          have h2 : c₁ + c₂ ≤ 2 ^ ((enc a).length ^ d + c₁ + c₂) :=
            Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
          have h3 : 2 ^ ((enc a).length ^ d + c₁ + c₂ + 1) ≤ F a :=
            Nat.pow_le_pow_right (by norm_num) (by simp only [E, n]; omega)
          rw [pow_succ'] at h3
          omega
        exact (two_pow_bound c₁ c₂ (2 ^ ((enc a).length ^ d)) 0).trans
          (Nat.pow_le_pow_right (by norm_num) hbase)
      obtain ⟨-, hout⟩ := (htm a).runFrom_of_le hle
      refine Iff.trans ?_ (wins_position_outWire_iff (tm := tm) encClaim hnT).symm
      rw [hout]
      by_cases h : a ∈ A <;> simp [h, indicator, OutView.ofList]
  exact ASPACE_two_pow_subset_AEXPSPACE hpolyExp
    (ASPACE_mono_of_le_mul_add (C := cL + 1 + cL + 2) (fun m => by
      have : 1 ≤ 2 ^ (m ^ d + c₁ + c₂ + m + 1 + 1) := Nat.one_le_two_pow
      nlinarith) hmem)

end TwoExp

/-- **`AEXPSPACE = 2EXPTIME`** [Chandra, Kozen and Stockmeyer, ]: alternating exponential
space coincides with deterministic double-exponential time.
-/
theorem AEXPSPACE_eq_TwoExpTime {α : Type} {enc : α ↪ List Bool} :
    AEXPSPACE enc = TwoExpTime enc :=
  le_antisymm AEXPSPACE_subset_TwoExpTime TwoExpTime_subset_AEXPSPACE

end Cslib.Complexity
