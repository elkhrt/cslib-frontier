module

public import CslibFrontier.Computability.Circuit.Boolean.Hastad.AverageCase
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Bool
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Computability.Circuit.CompositionDepth
import CslibFrontier.Computability.Circuit.Pi
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryDivision
import CslibFrontier.Crypto.Primitives.PRG.NisanWigderson.BitPolynomial
import CslibFrontier.Crypto.Primitives.PRG.NisanWigderson.Design
import CslibFrontier.Foundations.Data.Nat.Log
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import CslibFrontier.Probability.PMF.Event
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Explicit Polynomial-Time Nisan–Wigderson PRG for Constant-Depth Circuits

This module constructs an explicit, polynomial-time bit-computable Nisan–Wigderson pseudorandom
generator based on low-degree polynomial designs over prime fields and parity, fooling
polynomial-size constant-depth unbounded fan-in Boolean circuits (`AC⁰`) with polylogarithmic
seed length.

## Main definitions

* `CslibFrontier.Crypto.PRG.NisanWigderson.AC0.nwAC0Prime`, `nwAC0SeedLen`, `nwAC0Bit`,
  `nwAC0Gen`: the explicit polynomial-design Nisan–Wigderson generator for `AC⁰`.

## Main results

* `CslibFrontier.Crypto.PRG.NisanWigderson.AC0.computableInPolyTime_nwAC0Bit`:
  each output bit of `nwAC0Gen` is computable in time polynomial in `log M` and the seed length.
* `CslibFrontier.Crypto.PRG.NisanWigderson.AC0.nwAC0SeedLen_le`:
  polylogarithmic seed-length upper bound `O((log M + 1)^(2 d + 10))`.
* `CslibFrontier.Crypto.PRG.NisanWigderson.AC0.nwAC0Gen_fools_circuit`:
  `nwAC0Gen d c M` fools every unbounded fan-in circuit of depth `≤ d` and size `≤ c (M + 1)^c`
  within `1 / 100`.
* `CslibFrontier.Crypto.PRG.NisanWigderson.AC0.nwAC0Gen_expSize_barrier`:
  no polylogarithmic-seed generator can fool depth-2 circuits of size `2^(n^α)`.
-/

public section

namespace CslibFrontier.Crypto.PRG.NisanWigderson.AC0

open Cslib Cslib.BitString Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.Unbounded
open Cslib.Crypto.PRG Cslib.Crypto.PRG.NisanWigderson Cslib.Probability.PMF
open Finset _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.ComputableInPolyTime
open CslibFrontier.Computability.Circuit.Boolean.Hastad

/-! ### Part 3: Concrete Polynomial-Time `ZMod q` NW Generator for AC⁰ -/

/-- Decidable primality check over unary range `List.range p`. -/
def isPrimeBool (p : ℕ) : Bool :=
  decide (2 ≤ p) && (List.range p).all fun d => decide (d < 2) || decide (p % d ≠ 0)

theorem isPrimeBool_eq_true_iff (p : ℕ) : isPrimeBool p = true ↔ p.Prime := by
  simp only [isPrimeBool, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, ne_eq]
  constructor
  · rintro ⟨hp2, hall⟩
    rw [Nat.prime_def_lt]
    refine ⟨hp2, fun d hdp hdvd => ?_⟩
    rcases hall d hdp with hlt | hmod
    · have : d ≠ 0 := by intro h0; subst h0; simp at hdvd; omega
      omega
    · exact absurd (Nat.mod_eq_zero_of_dvd hdvd) hmod
  · intro hp
    refine ⟨hp.two_le, fun d hdp => ?_⟩
    by_cases hd2 : d < 2
    · exact Or.inl hd2
    · refine Or.inr fun hmod => ?_
      have hdvd : d ∣ p := Nat.dvd_of_mod_eq_zero hmod
      rcases hp.eq_one_or_self_of_dvd d hdvd with rfl | rfl <;> omega

/-- Least prime in `[L, 2 * L]` found by scanning `off = 0, ..., L`. -/
def leastPrimeGe (L : ℕ) : ℕ :=
  L + ((List.range (L + 1)).find? fun off => isPrimeBool (L + off)).getD 0

theorem leastPrimeGe_spec {L : ℕ} (hL : 1 ≤ L) :
    (leastPrimeGe L).Prime ∧ L ≤ leastPrimeGe L ∧ leastPrimeGe L ≤ 2 * L := by
  obtain ⟨p, hp, hLp, hp2L⟩ := Nat.exists_prime_lt_and_le_two_mul L (by omega)
  have hex : ∃ off ∈ List.range (L + 1), isPrimeBool (L + off) = true := by
    refine ⟨p - L, List.mem_range.mpr (by omega), ?_⟩
    rw [Nat.add_sub_cancel' hLp.le, isPrimeBool_eq_true_iff]
    exact hp
  cases hfind : (List.range (L + 1)).find? (fun off => isPrimeBool (L + off)) with
  | none =>
    exfalso
    obtain ⟨off, hoff, hpr⟩ := hex
    exact absurd hpr (by simpa using List.find?_eq_none.mp hfind off hoff)
  | some off =>
    have hmem := List.mem_of_find?_eq_some hfind
    have hpr := List.find?_some hfind
    rw [List.mem_range] at hmem
    rw [isPrimeBool_eq_true_iff] at hpr
    simp only [leastPrimeGe, hfind, Option.getD_some]
    exact ⟨hpr, by omega, by omega⟩

/-- Bit-width `ℓ = max 1 M.size` of output indices `i < M`. -/
def nwAC0IndexBits (M : ℕ) : ℕ := max 1 M.size

/-- Target Håstad parameter `s` for depth `d`, polynomial exponent `c`, and output length `M`. -/
def nwAC0HastadParam (c M : ℕ) : ℕ :=
  (c + 4) * nwAC0IndexBits M + c + 20

/-- Prime lower bound `L = 17 * s * (16 * s + 1) ^ (d + 1) + 17`. -/
def nwAC0PrimeLower (d c M : ℕ) : ℕ :=
  let s := nwAC0HastadParam c M
  17 * s * (16 * s + 1) ^ (d + 1) + 17

/-- Explicit prime modulus `q` for the `ZMod q` polynomial design of `nwAC0Gen d c`. -/
def nwAC0Prime (d c M : ℕ) : ℕ :=
  leastPrimeGe (nwAC0PrimeLower d c M)

/-- Explicit seed length `q ^ 2` of `nwAC0Gen d c` for output length `M`. -/
def nwAC0SeedLen (d c M : ℕ) : ℕ :=
  nwAC0Prime d c M * nwAC0Prime d c M

/-- Compute `(∑_{t < ℓ} (if i.testBit t then j^t else 0)) % max 1 q` via a bounded unary fold. -/
def polyEvalMod (ℓ i j q : ℕ) : ℕ :=
  let m := max 1 q
  ((List.range ℓ).foldl
    (fun (st : ℕ × ℕ) (t : ℕ) =>
      let acc := if i.testBit t then (st.1 + st.2) % m else st.1
      let pw := (st.2 * j) % m
      (acc, pw))
    (0, 1 % m)).1

/-- The `i`-th output bit of `nwAC0Gen d c` on output length `M` and seed `seed`
(totalized with `false` for out-of-range lookups). -/
def nwAC0Bit (d c : ℕ) (Mis : ℕ × ℕ × List Bool) : Bool :=
  let M := Mis.1
  let i := Mis.2.1
  let seed := Mis.2.2
  let ℓ := nwAC0IndexBits M
  let q := nwAC0Prime d c M
  let rowBits : List Bool :=
    (List.range q).map fun j => seed.getD (j * q + polyEvalMod ℓ i j q) false
  rowBits.foldl (fun acc b => acc ^^ b) false

/-- Fixed-length view of `nwAC0Gen d c` as a `BitString (nwAC0SeedLen d c M) → BitString M`. -/
def nwAC0Gen (d c M : ℕ) (s : BitString (nwAC0SeedLen d c M)) : BitString M :=
  fun i => nwAC0Bit d c (M, i.1, List.ofFn s)

/-- Pointwise evaluation of `nwAC0Gen` in terms of `nwAC0Bit`. -/
theorem nwAC0Gen_apply (d c M : ℕ) (s : BitString (nwAC0SeedLen d c M)) (i : Fin M) :
    nwAC0Gen d c M s i = nwAC0Bit d c (M, i.1, List.ofFn s) := by
  rfl

/-- The NW seed length `nwAC0SeedLen d c M = q ^ 2` is always strictly positive. -/
theorem nwAC0SeedLen_pos (d c M : ℕ) : 0 < nwAC0SeedLen d c M := by
  have hpr := (leastPrimeGe_spec (L := nwAC0PrimeLower d c M)
    (by dsimp [nwAC0PrimeLower]; omega)).1.pos
  exact Nat.mul_pos hpr hpr

/-- The binary bit-width `M.size` is bounded by `nwAC0SeedLen d c M`. -/
theorem size_le_nwAC0SeedLen (d c M : ℕ) : M.size ≤ nwAC0SeedLen d c M := by
  have hℓ : M.size ≤ nwAC0IndexBits M := le_max_right _ _
  have hs : M.size ≤ nwAC0HastadParam c M := by unfold nwAC0HastadParam; nlinarith
  have hp : 1 ≤ (16 * nwAC0HastadParam c M + 1) ^ (d + 1) := Nat.one_le_pow _ _ (by omega)
  have hL : M.size ≤ nwAC0PrimeLower d c M := by unfold nwAC0PrimeLower; nlinarith
  have hq : M.size ≤ nwAC0Prime d c M :=
    hL.trans (leastPrimeGe_spec (by dsimp [nwAC0PrimeLower]; omega)).2.1
  unfold nwAC0SeedLen
  nlinarith

/-- `nwAC0Bit d c (M, idx, s)` only inspects indices `< nwAC0SeedLen d c M`, so it agrees with
evaluating on the truncated/zero-padded `BitString (nwAC0SeedLen d c M)`. -/
theorem nwAC0Bit_eq_ofFn (d c M idx : ℕ) (s : List Bool) :
    nwAC0Bit d c (M, idx, s) =
      nwAC0Bit d c (M, idx, List.ofFn fun i : Fin (nwAC0SeedLen d c M) => s.getD i.1 false) := by
  unfold nwAC0Bit
  dsimp only
  congr 1
  refine List.map_congr_left fun j hj => ?_
  have hjlt : j < nwAC0Prime d c M := List.mem_range.mp hj
  have hqpos : 0 < nwAC0Prime d c M :=
    (leastPrimeGe_spec (by dsimp [nwAC0PrimeLower]; omega)).1.pos
  have hpe : polyEvalMod (nwAC0IndexBits M) idx j (nwAC0Prime d c M) < nwAC0Prime d c M := by
    have hm : max 1 (nwAC0Prime d c M) = nwAC0Prime d c M := max_eq_right hqpos
    have hf : ∀ l : ℕ, ((List.range l).foldl (fun (st : ℕ × ℕ) (t : ℕ) =>
        (if idx.testBit t then (st.1 + st.2) % nwAC0Prime d c M else st.1,
          (st.2 * j) % nwAC0Prime d c M))
        (0, 1 % nwAC0Prime d c M)).1 < nwAC0Prime d c M := by
      intro l; induction l with
      | zero => simpa using hqpos
      | succ l ihl =>
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
        dsimp only; split_ifs
        · exact Nat.mod_lt _ hqpos
        · exact ihl
    rw [polyEvalMod, hm]; exact hf _
  have hidx_lt : j * nwAC0Prime d c M +
      polyEvalMod (nwAC0IndexBits M) idx j (nwAC0Prime d c M) < nwAC0SeedLen d c M := by
    unfold nwAC0SeedLen
    have : (j + 1) * nwAC0Prime d c M ≤ nwAC0Prime d c M * nwAC0Prime d c M :=
      Nat.mul_le_mul_right _ hjlt
    nlinarith
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hidx_lt, ↓reduceDIte, Option.getD_some]

/-! #### Equivalence between `nwAC0Gen` and `NisanWigderson.generator` over `ZMod q` -/

private lemma equivFin_symm_eq_testBit {ℓ : ℕ} (i : Fin (2 ^ ℓ)) (t : Fin ℓ) :
    (BitString.equivFin ℓ).symm i t = i.1.testBit t.1 := by
  have h1 : ∀ (k : ℕ) (x : BitString k) (t : Fin k),
      (BitString.equivFin k x).1.testBit t.1 = x t := by
    intro k
    induction k with
    | zero => intro _ t; exact t.elim0
    | succ k ih =>
      intro x t
      rw [BitString.val_equivFin_succ]
      induction t using Fin.lastCases with
      | last =>
        have hlt : (BitString.equivFin k (Fin.init x)).1 < 2 ^ k := (BitString.equivFin k _).2
        have hdiv : ((BitString.equivFin k (Fin.init x)).1 +
            (x (Fin.last k)).toNat * 2 ^ k) / 2 ^ k = (x (Fin.last k)).toNat := by
          rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt hlt, zero_add]
        rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Fin.val_last, hdiv]
        cases x (Fin.last k) <;> rfl
      | cast t =>
        have hmod : ((BitString.equivFin k (Fin.init x)).1 +
            (x (Fin.last k)).toNat * 2 ^ k) % 2 ^ k =
            (BitString.equivFin k (Fin.init x)).1 := by
          rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (BitString.equivFin k _).2]
        have htb := Nat.testBit_mod_two_pow
          ((BitString.equivFin k (Fin.init x)).1 + (x (Fin.last k)).toNat * 2 ^ k) k t.1
        simp only [hmod, t.2, decide_true, Bool.true_and] at htb
        rw [Fin.val_castSucc, ← htb, ih]
        rfl
  have h := h1 ℓ ((BitString.equivFin ℓ).symm i) t
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

private lemma polyEvalMod_eq_zmod_val {ℓ i j q : ℕ} (hq : 0 < q) :
    (polyEvalMod ℓ i j q : ZMod q) =
      ∑ t : Fin ℓ, if i.testBit t.1 then ((j : ZMod q) ^ t.1) else 0 := by
  have hm : max 1 q = q := max_eq_right hq
  have hfold : ∀ m : ℕ,
      let r := (List.range m).foldl
        (fun (st : ℕ × ℕ) (t : ℕ) =>
          let acc := if i.testBit t then (st.1 + st.2) % q else st.1
          let pw := (st.2 * j) % q
          (acc, pw))
        (0, 1 % q)
      (r.1 : ZMod q) = (∑ t ∈ Finset.range m, if i.testBit t then ((j : ZMod q) ^ t) else 0) ∧
      (r.2 : ZMod q) = (j : ZMod q) ^ m := by
    intro m
    induction m with
    | zero =>
      simp only [List.range_zero, List.foldl_nil, Finset.range_zero, Finset.sum_empty, pow_zero,
        Nat.cast_zero, true_and]
      rw [ZMod.natCast_mod, Nat.cast_one]
    | succ m ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        Finset.sum_range_succ]
      dsimp only at ih ⊢
      constructor
      · split_ifs with hbit
        · rw [ZMod.natCast_mod, Nat.cast_add, ih.1, ih.2]
        · rw [ih.1, add_zero]
      · rw [ZMod.natCast_mod, Nat.cast_mul, ih.2, pow_succ]
  have h := (hfold ℓ).1
  dsimp only at h
  rw [polyEvalMod, hm, h, ← Fin.sum_univ_eq_sum_range]

private lemma polyEvalMod_lt {ℓ i j q : ℕ} (hq : 0 < q) : polyEvalMod ℓ i j q < q := by
  have hm : max 1 q = q := max_eq_right hq
  have hfold : ∀ m : ℕ,
      ((List.range m).foldl
        (fun (st : ℕ × ℕ) (t : ℕ) =>
          let acc := if i.testBit t then (st.1 + st.2) % q else st.1
          let pw := (st.2 * j) % q
          (acc, pw))
        (0, 1 % q)).1 < q := by
    intro m
    induction m with
    | zero => simpa using hq
    | succ m ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      dsimp only
      split_ifs
      · exact Nat.mod_lt _ hq
      · exact ih
  rw [polyEvalMod, hm]
  exact hfold ℓ

private lemma foldl_xor_range_eq_parity {q : ℕ} (f : Fin q → Bool) :
    ((List.range q).map fun j => if h : j < q then f ⟨j, h⟩ else false).foldl
      (fun acc b => acc ^^ b) false = parity q f := by
  have haux : ∀ m (hm : m ≤ q),
      ((List.range m).map fun j => if h : j < q then f ⟨j, h⟩ else false).foldl
        (fun acc b => acc ^^ b) false =
      decide (#(Finset.univ.filter fun j : Fin q => j.1 < m ∧ f j = true) % 2 = 1) := by
    intro m hm
    induction m with
    | zero =>
      simp only [List.range_zero, List.map_nil, List.foldl_nil, Nat.not_lt_zero, false_and,
        Finset.filter_false, Finset.card_empty]
      rfl
    | succ m ih =>
      have hmq : m < q := by omega
      rw [List.range_succ, List.map_append, List.map_singleton, List.foldl_append,
        List.foldl_cons, List.foldl_nil, ih (by omega)]
      simp only [hmq, ↓reduceDIte]
      cases hfm : f ⟨m, hmq⟩ with
      | false =>
        have hfilt : (Finset.univ.filter fun j : Fin q => j.1 < m + 1 ∧ f j = true) =
            Finset.univ.filter fun j : Fin q => j.1 < m ∧ f j = true := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨hjlt, hfj⟩
            refine ⟨?_, hfj⟩
            by_contra hge
            have hjeq : j = ⟨m, hmq⟩ := Fin.ext (show j.1 = m by omega)
            rw [hjeq, hfm] at hfj
            cases hfj
          · rintro ⟨hjlt, hfj⟩; exact ⟨by omega, hfj⟩
        rw [hfilt, Bool.xor_false]
      | true =>
        have hfilt : (Finset.univ.filter fun j : Fin q => j.1 < m + 1 ∧ f j = true) =
            insert ⟨m, hmq⟩ (Finset.univ.filter fun j : Fin q => j.1 < m ∧ f j = true) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
          constructor
          · rintro ⟨hjlt, hfj⟩
            by_cases hjm : j.1 = m
            · exact Or.inl hjm
            · exact Or.inr ⟨by omega, hfj⟩
          · rintro (hjm | ⟨hjlt, hfj⟩)
            · have hjeq : j = ⟨m, hmq⟩ := Fin.ext hjm
              rw [hjeq]; exact ⟨by omega, hfm⟩
            · exact ⟨by omega, hfj⟩
        have hnotmem : (⟨m, hmq⟩ : Fin q) ∉
            Finset.univ.filter fun j : Fin q => j.1 < m ∧ f j = true := by
          simp
        rw [hfilt, Finset.card_insert_of_notMem hnotmem, Bool.xor_true]
        set c := #(Finset.univ.filter fun j : Fin q => j.1 < m ∧ f j = true)
        rcases Nat.mod_two_eq_zero_or_one c with hmod | hmod <;> simp [Nat.add_mod, hmod]
  have h := haux q le_rfl
  simp only [Fin.is_lt, true_and] at h
  rw [h, parity, parityOn]

/-- Explicit `ZMod q ≃ Fin q` equivalence for `NeZero q`. -/
private def zmodEquivFin (q : ℕ) [NeZero q] : ZMod q ≃ Fin q where
  toFun a := ⟨a.val, ZMod.val_lt a⟩
  invFun i := (i.1 : ZMod q)
  left_inv a := ZMod.natCast_zmod_val a
  right_inv i := Fin.ext (ZMod.val_natCast_of_lt i.2)

/-- The concrete design underlying `nwAC0Gen d c M`. -/
private noncomputable def nwAC0Design (d c M : ℕ) :
    Design (nwAC0SeedLen d c M) (nwAC0Prime d c M) (nwAC0IndexBits M - 1) M :=
  let q := nwAC0Prime d c M
  have hpr : q.Prime := (leastPrimeGe_spec (by dsimp [nwAC0PrimeLower]; omega)).1
  have : Fact q.Prime := ⟨hpr⟩
  have : NeZero q := ⟨hpr.ne_zero⟩
  let Dfull := Design.bitPolynomial (nwAC0IndexBits M)
    (zmodEquivFin q).symm.toEmbedding (zmodEquivFin q)
  Dfull.subfamily (Fin.castLEEmb (by
    dsimp [nwAC0IndexBits]
    exact (Nat.lt_size_self M).le.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))))

/-- `nwAC0Gen d c M` agrees pointwise with
`NisanWigderson.generator (nwAC0Design d c M) (parity q)`. -/
private theorem nwAC0Gen_eq_generator (d c M : ℕ) (s : BitString (nwAC0SeedLen d c M)) :
    nwAC0Gen d c M s = generator (nwAC0Design d c M) (parity (nwAC0Prime d c M)) s := by
  set q := nwAC0Prime d c M
  have hpr : q.Prime := (leastPrimeGe_spec (by dsimp [nwAC0PrimeLower]; omega)).1
  have : Fact q.Prime := ⟨hpr⟩
  have : NeZero q := ⟨hpr.ne_zero⟩
  funext i
  have hi_lt : i.1 < 2 ^ nwAC0IndexBits M :=
    i.2.trans_le ((Nat.lt_size_self M).le.trans
      (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)))
  simp only [nwAC0Gen, nwAC0Bit, generator_apply]
  have hmap :
      ((List.range q).map fun j =>
        (List.ofFn s).getD (j * q + polyEvalMod (nwAC0IndexBits M) i.1 j q) false) =
      ((List.range q).map fun j =>
        if h : j < q then (nwAC0Design d c M).restrict i s ⟨j, h⟩ else false) := by
    refine List.map_congr_left fun j hj => ?_
    have hjlt : j < q := List.mem_range.mp hj
    simp only [hjlt, ↓reduceDIte]
    have hpe_lt : polyEvalMod (nwAC0IndexBits M) i.1 j q < q := polyEvalMod_lt hpr.pos
    have hidx_lt : j * q + polyEvalMod (nwAC0IndexBits M) i.1 j q < nwAC0SeedLen d c M := by
      have h1 : j * q + q ≤ q * q := by
        calc j * q + q = (j + 1) * q := by ring
          _ ≤ q * q := Nat.mul_le_mul_right q hjlt
      change j * q + polyEvalMod (nwAC0IndexBits M) i.1 j q < q * q
      omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hidx_lt, ↓reduceDIte,
      Option.getD_some]
    -- Show `s ⟨j * q + polyEvalMod ..., hidx_lt⟩ = (nwAC0Design d c M).restrict i s ⟨j, hjlt⟩`.
    symm
    have hres := Design.restrict_bitPolynomial (ℓ := nwAC0IndexBits M)
      (r := (zmodEquivFin q).symm.toEmbedding) (num := zmodEquivFin q)
      ⟨i.1, hi_lt⟩ (s : Fin (q * q) → Bool) ⟨j, hjlt⟩
    change ((Design.bitPolynomial (nwAC0IndexBits M)
      (zmodEquivFin q).symm.toEmbedding (zmodEquivFin q)).restrict ⟨i.1, hi_lt⟩
      (s : Fin (q * q) → Bool) ⟨j, hjlt⟩) = _
    rw [hres]
    congr 1
    apply Fin.ext
    change (finProdFinEquiv
      (⟨j, hjlt⟩, zmodEquivFin q
        (bitPoly ((BitString.equivFin (nwAC0IndexBits M)).symm ⟨i.1, hi_lt⟩)
          ((zmodEquivFin q).symm ⟨j, hjlt⟩)))).1 = j * q + polyEvalMod (nwAC0IndexBits M) i.1 j q
    rw [finProdFinEquiv_apply_val]
    dsimp only
    have hval_eq :
      (zmodEquivFin q (bitPoly ((BitString.equivFin (nwAC0IndexBits M)).symm ⟨i.1, hi_lt⟩)
        ((zmodEquivFin q).symm ⟨j, hjlt⟩))).1 = polyEvalMod (nwAC0IndexBits M) i.1 j q := by
      have hz : bitPoly ((BitString.equivFin (nwAC0IndexBits M)).symm ⟨i.1, hi_lt⟩)
          ((zmodEquivFin q).symm ⟨j, hjlt⟩) =
          (polyEvalMod (nwAC0IndexBits M) i.1 j q : ZMod q) := by
        rw [polyEvalMod_eq_zmod_val hpr.pos]
        unfold bitPoly
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [equivFin_symm_eq_testBit]
        rfl
      rw [hz]
      exact ZMod.val_natCast_of_lt hpe_lt
    rw [hval_eq]
    ring
  rw [hmap, foldl_xor_range_eq_parity]

/-! #### Polynomial-time computability of `nwAC0Bit` -/

private theorem computableInPolyTime_isPrimeBool :
    ComputableInPolyTime isPrimeBool encUnary encBool := by
  have hge2 : ComputableInPolyTime (fun p : ℕ => decide (2 ≤ p)) encUnary encBool := by
    have h := unary_le' (const (encIn := encUnary) 2) id'
    exact h
  have hall : ComputableInPolyTime
      (fun p : ℕ => (List.range p).all fun d => decide (d < 2) || decide (p % d ≠ 0))
      encUnary encBool := by
    refine allWithInput (encIn := encUnary) (range.comp id') ?_
    have hlt2 : ComputableInPolyTime (fun pd : ℕ × ℕ => decide (pd.2 < 2))
        (encPair encUnary encUnary) encBool :=
      unary_lt' (snd encUnary encUnary) (const 2)
    have hmod : ComputableInPolyTime (fun pd : ℕ × ℕ => pd.1 % pd.2)
        (encPair encUnary encUnary) encNat :=
      binary_mod.comp ((unary_to_binary.comp (fst encUnary encUnary)).prod
        (unary_to_binary.comp (snd encUnary encUnary)))
    have hne0 : ComputableInPolyTime (fun pd : ℕ × ℕ => decide (pd.1 % pd.2 ≠ 0))
        (encPair encUnary encUnary) encBool := by
      have h := bool_not.comp (decide_eq' hmod (const 0))
      convert h using 1
      funext pd; simp
    exact bool_or.comp (hlt2.prod hne0)
  exact bool_and.comp (hge2.prod hall)

private theorem computableInPolyTime_leastPrimeGe :
    ComputableInPolyTime leastPrimeGe encUnary encUnary := by
  have hcomp : ComputableInPolyTime (fun p : ℕ × ℕ => isPrimeBool (p.1 + p.2))
      (encPair encUnary encUnary) encBool := computableInPolyTime_isPrimeBool.comp unary_add
  have hfind : ComputableInPolyTime
      (fun L : ℕ => (List.range (L + 1)).find? fun off => isPrimeBool (L + off))
      encUnary (encOption encUnary) :=
    findWithInput (encIn := encUnary) (range.comp (unary_add' id' (const 1))) hcomp
  have hget : ComputableInPolyTime
      (fun L : ℕ => ((List.range (L + 1)).find? fun off => isPrimeBool (L + off)).getD 0)
      encUnary encUnary :=
    optionGetDWithInput hfind (const 0)
  exact unary_add' id' hget

private theorem computableInPolyTime_polyEvalMod :
    ComputableInPolyTime
      (fun p : ((ℕ × ℕ) × ℕ) × ℕ => polyEvalMod p.1.1.1 p.1.1.2 p.1.2 p.2)
      (encPair (encPair (encPair encUnary encNat) encUnary) encUnary) encUnary := by
  let encP := encPair (encPair (encPair encUnary encNat) encUnary) encUnary
  let step : (((ℕ × ℕ) × ℕ) × ℕ) → (ℕ × ℕ) → ℕ → (ℕ × ℕ) :=
    fun par st t =>
      let i := par.1.1.2
      let j := par.1.2
      let m := max 1 par.2
      (if i.testBit t then (st.1 + st.2) % m else st.1, (st.2 * j) % m)
  have hstep : ComputableInPolyTime
      (fun x : ((((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ => step x.1.1 x.1.2 x.2)
      (encPair (encPair encP (encPair encUnary encUnary)) encUnary)
      (encPair encUnary encUnary) := by
    let encIn := encPair (encPair encP (encPair encUnary encUnary)) encUnary
    have hpar : ComputableInPolyTime (fun x : ((((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ => x.1.1)
        encIn encP := (fst encP _).comp (fst _ _)
    have hst : ComputableInPolyTime (fun x : ((((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ => x.1.2)
        encIn (encPair encUnary encUnary) := (snd encP _).comp (fst _ _)
    have ht : ComputableInPolyTime (fun x : ((((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ => x.2)
        encIn encUnary := snd _ _
    have hi : ComputableInPolyTime (fun x : ((((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ => x.1.1.1.1.2)
        encIn encNat :=
      (snd encUnary encNat).comp ((fst _ encUnary).comp ((fst _ encUnary).comp hpar))
    have hj : ComputableInPolyTime (fun x : ((((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ => x.1.1.1.2)
        encIn encUnary := (snd _ encUnary).comp ((fst _ encUnary).comp hpar)
    have hm : ComputableInPolyTime
        (fun x : ((((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ => max 1 x.1.1.2)
        encIn encUnary :=
      unary_max.comp ((const 1).prod ((snd _ encUnary).comp hpar))
    have hst1 : ComputableInPolyTime (fun x : ((((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ => x.1.2.1)
        encIn encUnary := (fst encUnary encUnary).comp hst
    have hst2 : ComputableInPolyTime (fun x : ((((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ => x.1.2.2)
        encIn encUnary := (snd encUnary encUnary).comp hst
    have htb : ComputableInPolyTime
        (fun x : ((((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ => x.1.1.1.1.2.testBit x.2)
        encIn encBool := binary_testBit hi ht
    have hsum_mod_bin : ComputableInPolyTime
        (fun x : ((((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ => (x.1.2.1 + x.1.2.2) % max 1 x.1.1.2)
        encIn encNat :=
      binary_mod.comp ((unary_to_binary.comp (unary_add' hst1 hst2)).prod
        (unary_to_binary.comp hm))
    have hsum_mod : ComputableInPolyTime
        (fun x : ((((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ => (x.1.2.1 + x.1.2.2) % max 1 x.1.1.2)
        encIn encUnary :=
      binary_to_unary_bounded hsum_mod_bin (unary_add' hst1 hst2) (fun _ => Nat.mod_le _ _)
    have hmul_mod_bin : ComputableInPolyTime
        (fun x : ((((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ => (x.1.2.2 * x.1.1.1.2) % max 1 x.1.1.2)
        encIn encNat :=
      binary_mod.comp ((unary_to_binary.comp (unary_mul' hst2 hj)).prod
        (unary_to_binary.comp hm))
    have hmul_mod : ComputableInPolyTime
        (fun x : ((((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ => (x.1.2.2 * x.1.1.1.2) % max 1 x.1.1.2)
        encIn encUnary :=
      binary_to_unary_bounded hmul_mod_bin (unary_mul' hst2 hj) (fun _ => Nat.mod_le _ _)
    have hacc : ComputableInPolyTime
        (fun x : ((((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ =>
          if x.1.1.1.1.2.testBit x.2 then (x.1.2.1 + x.1.2.2) % max 1 x.1.1.2 else x.1.2.1)
        encIn encUnary := ite' htb hsum_mod hst1
    exact hacc.prod hmul_mod
  have hinit : ComputableInPolyTime
      (fun p : ((ℕ × ℕ) × ℕ) × ℕ => (0, 1 % max 1 p.2)) encP (encPair encUnary encUnary) := by
    have hm : ComputableInPolyTime (fun p : ((ℕ × ℕ) × ℕ) × ℕ => max 1 p.2) encP encUnary :=
      unary_max.comp ((const 1).prod (snd _ encUnary))
    have h1mod_bin : ComputableInPolyTime
        (fun p : ((ℕ × ℕ) × ℕ) × ℕ => 1 % max 1 p.2) encP encNat :=
      binary_mod.comp ((const 1).prod (unary_to_binary.comp hm))
    have h1mod : ComputableInPolyTime
        (fun p : ((ℕ × ℕ) × ℕ) × ℕ => 1 % max 1 p.2) encP encUnary :=
      binary_to_unary_bounded h1mod_bin (const 1) (fun _ => Nat.mod_le _ _)
    exact (const 0).prod h1mod
  have hlist : ComputableInPolyTime
      (fun p : ((ℕ × ℕ) × ℕ) × ℕ => List.range p.1.1.1) encP (encList encUnary) :=
    range.comp ((fst encUnary encNat).comp ((fst _ encUnary).comp (fst _ encUnary)))
  have hfold : ComputableInPolyTime
      (fun p : ((ℕ × ℕ) × ℕ) × ℕ => (List.range p.1.1.1).foldl (step p) (0, 1 % max 1 p.2))
      encP (encPair encUnary encUnary) := by
    refine foldlWith (encIn := encP) (encA := encUnary) (encB := encPair encUnary encUnary)
      (encL := encList encUnary) (encP := encP)
      id' hlist hinit hstep (B := fun p => 3 * (p.2 + 1) + 5) ?_ ?_
    · have hq : ComputableInPolyTime (fun p : ((ℕ × ℕ) × ℕ) × ℕ => 3 * (p.2 + 1) + 5)
          encP encUnary := by
        have hq0 := snd (encPair (encPair encUnary encNat) encUnary) encUnary
        exact unary_add' (unary_mul' (const 3) (unary_add' hq0 (const 1))) (const 5)
      exact hq.polyBounded
    · intro p idx _
      have hbd : ∀ l : List ℕ,
          let r := l.foldl (step p) (0, 1 % max 1 p.2)
          r.1 ≤ max 1 p.2 ∧ r.2 ≤ max 1 p.2 := by
        intro l
        induction l using List.reverseRecOn with
        | nil =>
          simp only [List.foldl_nil]
          exact ⟨Nat.zero_le _, (Nat.mod_lt 1 (by omega)).le⟩
        | append_singleton l a ih =>
          rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
          dsimp only [step]
          have hmpos : 0 < max 1 p.2 := by omega
          refine ⟨?_, (Nat.mod_lt _ hmpos).le⟩
          split_ifs
          · exact (Nat.mod_lt _ hmpos).le
          · exact ih.1
      have h := hbd ((List.range p.1.1.1).take idx)
      dsimp only at h
      simp only [length_encPair, encUnary_apply, List.length_replicate]
      omega
  exact (fst encUnary encUnary).comp hfold

/-- Computing `nwAC0Prime d c M` in unary from `M` in binary runs in `poly(log M)` time. -/
theorem computableInPolyTime_nwAC0Prime (d c : ℕ) :
    ComputableInPolyTime (nwAC0Prime d c) encNat encUnary := by
  have hℓ : ComputableInPolyTime nwAC0IndexBits encNat encUnary :=
    unary_max.comp ((const 1).prod binary_size)
  have hs : ComputableInPolyTime (nwAC0HastadParam c) encNat encUnary := by
    unfold nwAC0HastadParam
    exact unary_add' (unary_add' (unary_mul' (const (c + 4)) hℓ) (const c)) (const 20)
  have hL : ComputableInPolyTime (nwAC0PrimeLower d c) encNat encUnary := by
    unfold nwAC0PrimeLower
    have h16 : ComputableInPolyTime (fun M => 16 * nwAC0HastadParam c M + 1) encNat encUnary :=
      unary_add' (unary_mul' (const 16) hs) (const 1)
    have hpow : ComputableInPolyTime
        (fun M => (16 * nwAC0HastadParam c M + 1) ^ (d + 1)) encNat encUnary :=
      (unary_pow (d + 1)).comp h16
    exact unary_add' (unary_mul' (unary_mul' (const 17) hs) hpow) (const 17)
  exact computableInPolyTime_leastPrimeGe.comp hL

/-- Computing `nwAC0SeedLen d c M` in unary from `M` in binary runs in `poly(log M)` time. -/
theorem computableInPolyTime_nwAC0SeedLen (d c : ℕ) :
    ComputableInPolyTime (nwAC0SeedLen d c) encNat encUnary :=
  unary_mul' (computableInPolyTime_nwAC0Prime d c) (computableInPolyTime_nwAC0Prime d c)

/-- **Bit-computability of `nwAC0Gen`:**
on inputs `(M, i, seed)` with `M, i` in binary (`encNat`) and `seed` in raw bits, `nwAC0Bit d c`
computes the `i`-th bit of `nwAC0Gen d c M seed` in time `poly(log M + log i + |seed|)`. -/
theorem computableInPolyTime_nwAC0Bit (d c : ℕ) :
    ComputableInPolyTime (nwAC0Bit d c) (encPair encNat (encPair encNat encBits)) encBool := by
  let encIn := encPair encNat (encPair encNat encBits)
  have hM : ComputableInPolyTime (fun x : ℕ × ℕ × List Bool => x.1) encIn encNat := fst _ _
  have hi : ComputableInPolyTime (fun x : ℕ × ℕ × List Bool => x.2.1) encIn encNat :=
    (fst encNat encBits).comp (snd _ _)
  have hseed : ComputableInPolyTime (fun x : ℕ × ℕ × List Bool => x.2.2) encIn encBits :=
    (snd encNat encBits).comp (snd _ _)
  have hℓ : ComputableInPolyTime (fun x : ℕ × ℕ × List Bool => nwAC0IndexBits x.1) encIn encUnary :=
    (unary_max.comp ((const 1).prod binary_size)).comp hM
  have hq : ComputableInPolyTime (fun x : ℕ × ℕ × List Bool => nwAC0Prime d c x.1) encIn encUnary :=
    (computableInPolyTime_nwAC0Prime d c).comp hM
  have hrowBits : ComputableInPolyTime
      (fun x : ℕ × ℕ × List Bool =>
        (List.range (nwAC0Prime d c x.1)).map fun j =>
          x.2.2.getD (j * nwAC0Prime d c x.1 + polyEvalMod (nwAC0IndexBits x.1) x.2.1 j
            (nwAC0Prime d c x.1)) false)
      encIn encBits := by
    refine mapToBitsWithInput (range.comp hq) ?_
    let encPairJ := encPair encIn encUnary
    have hx : ComputableInPolyTime (fun y : (ℕ × ℕ × List Bool) × ℕ => y.1) encPairJ encIn :=
      fst _ _
    have hj : ComputableInPolyTime (fun y : (ℕ × ℕ × List Bool) × ℕ => y.2) encPairJ encUnary :=
      snd _ _
    have hq' : ComputableInPolyTime
        (fun y : (ℕ × ℕ × List Bool) × ℕ => nwAC0Prime d c y.1.1) encPairJ encUnary := hq.comp hx
    have hℓ' : ComputableInPolyTime
        (fun y : (ℕ × ℕ × List Bool) × ℕ => nwAC0IndexBits y.1.1) encPairJ encUnary := hℓ.comp hx
    have hi' : ComputableInPolyTime
        (fun y : (ℕ × ℕ × List Bool) × ℕ => y.1.2.1) encPairJ encNat := hi.comp hx
    have hseed' : ComputableInPolyTime
        (fun y : (ℕ × ℕ × List Bool) × ℕ => y.1.2.2) encPairJ encBits := hseed.comp hx
    have hpe : ComputableInPolyTime
        (fun y : (ℕ × ℕ × List Bool) × ℕ =>
          polyEvalMod (nwAC0IndexBits y.1.1) y.1.2.1 y.2 (nwAC0Prime d c y.1.1))
        encPairJ encUnary :=
      computableInPolyTime_polyEvalMod.comp (((hℓ'.prod hi').prod hj).prod hq')
    have hidx : ComputableInPolyTime
        (fun y : (ℕ × ℕ × List Bool) × ℕ =>
          y.2 * nwAC0Prime d c y.1.1 +
            polyEvalMod (nwAC0IndexBits y.1.1) y.1.2.1 y.2 (nwAC0Prime d c y.1.1))
        encPairJ encUnary :=
      unary_add' (unary_mul' hj hq') hpe
    exact bitsGetDWithInput hseed' hidx false
  exact bitsFoldlWithInput (fun acc b => acc ^^ b) hrowBits (const false)

/-! #### Seed-length bound and Fooling Polynomial-Size Constant-Depth Circuits -/

/-- Seed length bound: `nwAC0SeedLen d c M ≤ C * (Nat.log 2 M + 1) ^ (2 * d + 6)` (in fact
`O((log M)^{2d + 4})`). -/
theorem nwAC0SeedLen_le (d c : ℕ) :
    ∃ C : ℕ, ∀ M : ℕ,
      nwAC0SeedLen d c M ≤ C * (Nat.log 2 M + 1) ^ (2 * d + 6) := by
  let A := 16 * (2 * c + 24) + 1
  let B0 := 17 * (2 * c + 24) * A ^ (d + 1) + 17
  let B := 2 * B0
  refine ⟨B * B, fun M => ?_⟩
  have hℓ : nwAC0IndexBits M ≤ Nat.log 2 M + 1 := by
    dsimp [nwAC0IndexBits]
    have hsz : M.size ≤ Nat.log 2 M + 1 :=
      Nat.size_le.mpr (Nat.lt_pow_succ_log_self (by norm_num) M)
    omega
  have hs : nwAC0HastadParam c M ≤ (2 * c + 24) * (Nat.log 2 M + 1) := by
    dsimp [nwAC0HastadParam]
    have h1 : 1 ≤ Nat.log 2 M + 1 := by omega
    nlinarith
  have hL : nwAC0PrimeLower d c M ≤ B0 * (Nat.log 2 M + 1) ^ (d + 2) := by
    dsimp [nwAC0PrimeLower]
    set L0 := Nat.log 2 M + 1
    have hL0_pos : 1 ≤ L0 := by omega
    have h16 : 16 * nwAC0HastadParam c M + 1 ≤ A * L0 := by
      dsimp [A]; nlinarith
    have hpow : (16 * nwAC0HastadParam c M + 1) ^ (d + 1) ≤ A ^ (d + 1) * L0 ^ (d + 1) := by
      calc _ ≤ (A * L0) ^ (d + 1) := Nat.pow_le_pow_left h16 (d + 1)
        _ = A ^ (d + 1) * L0 ^ (d + 1) := mul_pow A L0 (d + 1)
    have hprod : 17 * nwAC0HastadParam c M * (16 * nwAC0HastadParam c M + 1) ^ (d + 1) ≤
        17 * (2 * c + 24) * A ^ (d + 1) * L0 ^ (d + 2) := by
      calc _ ≤ 17 * ((2 * c + 24) * L0) * (A ^ (d + 1) * L0 ^ (d + 1)) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left 17 hs) hpow
        _ = 17 * (2 * c + 24) * A ^ (d + 1) * (L0 * L0 ^ (d + 1)) := by ring
        _ = 17 * (2 * c + 24) * A ^ (d + 1) * L0 ^ (d + 2) := by rw [← pow_succ']
    have h1_le : 1 ≤ L0 ^ (d + 2) := Nat.one_le_pow _ _ hL0_pos
    dsimp [B0]
    rw [add_mul]
    have h17 : 17 ≤ 17 * L0 ^ (d + 2) := Nat.le_mul_of_pos_right 17 h1_le
    omega
  have hq : nwAC0Prime d c M ≤ B * (Nat.log 2 M + 1) ^ (d + 2) := by
    have hspec := leastPrimeGe_spec (L := nwAC0PrimeLower d c M) (by dsimp [nwAC0PrimeLower]; omega)
    calc nwAC0Prime d c M ≤ 2 * nwAC0PrimeLower d c M := hspec.2.2
      _ ≤ 2 * (B0 * (Nat.log 2 M + 1) ^ (d + 2)) := Nat.mul_le_mul_left 2 hL
      _ = B * (Nat.log 2 M + 1) ^ (d + 2) := by dsimp [B]; ring
  have hpow_le : (Nat.log 2 M + 1) ^ (2 * d + 4) ≤ (Nat.log 2 M + 1) ^ (2 * d + 6) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  calc nwAC0SeedLen d c M = nwAC0Prime d c M * nwAC0Prime d c M := rfl
    _ ≤ (B * (Nat.log 2 M + 1) ^ (d + 2)) * (B * (Nat.log 2 M + 1) ^ (d + 2)) :=
        Nat.mul_le_mul hq hq
    _ = B * B * (Nat.log 2 M + 1) ^ (2 * d + 4) := by
        rw [show 2 * d + 4 = (d + 2) + (d + 2) by omega, pow_add]; ring
    _ ≤ B * B * (Nat.log 2 M + 1) ^ (2 * d + 6) := Nat.mul_le_mul_left _ hpow_le

/-- **Nisan–Wigderson PRG for constant-depth circuits:**
for every constant depth `d` and polynomial size bound `c * (M + 1) ^ c`, `nwAC0Gen d c` has
seed length `O((log M)^{2d + 6})` (in fact `O((log M)^{2d + 4})`), bit-computability in
`poly(log M)` time (`computableInPolyTime_nwAC0Bit`), and fools every depth-`d`,
size-`≤ c * (M + 1) ^ c` unbounded fan-in circuit `G` within `1 / 100`. -/
theorem nwAC0Gen_fools_circuit (d c M : ℕ) (hM : 0 < M) (G : Circuit Unbounded.signature M 1)
    (hGd : G.depth ≤ d) (hGs : G.size ≤ c * (M + 1) ^ c) :
    |((uniformOfFintype (BitString (nwAC0SeedLen d c M))).toOuterMeasure
        {s | G.eval Unbounded.interpretation (nwAC0Gen d c M s) 0 = true}).toReal -
      ((uniformOfFintype (BitString M)).toOuterMeasure
        {z | G.eval Unbounded.interpretation z 0 = true}).toReal| < 1 / 100 := by
  let D := nwAC0Design d c M
  let q := nwAC0Prime d c M
  let s := nwAC0HastadParam c M
  let ℓ := nwAC0IndexBits M
  have hs2 : 2 ≤ s := by dsimp [s, nwAC0HastadParam]; omega
  have hGdw : G.depthWith Unbounded.andOrCost ≤ d :=
    (Circuit.depthWith_le_depth Unbounded.andOrCost_le_one G).trans hGd
  have hq_spec := leastPrimeGe_spec (L := nwAC0PrimeLower d c M) (by dsimp [nwAC0PrimeLower]; omega)
  have hq_cond : s * (16 * s + 1) ^ (d + 1) ≤ q / 17 := by
    have hL : 17 * (s * (16 * s + 1) ^ (d + 1)) ≤ q := by
      have hspec := hq_spec.2.1
      change nwAC0PrimeLower d c M ≤ q at hspec
      dsimp only [nwAC0PrimeLower, s] at hspec ⊢
      linarith
    exact (Nat.le_div_iff_mul_le (by norm_num)).mpr (by linarith)
  have hadv := nw_unbounded_advantage_le D hM G hs2 hGdw hq_cond
  -- Connect `realExperiment` / `idealExperiment` to `toOuterMeasure`.
  have hreal_eq :
      ((generator D (parity q)).realExperiment
        (fun y => _root_.PMF.pure (G.eval Unbounded.interpretation y 0)) true).toReal =
      ((uniformOfFintype (BitString (nwAC0SeedLen d c M))).toOuterMeasure
        {s | G.eval Unbounded.interpretation (nwAC0Gen d c M s) 0 = true}).toReal := by
    rw [toOuterMeasure_apply_toReal]
    have h1 : ((generator D (parity q)).realExperiment
        (fun y => _root_.PMF.pure (G.eval Unbounded.interpretation y 0)) true) =
        ∑ seed : BitString (nwAC0SeedLen d c M),
          if G.eval Unbounded.interpretation (nwAC0Gen d c M seed) 0 = true
          then uniformOfFintype (BitString (nwAC0SeedLen d c M)) seed else 0 := by
      simp only [Generator.realExperiment, Generator.outputDist, _root_.PMF.bind_map,
        _root_.PMF.bind_apply, tsum_fintype, nwAC0Gen_eq_generator]
      refine Finset.sum_congr rfl fun seed _ => ?_
      dsimp only [D, q]
      cases h : G.eval Unbounded.interpretation
          (generator (nwAC0Design d c M) (parity (nwAC0Prime d c M)) seed) 0 <;>
        simp [h, _root_.PMF.pure_apply]
    rw [h1, ENNReal.toReal_sum fun seed _ => by split_ifs <;> simp]
    refine Finset.sum_congr rfl fun seed _ => by
      simp only [Set.mem_ofPred_eq]
      split_ifs <;> simp
  have hideal_eq :
      (Generator.idealExperiment
        (fun y => _root_.PMF.pure (G.eval Unbounded.interpretation y 0)) true).toReal =
      ((uniformOfFintype (BitString M)).toOuterMeasure
        {z | G.eval Unbounded.interpretation z 0 = true}).toReal := by
    rw [toOuterMeasure_apply_toReal]
    have h1 : (Generator.idealExperiment
        (fun y => _root_.PMF.pure (G.eval Unbounded.interpretation y 0)) true) =
        ∑ z : BitString M,
          if G.eval Unbounded.interpretation z 0 = true
          then uniformOfFintype (BitString M) z else 0 := by
      simp only [Generator.idealExperiment, _root_.PMF.bind_apply, tsum_fintype]
      refine Finset.sum_congr rfl fun z _ => ?_
      cases G.eval Unbounded.interpretation z 0 <;> simp [_root_.PMF.pure_apply]
    rw [h1, ENNReal.toReal_sum fun z _ => by split_ifs <;> simp]
    refine Finset.sum_congr rfl fun z _ => by
      simp only [Set.mem_ofPred_eq]
      split_ifs <;> simp
  rw [hreal_eq, hideal_eq] at hadv
  refine hadv.trans_lt ?_
  -- Numeric check: `100 * M * (G.size + M * (2^(ℓ - 1) * ℓ + 1) + 2) < 2^(s + 1)`.
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  have hM_lt : M < 2 ^ ℓ :=
    (Nat.lt_size_self M).trans_le (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
  have hM1_le : M + 1 ≤ 2 ^ ℓ := hM_lt
  have hℓ_le : ℓ ≤ 2 ^ ℓ := Nat.lt_two_pow_self.le
  have hGs_pow : G.size ≤ 2 ^ (c * ℓ + c) := by
    have hc_le : c ≤ 2 ^ c := Nat.lt_two_pow_self.le
    calc G.size ≤ c * (M + 1) ^ c := hGs
      _ ≤ 2 ^ c * (2 ^ ℓ) ^ c := Nat.mul_le_mul hc_le (Nat.pow_le_pow_left hM1_le c)
      _ = 2 ^ (c * ℓ + c) := by rw [← pow_mul, ← pow_add, mul_comm ℓ c, add_comm]
  have h2a_le : 2 ^ (ℓ - 1) * (ℓ - 1 + 1) + 1 ≤ 2 ^ (2 * ℓ) + 1 := by
    have h1 : 2 ^ (ℓ - 1) ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
    have h2 : ℓ - 1 + 1 = ℓ := Nat.sub_add_cancel (le_max_left 1 M.size)
    rw [h2]
    have h3 : 2 ^ (ℓ - 1) * ℓ ≤ 2 ^ ℓ * 2 ^ ℓ := Nat.mul_le_mul h1 hℓ_le
    rw [← pow_add, ← two_mul] at h3
    omega
  have hMterm : M * (2 ^ (ℓ - 1) * (ℓ - 1 + 1) + 1) ≤ 2 * 2 ^ (3 * ℓ) := by
    have h1 : M * (2 ^ (ℓ - 1) * (ℓ - 1 + 1) + 1) ≤ 2 ^ ℓ * (2 ^ (2 * ℓ) + 1) :=
      Nat.mul_le_mul hM_lt.le h2a_le
    have h2 : 1 ≤ 2 ^ (2 * ℓ) := Nat.one_le_two_pow
    have h3 : 2 ^ ℓ * (2 ^ (2 * ℓ) + 1) ≤ 2 ^ ℓ * (2 * 2 ^ (2 * ℓ)) :=
      Nat.mul_le_mul_left _ (by omega)
    have h4 : 2 ^ ℓ * (2 * 2 ^ (2 * ℓ)) = 2 * 2 ^ (3 * ℓ) := by
      rw [show 3 * ℓ = ℓ + 2 * ℓ by ring, pow_add]; ring
    omega
  have hnum : M * (G.size + M * (2 ^ (ℓ - 1) * (ℓ - 1 + 1) + 1) + 2) * 100 < 2 ^ (s + 1) := by
    have hbig : G.size + M * (2 ^ (ℓ - 1) * (ℓ - 1 + 1) + 1) + 2 ≤
        5 * 2 ^ ((c + 3) * ℓ + c) := by
      have h1 : 2 ^ (c * ℓ + c) ≤ 2 ^ ((c + 3) * ℓ + c) :=
        Nat.pow_le_pow_right (by norm_num) (by nlinarith)
      have h2 : 2 ^ (3 * ℓ) ≤ 2 ^ ((c + 3) * ℓ + c) :=
        Nat.pow_le_pow_right (by norm_num) (by nlinarith)
      have h3 : 1 ≤ 2 ^ ((c + 3) * ℓ + c) := Nat.one_le_two_pow
      omega
    set E := (c + 4) * ℓ + c
    calc M * (G.size + M * (2 ^ (ℓ - 1) * (ℓ - 1 + 1) + 1) + 2) * 100
        ≤ 2 ^ ℓ * (5 * 2 ^ ((c + 3) * ℓ + c)) * 100 :=
          Nat.mul_le_mul_right 100 (Nat.mul_le_mul hM_lt.le hbig)
      _ = 500 * 2 ^ E := by
          have hE : E = ℓ + ((c + 3) * ℓ + c) := by dsimp [E]; ring
          rw [hE, pow_add 2 ℓ ((c + 3) * ℓ + c)]; ring
      _ < 2 ^ (s + 1) := by
          have hsE : s + 1 = E + 21 := rfl
          rw [hsE, pow_add 2 E 21]
          have h21 : (2 : ℕ) ^ 21 = 2097152 := by norm_num
          have hpos : 1 ≤ 2 ^ E := Nat.one_le_two_pow
          rw [h21]; omega
  have hnum_r : ((M * (G.size + M * (2 ^ (ℓ - 1) * (ℓ - 1 + 1) + 1) + 2) * 100 : ℕ) : ℝ) <
      ((2 ^ (s + 1) : ℕ) : ℝ) := by exact_mod_cast hnum
  dsimp only [D, nwAC0Design, ℓ, s] at hnum_r ⊢
  push_cast at hnum_r ⊢
  linarith

/-! ### Part 4: Support-Size Barrier Against Subexponential Circuit Sizes -/

private lemma toOuterMeasure_univ_toReal {α : Type*} [Finite α] (p : _root_.PMF α) :
    (p.toOuterMeasure Set.univ).toReal = 1 := by
  have := Fintype.ofFinite α
  rw [_root_.PMF.toOuterMeasure_apply_fintype]
  simp only [Set.indicator_univ]
  have hts := p.tsum_coe
  rw [tsum_fintype] at hts
  rw [hts, ENNReal.toReal_one]

/-- **Support-size barrier for polylogarithmic-seed PRGs:**
for any depth parameter `d`, any constant `α > 0`, any seed
constant `C`, and any generator family `G` mapping `{0,1}^{C (⌊log₂ n⌋ + 1)^{2d+6}} → {0,1}^n`,
there exists a length `n` and a depth-2 (in `andOrCost`; raw depth `≤ 3`) circuit `D` of size
`≤ 2^{n^α}` that accepts every output of `G n` with probability `1` and uniform strings with
probability at most `1 / 2`, distinguishing `G n` with advantage at least `1 / 2 > 1 / 100`. -/
theorem nwAC0Gen_expSize_barrier (d C : ℕ) {α : ℝ} (hα : 0 < α)
    (G : ∀ n : ℕ, BitString (C * (Nat.log 2 n + 1) ^ (2 * d + 6)) → BitString n) :
    ∃ (n : ℕ) (D : Circuit Unbounded.signature n 1),
      0 < n ∧ D.depthWith Unbounded.andOrCost ≤ 2 ∧ D.depth ≤ 3 ∧
      (D.size : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) ^ α) ∧
      (1 / 100 : ℝ) <
        |((uniformOfFintype (BitString (C * (Nat.log 2 n + 1) ^ (2 * d + 6)))).toOuterMeasure
            {s | D.eval Unbounded.interpretation (G n s) 0 = true}).toReal -
          ((uniformOfFintype (BitString n)).toOuterMeasure
            {z | D.eval Unbounded.interpretation z 0 = true}).toReal| := by
  classical
  -- Choose `n = 2^m` with `m` large enough that `seedLen(n) + 1 ≤ n` and
  -- `seedLen(n) + m + 3 ≤ 2^(α * m) = n^α`.
  let K : ℕ := 2 * d + 6
  -- Show `(C * (m + 1)^K + m + 3 : ℝ) ≤ 2^(α * m)` and `C * (m + 1)^K + 1 ≤ 2^m` for large `m`.
  have hev1 : ∀ᶠ m : ℕ in Filter.atTop,
      ((C * (m + 1) ^ K + m + 3 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (α * (m : ℝ)) := by
    have hlim : Filter.Tendsto (fun m : ℕ => ((C * (m + 1) ^ K + m + 3 : ℕ) : ℝ) /
        ((2 : ℝ) ^ α) ^ m) Filter.atTop (nhds 0) := by
      have h1lt : 1 < (2 : ℝ) ^ α := Real.one_lt_rpow (by norm_num) hα
      have hpoly : Filter.Tendsto (fun m : ℕ => ((m : ℝ) ^ (K + 1)) / ((2 : ℝ) ^ α) ^ m)
          Filter.atTop (nhds 0) :=
        tendsto_pow_const_div_const_pow_of_one_lt (K + 1) h1lt
      have hconst : Filter.Tendsto (fun m : ℕ => ((C * 2 ^ K + 4 : ℝ)) *
          (((m : ℝ) ^ (K + 1)) / ((2 : ℝ) ^ α) ^ m)) Filter.atTop (nhds 0) := by
        simpa using hpoly.const_mul (C * 2 ^ K + 4 : ℝ)
      refine squeeze_zero' (Filter.Eventually.of_forall fun m => by positivity) ?_ hconst
      filter_upwards [Filter.eventually_ge_atTop 1] with m hm
      rw [← mul_div_assoc]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      have hm1 : (m + 1 : ℝ) ≤ 2 * (m : ℝ) := by
        have : (1 : ℝ) ≤ m := by exact_mod_cast hm
        linarith
      have hmpow : ((m : ℝ) + 1) ^ K ≤ (2 : ℝ) ^ K * (m : ℝ) ^ K := by
        calc ((m : ℝ) + 1) ^ K ≤ (2 * (m : ℝ)) ^ K := pow_le_pow_left₀ (by positivity) hm1 K
          _ = (2 : ℝ) ^ K * (m : ℝ) ^ K := mul_pow _ _ _
      have hmK : (m : ℝ) ^ K ≤ (m : ℝ) ^ (K + 1) :=
        pow_le_pow_right₀ (by exact_mod_cast hm) (Nat.le_succ K)
      have hm1p : (m : ℝ) ≤ (m : ℝ) ^ (K + 1) := by
        have : (1 : ℝ) ≤ m := by exact_mod_cast hm
        calc (m : ℝ) = (m : ℝ) ^ 1 := (pow_one _).symm
          _ ≤ (m : ℝ) ^ (K + 1) := pow_le_pow_right₀ this (by omega)
      have h1p : (1 : ℝ) ≤ (m : ℝ) ^ (K + 1) := one_le_pow₀ (by exact_mod_cast hm)
      push_cast
      calc (C : ℝ) * ((m : ℝ) + 1) ^ K + (m : ℝ) + 3
          ≤ (C : ℝ) * ((2 : ℝ) ^ K * (m : ℝ) ^ K) + (m : ℝ) + 3 := by gcongr
        _ ≤ (C : ℝ) * ((2 : ℝ) ^ K * (m : ℝ) ^ (K + 1)) +
              (m : ℝ) ^ (K + 1) + 3 * (m : ℝ) ^ (K + 1) := by
            have hC_nn : (0 : ℝ) ≤ (C : ℝ) * (2 : ℝ) ^ K := by positivity
            have h1 : (C : ℝ) * ((2 : ℝ) ^ K * (m : ℝ) ^ K) ≤
                (C : ℝ) * ((2 : ℝ) ^ K * (m : ℝ) ^ (K + 1)) := by
              rw [← mul_assoc, ← mul_assoc]
              exact mul_le_mul_of_nonneg_left hmK hC_nn
            linarith
        _ = ((C : ℝ) * (2 : ℝ) ^ K + 4) * (m : ℝ) ^ (K + 1) := by ring
    filter_upwards [(Filter.Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1) hlim)] with m hm
    have hpos : (0 : ℝ) < ((2 : ℝ) ^ α) ^ m := by positivity
    have hle := (div_le_one hpos).mp hm
    rwa [← Real.rpow_natCast ((2 : ℝ) ^ α) m, ← Real.rpow_mul (by norm_num)] at hle
  have hev2 : ∀ᶠ m : ℕ in Filter.atTop, C * (m + 1) ^ K + 1 ≤ 2 ^ m := by
    have hlim : Filter.Tendsto (fun m : ℕ => ((C * (m + 1) ^ K + 1 : ℕ) : ℝ) / (2 : ℝ) ^ m)
        Filter.atTop (nhds 0) := by
      have hpoly : Filter.Tendsto (fun m : ℕ => ((m : ℝ) ^ K) / (2 : ℝ) ^ m)
          Filter.atTop (nhds 0) :=
        tendsto_pow_const_div_const_pow_of_one_lt K (by norm_num : (1 : ℝ) < 2)
      have hconst : Filter.Tendsto (fun m : ℕ => ((C * 2 ^ K + 1 : ℝ)) *
          (((m : ℝ) ^ K) / (2 : ℝ) ^ m)) Filter.atTop (nhds 0) := by
        simpa using hpoly.const_mul (C * 2 ^ K + 1 : ℝ)
      refine squeeze_zero' (Filter.Eventually.of_forall fun m => by positivity) ?_ hconst
      filter_upwards [Filter.eventually_ge_atTop 1] with m hm
      rw [← mul_div_assoc]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      have hm1 : (m + 1 : ℝ) ≤ 2 * (m : ℝ) := by
        have : (1 : ℝ) ≤ m := by exact_mod_cast hm
        linarith
      have hmpow : ((m : ℝ) + 1) ^ K ≤ (2 : ℝ) ^ K * (m : ℝ) ^ K := by
        calc ((m : ℝ) + 1) ^ K ≤ (2 * (m : ℝ)) ^ K := pow_le_pow_left₀ (by positivity) hm1 K
          _ = (2 : ℝ) ^ K * (m : ℝ) ^ K := mul_pow _ _ _
      have h1p : (1 : ℝ) ≤ (m : ℝ) ^ K := one_le_pow₀ (by exact_mod_cast hm)
      push_cast
      have hC_nn : (0 : ℝ) ≤ C := by positivity
      have h1 : (C : ℝ) * ((m : ℝ) + 1) ^ K ≤ (C : ℝ) * ((2 : ℝ) ^ K * (m : ℝ) ^ K) :=
        mul_le_mul_of_nonneg_left hmpow hC_nn
      linarith
    filter_upwards [(Filter.Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1) hlim)] with m hm
    have hle : ((C * (m + 1) ^ K + 1 : ℕ) : ℝ) ≤ ((2 ^ m : ℕ) : ℝ) := by
      have hpos : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
      simpa [Nat.cast_pow, Nat.cast_ofNat] using (div_le_one hpos).mp hm
    exact_mod_cast hle
  obtain ⟨m, hm1, hm2, hm_pos⟩ :=
    (hev1.and (hev2.and (Filter.eventually_ge_atTop 1))).exists
  let n : ℕ := 2 ^ m
  have hn_pos : 0 < n := Nat.two_pow_pos m
  have hlog_n : Nat.log 2 n = m := Nat.log_pow (by norm_num) m
  let ℓ : ℕ := C * (Nat.log 2 n + 1) ^ (2 * d + 6)
  have hℓ_eq : ℓ = C * (m + 1) ^ K := by simp [ℓ, K, hlog_n]
  -- Build the depth-2 range-indicator DNF over `S = Finset.univ.image (G n)`.
  let R : Finset (BitString n) := Finset.univ.image (G n)
  let eR : Fin #R ≃ {y : BitString n // y ∈ R} := R.equivFin.symm
  let lit (i : Fin n) (b : Bool) : Circuit Unbounded.signature n 1 :=
    if b then Circuit.wiring Unbounded.signature (fun _ => i)
    else Circuit.oneGate (σ := Unbounded.signature) .not (fun _ => i)
  have hlit_eval (i : Fin n) (b : Bool) (z : BitString n) :
      (lit i b).eval Unbounded.interpretation z 0 = decide (z i = b) := by
    cases b <;> simp [lit]
  have hlit_dw (i : Fin n) (b : Bool) : (lit i b).depthWith andOrCost = 0 := by
    cases b
    · simp [lit]
    · simp [lit, Circuit.depthWith_wiring]
  have hlit_d (i : Fin n) (b : Bool) : (lit i b).depth ≤ 1 := by
    cases b <;> simp [lit]
  have hlit_sz (i : Fin n) (b : Bool) : (lit i b).size ≤ 1 := by
    cases b <;> simp [lit]
  let eqWord (y : BitString n) : Circuit Unbounded.signature n 1 :=
    (Circuit.oneGate (σ := Unbounded.signature) (.and n) id).comp
      (Circuit.pi fun i : Fin n => lit i (y i))
  have heq_eval (y z : BitString n) :
      (eqWord y).eval Unbounded.interpretation z 0 = decide (z = y) := by
    simp only [eqWord, Circuit.eval_comp, Circuit.eval_pi, Circuit.eval_oneGate,
      interpretation_and, id_eq, hlit_eval, decide_eq_true_eq, funext_iff]
  let D : Circuit Unbounded.signature n 1 :=
    (Circuit.oneGate (σ := Unbounded.signature) (.or #R) id).comp
      (Circuit.pi fun idx : Fin #R => eqWord (eR idx).1)
  have hDeval (z : BitString n) :
      D.eval Unbounded.interpretation z 0 = decide (z ∈ R) := by
    simp only [D, Circuit.eval_comp, Circuit.eval_pi, Circuit.eval_oneGate,
      interpretation_or, id_eq, heq_eval, decide_eq_true_eq]
    rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
    constructor
    · rintro ⟨idx, rfl⟩; exact (eR idx).2
    · intro hz; exact ⟨eR.symm ⟨z, hz⟩, by simp⟩
  have hR_card : #R ≤ 2 ^ ℓ :=
    Finset.card_image_le.trans_eq (by simp [BitString, ℓ])
  have heq_dw (y : BitString n) : (eqWord y).depthWith andOrCost ≤ 1 := by
    dsimp only [eqWord]
    refine (Circuit.depthWith_comp_le (σ := Unbounded.signature) andOrCost _ _).trans ?_
    have hpi2 := Circuit.depthWith_pi_le (σ := Unbounded.signature) andOrCost
      (fun i : Fin n => lit i (y i)) (fun i => (hlit_dw _ _).le)
    simp only [Circuit.depthWith_oneGate, andOrCost_and]
    omega
  have heq_d (y : BitString n) : (eqWord y).depth ≤ 2 := by
    dsimp only [eqWord]
    refine (Circuit.depth_comp_le _ _).trans ?_
    have hpi2 := Circuit.depth_pi_le (fun i : Fin n => lit i (y i)) (fun i => hlit_d _ _)
    simp only [Circuit.depth_oneGate]
    omega
  refine ⟨n, D, hn_pos, ?_, ?_, ?_, ?_⟩
  · dsimp only [D]
    refine (Circuit.depthWith_comp_le (σ := Unbounded.signature) andOrCost _ _).trans ?_
    have hpi := Circuit.depthWith_pi_le (σ := Unbounded.signature) andOrCost
      (fun idx : Fin #R => eqWord (eR idx).1) (fun idx => heq_dw _)
    simp only [Circuit.depthWith_oneGate, andOrCost_or]
    omega
  · dsimp only [D]
    refine (Circuit.depth_comp_le _ _).trans ?_
    have hpi := Circuit.depth_pi_le (fun idx : Fin #R => eqWord (eR idx).1) (fun idx => heq_d _)
    simp only [Circuit.depth_oneGate]
    omega
  · -- Size bound `D.size ≤ 2^ℓ * (n + 1) + 1 ≤ 2^(ℓ + m + 3) ≤ 2^(n^α)`.
    have hDsz : D.size ≤ 2 ^ (ℓ + m + 3) := by
      have heq_sz (y : BitString n) : (eqWord y).size ≤ n + 1 := by
        simp only [eqWord, Circuit.size_comp, Circuit.size_pi, Circuit.size_oneGate]
        calc (∑ i : Fin n, (lit i (y i)).size) + 1
            ≤ (∑ _i : Fin n, 1) + 1 :=
              Nat.add_le_add_right (Finset.sum_le_sum fun _ _ => hlit_sz _ _) 1
          _ = n + 1 := by simp
      simp only [D, Circuit.size_comp, Circuit.size_pi, Circuit.size_oneGate]
      have hsum : ∑ idx : Fin #R, (eqWord (eR idx).1).size ≤ #R * (n + 1) := by
        calc _ ≤ ∑ _idx : Fin #R, (n + 1) := Finset.sum_le_sum fun _ _ => heq_sz _
          _ = #R * (n + 1) := by simp
      have hn1 : n + 1 ≤ 2 * 2 ^ m := by dsimp [n]; have := Nat.one_le_two_pow (n := m); omega
      calc (∑ idx : Fin #R, (eqWord (eR idx).1).size) + 1
          ≤ 2 ^ ℓ * (2 * 2 ^ m) + 1 := by
            have := Nat.mul_le_mul hR_card hn1; omega
        _ ≤ 2 ^ (ℓ + m + 3) := by
            rw [pow_add 2 (ℓ + m) 3, pow_add 2 ℓ m]
            have hmul : 2 ^ ℓ * (2 * 2 ^ m) = 2 * (2 ^ ℓ * 2 ^ m) := by ring
            have h1 : 1 ≤ 2 ^ ℓ * 2 ^ m := Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)
            rw [hmul]
            have h23 : (2 : ℕ) ^ 3 = 8 := by norm_num
            rw [h23]
            omega
    have hn_rpow : ((n : ℝ) ^ α) = (2 : ℝ) ^ (α * (m : ℝ)) := by
      dsimp [n]
      rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
        mul_comm]
    rw [hn_rpow]
    calc (D.size : ℝ) ≤ ((2 ^ (ℓ + m + 3) : ℕ) : ℝ) := by exact_mod_cast hDsz
      _ = (2 : ℝ) ^ ((ℓ + m + 3 : ℕ) : ℝ) := by rw [Real.rpow_natCast]; push_cast; rfl
      _ ≤ (2 : ℝ) ^ ((2 : ℝ) ^ (α * (m : ℝ))) := by
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
          rw [hℓ_eq]
          exact hm1
  · -- Distinguishing advantage `≥ 1 - 1/2 = 1/2 > 1/100`.
    have hreal : ((uniformOfFintype (BitString ℓ)).toOuterMeasure
        {s | D.eval Unbounded.interpretation (G n s) 0 = true}).toReal = 1 := by
      have huniv : {s : BitString ℓ | D.eval Unbounded.interpretation (G n s) 0 = true} =
          Set.univ := Set.eq_univ_iff_forall.mpr fun s => by
        simp [hDeval, R]
      rw [huniv, toOuterMeasure_univ_toReal]
    have hideal : ((uniformOfFintype (BitString n)).toOuterMeasure
        {z | D.eval Unbounded.interpretation z 0 = true}).toReal ≤ 1 / 2 := by
      rw [toOuterMeasure_apply_toReal]
      refine le_trans (le_of_eq ?_)
        (show (∑ a ∈ R, (uniformOfFintype (BitString n) a).toReal) ≤ 1 / 2 by
          simp only [uniformOfFintype_apply, BitString, Fintype.card_fun, Fintype.card_bool,
            Fintype.card_fin, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
            Nat.cast_pow, Nat.cast_ofNat, Finset.sum_const, nsmul_eq_mul, ← div_eq_mul_inv]
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          have hle_nat : 2 * #R ≤ 2 ^ n := by
            calc 2 * #R ≤ 2 * 2 ^ ℓ := Nat.mul_le_mul_left 2 hR_card
              _ = 2 ^ (ℓ + 1) := by rw [pow_succ']
              _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by rw [hℓ_eq]; exact hm2)
          have hle_r : ((2 * #R : ℕ) : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by exact_mod_cast hle_nat
          push_cast at hle_r
          linarith)
      rw [← Finset.sum_subset (Finset.subset_univ R)]
      · refine Finset.sum_congr rfl fun a ha => ?_
        simp [hDeval, ha]
      · intro a _ ha
        simp [hDeval, ha]
    rw [hreal]
    have hge : (1 / 2 : ℝ) ≤ |1 - ((uniformOfFintype (BitString n)).toOuterMeasure
        {z | D.eval Unbounded.interpretation z 0 = true}).toReal| := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    linarith


end CslibFrontier.Crypto.PRG.NisanWigderson.AC0
