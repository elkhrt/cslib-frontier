/-
Copyright (c) 2026 Formal Papers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.ExactTriangle.Hashing
public import CslibFrontier.Computability.WordRAM.Defs
public import Mathlib.Data.Finset.Card

import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Binary CSP Carrier, Raw Encoding, and Williams Split-and-List Reduction

Defines `BinaryConstraint`, `BinaryCSP`, the raw honest word encoding `BinaryCSP.encode`, the
three-block base-`d` split (`blockB`, `blockN1`, `blockN2`, `blockN3`, `blockM`, `williamsWeight`),
and proves the exact `#2-CSP` modular-zero triangle reduction `countZeroMod_eq_solCount`.
-/

public section

namespace Cslib.Algorithms.WordRAM.CSP

open Cslib.WordRAM
open Cslib.Algorithms.ExactTriangle

/-! ### Binary CSP Carrier and Raw Input Encoding -/

/-- A binary constraint on `n` variables with domain size `d`: a pair of variable indices
`(fst, snd)` and a finite set of permitted value pairs in `Fin d × Fin d`. -/
@[ext]
structure BinaryConstraint (n d : ℕ) where
  /-- First variable in the constraint scope. -/
  fst : Fin n
  /-- Second variable in the constraint scope. -/
  snd : Fin n
  /-- Permitted pairs of domain values. -/
  permitted : Finset (Fin d × Fin d)
  deriving DecidableEq

/-- A binary constraint is satisfied by `σ` iff `(σ fst, σ snd) ∈ permitted`. -/
@[expose] def BinaryConstraint.Satisfies {n d : ℕ} (c : BinaryConstraint n d)
    (σ : Fin n → Fin d) : Prop :=
  (σ c.fst, σ c.snd) ∈ c.permitted

instance BinaryConstraint.instDecidableSatisfies {n d : ℕ} (c : BinaryConstraint n d)
    (σ : Fin n → Fin d) : Decidable (c.Satisfies σ) :=
  inferInstanceAs (Decidable ((σ c.fst, σ c.snd) ∈ c.permitted))

/-- A binary CSP instance with `n` variables, domain size `d`, and `m` binary constraints. -/
@[ext]
structure BinaryCSP where
  /-- Number of variables. -/
  n : ℕ
  /-- Domain size. -/
  d : ℕ
  /-- Number of constraints. -/
  m : ℕ
  /-- Indexed family of binary constraints. -/
  constraints : Fin m → BinaryConstraint n d

/-- An assignment `σ : Fin I.n → Fin I.d` is a solution iff it satisfies every constraint. -/
@[expose] def BinaryCSP.IsSolution (I : BinaryCSP) (σ : Fin I.n → Fin I.d) : Prop :=
  ∀ i : Fin I.m, (I.constraints i).Satisfies σ

instance BinaryCSP.instDecidableIsSolution (I : BinaryCSP) (σ : Fin I.n → Fin I.d) :
    Decidable (I.IsSolution σ) :=
  inferInstanceAs (Decidable (∀ i : Fin I.m, (I.constraints i).Satisfies σ))

/-- A binary CSP instance is satisfiable iff it admits a solution. -/
@[expose] def BinaryCSP.IsSatisfiable (I : BinaryCSP) : Prop :=
  ∃ σ : Fin I.n → Fin I.d, I.IsSolution σ

/-- The exact number of satisfying assignments of `I`. -/
def BinaryCSP.solCount (I : BinaryCSP) : ℕ :=
  (Finset.univ.filter fun σ : Fin I.n → Fin I.d => I.IsSolution σ).card

/-- `I` is satisfiable iff `I.solCount > 0`. -/
theorem BinaryCSP.isSatisfiable_iff_solCount_pos (I : BinaryCSP) :
    I.IsSatisfiable ↔ 0 < I.solCount := by
  simp only [IsSatisfiable, solCount, Finset.card_pos, Finset.Nonempty, Finset.mem_filter,
    Finset.mem_univ, true_and]

/-- The binary CSP satisfiability decision language. -/
@[expose] def BinaryCSPSAT : Set BinaryCSP :=
  { I | I.IsSatisfiable }

/-- Raw row-major word encoding of a single binary constraint: `[fst, snd]` followed by the
`d × d` 0/1 indicator table of `permitted`. -/
def BinaryConstraint.encode {n d : ℕ} (c : BinaryConstraint n d) : List ℕ :=
  [c.fst.val, c.snd.val] ++
    (List.finRange d).flatMap fun u =>
      (List.finRange d).map fun v => if (u, v) ∈ c.permitted then 1 else 0

/-- Raw honest word-list encoding of a binary CSP instance: `[n, d, m]` followed by the
concatenation of the `m` constraint encodings. -/
def BinaryCSP.encode (I : BinaryCSP) : List ℕ :=
  [I.n, I.d, I.m] ++ (List.finRange I.m).flatMap fun i => (I.constraints i).encode

private theorem length_flatMap_const {α β : Type*} (L : List α) (f : α → List β) (s : ℕ)
    (h : ∀ a ∈ L, (f a).length = s) : (L.flatMap f).length = L.length * s := by
  induction L with
  | nil => simp
  | cons a L' ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]
    ring

private theorem getD_flatMap_const {α : Type*} (L : List α) (f : α → List ℕ) (s : ℕ)
    (h : ∀ a ∈ L, (f a).length = s) (i j : ℕ) (hi : i < L.length) (hj : j < s) :
    (L.flatMap f).getD (i * s + j) 0 = (f (L[i]'hi)).getD j 0 := by
  induction L generalizing i with
  | nil => simp at hi
  | cons a L' ih =>
    cases i with
    | zero =>
      simp only [List.flatMap_cons, Nat.zero_mul, Nat.zero_add, List.getElem_cons_zero]
      rw [List.getD_append]
      simp [h a (by simp), hj]
    | succ i' =>
      have hlen : (f a).length = s := h a (by simp)
      have hge : (f a).length ≤ (i' + 1) * s + j := by
        rw [hlen]; nlinarith
      simp only [List.flatMap_cons, List.getElem_cons_succ]
      rw [List.getD_append_right _ _ _ _ hge, hlen]
      have hsub : (i' + 1) * s + j - s = i' * s + j := by
        rw [Nat.add_mul, Nat.one_mul]; omega
      rw [hsub]
      exact ih (fun x hx => h x (by simp [hx])) i' (by simpa using hi)

theorem BinaryConstraint.encode_length {n d : ℕ} (c : BinaryConstraint n d) :
    c.encode.length = 2 + d * d := by
  unfold BinaryConstraint.encode
  rw [List.length_append, length_flatMap_const _ _ d (fun _ _ => by simp)]
  simp

theorem BinaryCSP.encode_length (I : BinaryCSP) :
    I.encode.length = 3 + I.m * (2 + I.d * I.d) := by
  unfold BinaryCSP.encode
  rw [List.length_append,
    length_flatMap_const _ _ (2 + I.d * I.d) (fun _ _ => BinaryConstraint.encode_length _)]
  simp

theorem BinaryCSP.encode_mem_n (I : BinaryCSP) :
    (Data.init I.encode : Data 160).mem 1 = I.n := by
  simp [BinaryCSP.encode]

theorem BinaryCSP.encode_mem_d (I : BinaryCSP) :
    (Data.init I.encode : Data 160).mem 2 = I.d := by
  simp [BinaryCSP.encode]

theorem BinaryCSP.encode_mem_m (I : BinaryCSP) :
    (Data.init I.encode : Data 160).mem 3 = I.m := by
  simp [BinaryCSP.encode]

theorem BinaryCSP.encode_mem_fst {r : ℕ} (I : BinaryCSP) (i : Fin I.m) :
    (Data.init I.encode : Data r).mem (4 + i.val * (2 + I.d * I.d)) =
      (I.constraints i).fst.val := by
  rw [show 4 + i.val * (2 + I.d * I.d) = (3 + (i.val * (2 + I.d * I.d) + 0)) + 1 by omega,
    Data.init_mem_succ, BinaryCSP.encode,
    List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_sub_cancel_left]
  rw [getD_flatMap_const _ _ (2 + I.d * I.d)
    (fun _ _ => BinaryConstraint.encode_length _) i.val 0 (by simp) (by omega)]
  simp [BinaryConstraint.encode]

theorem BinaryCSP.encode_mem_snd {r : ℕ} (I : BinaryCSP) (i : Fin I.m) :
    (Data.init I.encode : Data r).mem (4 + i.val * (2 + I.d * I.d) + 1) =
      (I.constraints i).snd.val := by
  rw [show 4 + i.val * (2 + I.d * I.d) + 1 = (3 + (i.val * (2 + I.d * I.d) + 1)) + 1 by omega,
    Data.init_mem_succ, BinaryCSP.encode,
    List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_sub_cancel_left]
  rw [getD_flatMap_const _ _ (2 + I.d * I.d)
    (fun _ _ => BinaryConstraint.encode_length _) i.val 1 (by simp) (by omega)]
  simp [BinaryConstraint.encode]

theorem BinaryCSP.encode_mem_perm {r : ℕ} (I : BinaryCSP) (i : Fin I.m)
    (u v : Fin I.d) :
    (Data.init I.encode : Data r).mem
        (4 + i.val * (2 + I.d * I.d) + (u.val * I.d + v.val + 2)) =
      if (u, v) ∈ (I.constraints i).permitted then 1 else 0 := by
  have hlt : u.val * I.d + v.val + 2 < 2 + I.d * I.d := by
    have : u.val * I.d + v.val < I.d * I.d := by nlinarith [u.isLt, v.isLt]
    omega
  rw [show 4 + i.val * (2 + I.d * I.d) + (u.val * I.d + v.val + 2) =
      (3 + (i.val * (2 + I.d * I.d) + (u.val * I.d + v.val + 2))) + 1 by omega,
    Data.init_mem_succ, BinaryCSP.encode,
    List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_sub_cancel_left]
  rw [getD_flatMap_const _ _ (2 + I.d * I.d)
    (fun _ _ => BinaryConstraint.encode_length _) i.val _ (by simp) hlt]
  simp only [List.getElem_finRange, BinaryConstraint.encode]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
    show u.val * I.d + v.val + 2 - 2 = u.val * I.d + v.val by omega]
  rw [getD_flatMap_const _ _ I.d (fun _ _ => by simp) u.val v.val (by simp) v.isLt]
  simp [List.getD_eq_getElem?_getD, v.isLt]

/-! ### Three-Block Split, Base-`d` Encoding, and Exact `#2-CSP` Reduction -/

/-- Block length `b = ⌈n / 3⌉ = (n + 2) / 3`. -/
def blockB (n : ℕ) : ℕ := (n + 2) / 3

/-- Size of block 0: `min n b`. -/
def blockN1 (n : ℕ) : ℕ := min n (blockB n)

/-- Size of block 1: `min (n - n₁) b`. -/
def blockN2 (n : ℕ) : ℕ := min (n - blockN1 n) (blockB n)

/-- Size of block 2: `n - (n₁ + n₂)`. -/
def blockN3 (n : ℕ) : ℕ := n - (blockN1 n + blockN2 n)

/-- Matrix side length `M = d ^ b`. -/
def blockM (n d : ℕ) : ℕ := d ^ blockB n

/-- Block index (`0`, `1`, or `2`) of variable `x < n`. -/
def blockOf (n x : ℕ) : ℕ :=
  if x < blockN1 n then 0 else if x < blockN1 n + blockN2 n then 1 else 2

/-- Starting variable index of block `k ∈ {0, 1, 2}`. -/
def blockOff (n k : ℕ) : ℕ :=
  if k = 0 then 0 else if k = 1 then blockN1 n else blockN1 n + blockN2 n

/-- Number of valid base-`d` indices in block `k ∈ {0, 1, 2}`. -/
def blockLim (n d k : ℕ) : ℕ :=
  if k = 0 then d ^ blockN1 n else if k = 1 then d ^ blockN2 n else d ^ blockN3 n

theorem block_sum (n : ℕ) : blockN1 n + blockN2 n + blockN3 n = n := by
  unfold blockN3 blockN2 blockN1 blockB; omega

theorem blockN1_le (n : ℕ) : blockN1 n ≤ blockB n := by
  unfold blockN1; omega

theorem blockN2_le (n : ℕ) : blockN2 n ≤ blockB n := by
  unfold blockN2; omega

theorem blockN3_le (n : ℕ) : blockN3 n ≤ blockB n := by
  unfold blockN3 blockN2 blockN1 blockB; omega

private theorem blockLim_le_blockM {n d k : ℕ} (hd : 0 < d) :
    blockLim n d k ≤ blockM n d := by
  unfold blockLim blockM
  split_ifs
  · exact Nat.pow_le_pow_right hd (blockN1_le n)
  · exact Nat.pow_le_pow_right hd (blockN2_le n)
  · exact Nat.pow_le_pow_right hd (blockN3_le n)

/-- Little-endian base-`d` encoding of a block assignment `Fin L → Fin d`. -/
private def encodeBlock {d : ℕ} : {L : ℕ} → (Fin L → Fin d) → ℕ
  | 0, _ => 0
  | _ + 1, σ => (σ 0).val + d * encodeBlock (fun j => σ j.succ)

private theorem encodeBlock_lt {d : ℕ} (hd : 0 < d) :
    ∀ {L : ℕ} (σ : Fin L → Fin d), encodeBlock σ < d ^ L
  | 0, _ => by simp [encodeBlock]
  | L + 1, σ => by
    have ih := encodeBlock_lt hd (fun j : Fin L => σ j.succ)
    have h0 := (σ 0).isLt
    simp only [encodeBlock, pow_succ']
    nlinarith

private theorem encodeBlock_digit {d : ℕ} (hd : 0 < d) :
    ∀ {L : ℕ} (σ : Fin L → Fin d) (j : Fin L),
      (encodeBlock σ / d ^ j.val) % d = (σ j).val
  | 0, _, j => j.elim0
  | L + 1, σ, j => by
    refine Fin.cases ?_ ?_ j
    · simp only [encodeBlock, Fin.val_zero, pow_zero, Nat.div_one,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (σ 0).isLt]
    · intro k
      simp only [encodeBlock, Fin.val_succ, pow_succ']
      rw [← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hd,
        Nat.div_eq_of_lt (σ 0).isLt, Nat.zero_add]
      exact encodeBlock_digit hd (fun i : Fin L => σ i.succ) k

/-- Decode a base-`d` integer into a block assignment `Fin L → Fin d`. -/
private def decodeBlock {d : ℕ} (hd : 0 < d) (L : ℕ) (v : ℕ) : Fin L → Fin d :=
  fun j => ⟨(v / d ^ j.val) % d, Nat.mod_lt _ hd⟩

private theorem encode_decodeBlock {d : ℕ} (hd : 0 < d) :
    ∀ {L : ℕ} {v : ℕ}, v < d ^ L → encodeBlock (decodeBlock hd L v) = v
  | 0, v, hv => by simp at hv; simp [encodeBlock, hv]
  | L + 1, v, hv => by
    have hdiv : v / d < d ^ L := by
      rw [Nat.div_lt_iff_lt_mul hd]
      simpa only [pow_succ] using hv
    have hsub : (fun j : Fin L => decodeBlock hd (L + 1) v j.succ) =
        decodeBlock hd L (v / d) := by
      funext j
      apply Fin.ext
      simp only [decodeBlock, Fin.val_succ, pow_succ', ← Nat.div_div_eq_div_mul]
    simp only [encodeBlock]
    rw [hsub, encode_decodeBlock hd hdiv]
    simp only [decodeBlock, Fin.val_zero, pow_zero, Nat.div_one, Nat.mod_add_div]

/-- Decode a triple of block indices `(a, b', c)` into a full assignment `Fin n → Fin d`. -/
private def decodeTriple {n d : ℕ} (hd : 0 < d) (a b' c : ℕ) : Fin n → Fin d :=
  fun j =>
    if j.val < blockN1 n then ⟨(a / d ^ j.val) % d, Nat.mod_lt _ hd⟩
    else if j.val < blockN1 n + blockN2 n then
      ⟨(b' / d ^ (j.val - blockN1 n)) % d, Nat.mod_lt _ hd⟩
    else ⟨(c / d ^ (j.val - (blockN1 n + blockN2 n))) % d, Nat.mod_lt _ hd⟩

/-- Encode a full assignment `σ : Fin n → Fin d` into its three block indices `(a, b', c)`. -/
private def encodeTriple {n d : ℕ} (σ : Fin n → Fin d) : ℕ × ℕ × ℕ :=
  (encodeBlock (fun j : Fin (blockN1 n) => σ ⟨j.val, by have := block_sum n; omega⟩),
   encodeBlock (fun j : Fin (blockN2 n) =>
     σ ⟨blockN1 n + j.val, by have := block_sum n; omega⟩),
   encodeBlock (fun j : Fin (blockN3 n) =>
     σ ⟨blockN1 n + blockN2 n + j.val, by have := block_sum n; omega⟩))

private theorem decode_encodeTriple {n d : ℕ} (hd : 0 < d) (σ : Fin n → Fin d) :
    decodeTriple hd (encodeTriple σ).1 (encodeTriple σ).2.1 (encodeTriple σ).2.2 = σ := by
  funext j
  apply Fin.ext
  unfold decodeTriple encodeTriple
  split_ifs with h1 h2
  · exact encodeBlock_digit hd _ ⟨j.val, h1⟩
  · have hlt : j.val - blockN1 n < blockN2 n := by omega
    simpa only [Nat.add_sub_cancel' (Nat.le_of_not_lt h1)] using
      encodeBlock_digit hd (fun i : Fin (blockN2 n) =>
        σ ⟨blockN1 n + i.val, by have := block_sum n; omega⟩) ⟨j.val - blockN1 n, hlt⟩
  · have hlt : j.val - (blockN1 n + blockN2 n) < blockN3 n := by
      have := block_sum n; omega
    simpa only [Nat.add_sub_cancel' (Nat.le_of_not_lt h2)] using
      encodeBlock_digit hd (fun i : Fin (blockN3 n) =>
        σ ⟨blockN1 n + blockN2 n + i.val, by have := block_sum n; omega⟩)
        ⟨j.val - (blockN1 n + blockN2 n), hlt⟩

private theorem encode_decodeTriple {n d : ℕ} (hd : 0 < d) {a b' c : ℕ}
    (ha : a < d ^ blockN1 n) (hb : b' < d ^ blockN2 n) (hc : c < d ^ blockN3 n) :
    encodeTriple (decodeTriple hd a b' c : Fin n → Fin d) = (a, b', c) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · have h1 : (fun j : Fin (blockN1 n) =>
        (decodeTriple hd a b' c : Fin n → Fin d) ⟨j.val, by have := block_sum n; omega⟩) =
        decodeBlock hd (blockN1 n) a := by
      funext j; simp [decodeTriple, decodeBlock, j.isLt]
    simpa only [encodeTriple, h1] using encode_decodeBlock hd ha
  · have h2 : (fun j : Fin (blockN2 n) =>
        (decodeTriple hd a b' c : Fin n → Fin d)
          ⟨blockN1 n + j.val, by have := block_sum n; omega⟩) =
        decodeBlock hd (blockN2 n) b' := by
      funext j
      have hge : ¬(blockN1 n + j.val < blockN1 n) := by omega
      have hlt : blockN1 n + j.val < blockN1 n + blockN2 n := by omega
      simp [decodeTriple, decodeBlock, hge, hlt]
    simpa only [encodeTriple, h2] using encode_decodeBlock hd hb
  · have h3 : (fun j : Fin (blockN3 n) =>
        (decodeTriple hd a b' c : Fin n → Fin d)
          ⟨blockN1 n + blockN2 n + j.val, by have := block_sum n; omega⟩) =
        decodeBlock hd (blockN3 n) c := by
      funext j
      have hge1 : ¬(blockN1 n + blockN2 n + j.val < blockN1 n) := by omega
      have hge2 : ¬(blockN1 n + blockN2 n + j.val < blockN1 n + blockN2 n) := by omega
      simp [decodeTriple, decodeBlock, hge1, hge2]
    simpa only [encodeTriple, h3] using encode_decodeBlock hd hc

/-- Pure predicate asserting `(vx, vy)` is a valid permitted value pair of `c`. -/
@[expose] def hasPermitted {n d : ℕ} (c : BinaryConstraint n d) (vx vy : ℕ) : Prop :=
  ∃ (hx : vx < d) (hy : vy < d), (⟨vx, hx⟩, ⟨vy, hy⟩) ∈ c.permitted

instance instDecidableHasPermitted {n d : ℕ} (c : BinaryConstraint n d) (vx vy : ℕ) :
    Decidable (hasPermitted c vx vy) :=
  if hx : vx < d then
    if hy : vy < d then
      if hmem : (⟨vx, hx⟩, ⟨vy, hy⟩) ∈ c.permitted then
        isTrue ⟨hx, hy, hmem⟩
      else isFalse (fun ⟨_, _, h⟩ => hmem h)
    else isFalse (fun ⟨_, h, _⟩ => hy h)
  else isFalse (fun ⟨h, _, _⟩ => hx h)

/-- Whether a single constraint `c` is checked and satisfied by block pair `(rowBlock, colBlock)`
at indices `(rIdx, cIdx)`. -/
@[expose] def constraintOk (n d rowBlock colBlock rIdx cIdx : ℕ)
    (c : BinaryConstraint n d) : Prop :=
  let bx := blockOf n c.fst.val
  let by_ := blockOf n c.snd.val
  (bx = rowBlock ∨ bx = colBlock) → (by_ = rowBlock ∨ by_ = colBlock) →
    let vx := ((if bx = rowBlock then rIdx else cIdx) /
      d ^ (c.fst.val - if bx = rowBlock then blockOff n rowBlock else blockOff n colBlock)) % d
    let vy := ((if by_ = rowBlock then rIdx else cIdx) /
      d ^ (c.snd.val - if by_ = rowBlock then blockOff n rowBlock else blockOff n colBlock)) % d
    hasPermitted c vx vy

instance instDecidableConstraintOk (n d rowBlock colBlock rIdx cIdx : ℕ)
    (c : BinaryConstraint n d) :
    Decidable (constraintOk n d rowBlock colBlock rIdx cIdx c) := by
  unfold constraintOk; infer_instance

/-- Canonical `{0, 1}` weight for matrix cell `(rIdx, cIdx)` of block pair `(rowBlock, colBlock)`:
`0` iff `rIdx, cIdx` are within their block ranges and satisfy every constraint whose endpoints lie
in `{rowBlock, colBlock}`; `1` otherwise. -/
def williamsWeight (I : BinaryCSP) (rowBlock colBlock rIdx cIdx : ℕ) : ℤ :=
  if rIdx < blockLim I.n I.d rowBlock ∧ cIdx < blockLim I.n I.d colBlock ∧
      ∀ i : Fin I.m, constraintOk I.n I.d rowBlock colBlock rIdx cIdx (I.constraints i)
  then 0 else 1

theorem williamsWeight_abs_le_one (I : BinaryCSP) (rb cb r c : ℕ) :
    (williamsWeight I rb cb r c).natAbs ≤ 1 := by
  unfold williamsWeight; split_ifs <;> decide

private theorem decodeTriple_eval {n d : ℕ} (hd : 0 < d) (a b' c : ℕ) (x : Fin n)
    (rowBlock colBlock rIdx cIdx : ℕ) (hne : rowBlock ≠ colBlock)
    (hr : rIdx = if rowBlock = 0 then a else if rowBlock = 1 then b' else c)
    (hc : cIdx = if colBlock = 0 then a else if colBlock = 1 then b' else c)
    (hx : blockOf n x.val = rowBlock ∨ blockOf n x.val = colBlock) :
    ((decodeTriple hd a b' c : Fin n → Fin d) x).val =
      ((if blockOf n x.val = rowBlock then rIdx else cIdx) /
        d ^ (x.val - if blockOf n x.val = rowBlock then blockOff n rowBlock
          else blockOff n colBlock)) % d := by
  subst hr; subst hc
  by_cases h1 : x.val < blockN1 n
  · have hbo : blockOf n x.val = 0 := by simp [blockOf, h1]
    rw [hbo] at hx ⊢
    simp only [decodeTriple, h1, ↓reduceIte]
    rcases hx with h0 | h0
    · rw [← h0]; simp [blockOff]
    · have hne' : (0 : ℕ) ≠ rowBlock := fun hk => hne (hk.symm.trans h0)
      simp [hne', ← h0, blockOff]
  · by_cases h2 : x.val < blockN1 n + blockN2 n
    · have hbo : blockOf n x.val = 1 := by simp [blockOf, h1, h2]
      rw [hbo] at hx ⊢
      simp only [decodeTriple, h1, h2, ↓reduceIte]
      rcases hx with h0 | h0
      · rw [← h0]; simp [blockOff]
      · have hne' : (1 : ℕ) ≠ rowBlock := fun hk => hne (hk.symm.trans h0)
        simp [hne', ← h0, blockOff]
    · have hbo : blockOf n x.val = 2 := by simp [blockOf, h1, h2]
      rw [hbo] at hx ⊢
      simp only [decodeTriple, h1, h2, ↓reduceIte]
      rcases hx with h0 | h0
      · rw [← h0]; simp [blockOff]
      · have hne' : (2 : ℕ) ≠ rowBlock := fun hk => hne (hk.symm.trans h0)
        simp [hne', ← h0, blockOff]

/-- Exact `#2-CSP` reduction: for any binary CSP `I` with `0 < I.d`, counting modular-zero
triangles modulo `4` on the three `{0, 1}` block-pair matrices equals `I.solCount`. -/
theorem countZeroMod_eq_solCount (I : BinaryCSP) (hd : 0 < I.d) :
    countZeroMod
      (fun α β : Fin (blockM I.n I.d) => williamsWeight I 0 1 α.val β.val)
      (fun α β : Fin (blockM I.n I.d) => williamsWeight I 1 2 α.val β.val)
      (fun α β : Fin (blockM I.n I.d) => williamsWeight I 0 2 α.val β.val) 4 =
      I.solCount := by
  classical
  have hzero_iff (t : Triangle (blockM I.n I.d)) :
      (weightSum
        (fun α β : Fin (blockM I.n I.d) => williamsWeight I 0 1 α.val β.val)
        (fun α β : Fin (blockM I.n I.d) => williamsWeight I 1 2 α.val β.val)
        (fun α β : Fin (blockM I.n I.d) => williamsWeight I 0 2 α.val β.val)
        t.a t.b t.c ≡ 0 [ZMOD (4 : ℤ)]) ↔
        t.a.val < I.d ^ blockN1 I.n ∧ t.b.val < I.d ^ blockN2 I.n ∧ t.c.val < I.d ^ blockN3 I.n ∧
          I.IsSolution (decodeTriple hd t.a.val t.b.val t.c.val) := by
    have hw : ∀ rb cb r c, williamsWeight I rb cb r c = 0 ∨ williamsWeight I rb cb r c = 1 := by
      intro rb cb r c; unfold williamsWeight; split_ifs <;> simp
    have hsum_mod : (weightSum
        (fun α β : Fin (blockM I.n I.d) => williamsWeight I 0 1 α.val β.val)
        (fun α β : Fin (blockM I.n I.d) => williamsWeight I 1 2 α.val β.val)
        (fun α β : Fin (blockM I.n I.d) => williamsWeight I 0 2 α.val β.val)
        t.a t.b t.c ≡ 0 [ZMOD (4 : ℤ)]) ↔
        williamsWeight I 0 1 t.a.val t.b.val = 0 ∧
        williamsWeight I 1 2 t.b.val t.c.val = 0 ∧
        williamsWeight I 0 2 t.a.val t.c.val = 0 := by
      rcases hw 0 1 t.a.val t.b.val with h1 | h1 <;>
      rcases hw 1 2 t.b.val t.c.val with h2 | h2 <;>
      rcases hw 0 2 t.a.val t.c.val with h3 | h3 <;>
      simp [weightSum, h1, h2, h3, Int.ModEq]
    rw [hsum_mod]
    simp only [williamsWeight, blockLim, ite_eq_left_iff, one_ne_zero, imp_false, not_not,
      Nat.reduceEqDiff, ↓reduceIte]
    constructor
    · rintro ⟨⟨ha, hb, hAB⟩, ⟨_, hc, hBC⟩, ⟨_, _, hAC⟩⟩
      refine ⟨ha, hb, hc, fun i => ?_⟩
      change ((decodeTriple hd t.a.val t.b.val t.c.val (I.constraints i).fst),
              (decodeTriple hd t.a.val t.b.val t.c.val (I.constraints i).snd)) ∈
        (I.constraints i).permitted
      have hblk : ∀ x : Fin I.n, blockOf I.n x.val = 0 ∨ blockOf I.n x.val = 1 ∨
          blockOf I.n x.val = 2 := by
        intro x; unfold blockOf; split_ifs <;> simp
      rcases hblk (I.constraints i).fst with hbx | hbx | hbx <;>
      rcases hblk (I.constraints i).snd with hby | hby | hby
      · have h := hAB i (Or.inl hbx) (Or.inl hby)
        obtain ⟨_, _, hm⟩ := h
        convert hm using 2 <;> apply Fin.ext <;>
          exact decodeTriple_eval hd t.a.val t.b.val t.c.val _ 0 1 t.a.val t.b.val
            (by omega) rfl rfl (by simp [hbx, hby])
      · have h := hAB i (Or.inl hbx) (Or.inr hby)
        obtain ⟨_, _, hm⟩ := h
        convert hm using 2 <;> apply Fin.ext <;>
          exact decodeTriple_eval hd t.a.val t.b.val t.c.val _ 0 1 t.a.val t.b.val
            (by omega) rfl rfl (by simp [hbx, hby])
      · have h := hAC i (Or.inl hbx) (Or.inr hby)
        obtain ⟨_, _, hm⟩ := h
        convert hm using 2 <;> apply Fin.ext <;>
          exact decodeTriple_eval hd t.a.val t.b.val t.c.val _ 0 2 t.a.val t.c.val
            (by omega) rfl rfl (by simp [hbx, hby])
      · have h := hAB i (Or.inr hbx) (Or.inl hby)
        obtain ⟨_, _, hm⟩ := h
        convert hm using 2 <;> apply Fin.ext <;>
          exact decodeTriple_eval hd t.a.val t.b.val t.c.val _ 0 1 t.a.val t.b.val
            (by omega) rfl rfl (by simp [hbx, hby])
      · have h := hBC i (Or.inl hbx) (Or.inl hby)
        obtain ⟨_, _, hm⟩ := h
        convert hm using 2 <;> apply Fin.ext <;>
          exact decodeTriple_eval hd t.a.val t.b.val t.c.val _ 1 2 t.b.val t.c.val
            (by omega) rfl rfl (by simp [hbx, hby])
      · have h := hBC i (Or.inl hbx) (Or.inr hby)
        obtain ⟨_, _, hm⟩ := h
        convert hm using 2 <;> apply Fin.ext <;>
          exact decodeTriple_eval hd t.a.val t.b.val t.c.val _ 1 2 t.b.val t.c.val
            (by omega) rfl rfl (by simp [hbx, hby])
      · have h := hAC i (Or.inr hbx) (Or.inl hby)
        obtain ⟨_, _, hm⟩ := h
        convert hm using 2 <;> apply Fin.ext <;>
          exact decodeTriple_eval hd t.a.val t.b.val t.c.val _ 0 2 t.a.val t.c.val
            (by omega) rfl rfl (by simp [hbx, hby])
      · have h := hBC i (Or.inr hbx) (Or.inl hby)
        obtain ⟨_, _, hm⟩ := h
        convert hm using 2 <;> apply Fin.ext <;>
          exact decodeTriple_eval hd t.a.val t.b.val t.c.val _ 1 2 t.b.val t.c.val
            (by omega) rfl rfl (by simp [hbx, hby])
      · have h := hAC i (Or.inr hbx) (Or.inr hby)
        obtain ⟨_, _, hm⟩ := h
        convert hm using 2 <;> apply Fin.ext <;>
          exact decodeTriple_eval hd t.a.val t.b.val t.c.val _ 0 2 t.a.val t.c.val
            (by omega) rfl rfl (by simp [hbx, hby])
    · rintro ⟨ha, hb, hc, hsol⟩
      have hpair : ∀ (rb cb rIdx cIdx : ℕ), rb ≠ cb →
          rIdx = (if rb = 0 then t.a.val else if rb = 1 then t.b.val else t.c.val) →
          cIdx = (if cb = 0 then t.a.val else if cb = 1 then t.b.val else t.c.val) →
          ∀ i : Fin I.m, constraintOk I.n I.d rb cb rIdx cIdx (I.constraints i) := by
        intro rb cb rIdx cIdx hne hr hc' i hx hy
        refine ⟨Nat.mod_lt _ hd, Nat.mod_lt _ hd, ?_⟩
        have h1 := decodeTriple_eval hd t.a.val t.b.val t.c.val (I.constraints i).fst
          rb cb rIdx cIdx hne hr hc' hx
        have h2 := decodeTriple_eval hd t.a.val t.b.val t.c.val (I.constraints i).snd
          rb cb rIdx cIdx hne hr hc' hy
        have h1' : (⟨_, Nat.mod_lt _ hd⟩ : Fin I.d) =
            decodeTriple hd t.a.val t.b.val t.c.val (I.constraints i).fst := Fin.ext h1.symm
        have h2' : (⟨_, Nat.mod_lt _ hd⟩ : Fin I.d) =
            decodeTriple hd t.a.val t.b.val t.c.val (I.constraints i).snd := Fin.ext h2.symm
        rw [h1', h2']
        exact hsol i
      exact ⟨⟨ha, hb, hpair 0 1 t.a.val t.b.val (by omega) rfl rfl⟩,
             ⟨hb, hc, hpair 1 2 t.b.val t.c.val (by omega) rfl rfl⟩,
             ⟨ha, hc, hpair 0 2 t.a.val t.c.val (by omega) rfl rfl⟩⟩
  unfold countZeroMod BinaryCSP.solCount
  refine Finset.card_bij
    (fun (t : Triangle (blockM I.n I.d)) _ => decodeTriple hd t.a.val t.b.val t.c.val)
    ?_ ?_ ?_
  · intro t ht
    rw [Finset.mem_filter] at ht ⊢
    exact ⟨Finset.mem_univ _, ((hzero_iff t).mp ht.2).2.2.2⟩
  · intro t₁ ht₁ t₂ ht₂ heq
    have h1 := (hzero_iff t₁).mp (Finset.mem_filter.mp ht₁).2
    have h2 := (hzero_iff t₂).mp (Finset.mem_filter.mp ht₂).2
    have he1 := encode_decodeTriple hd h1.1 h1.2.1 h1.2.2.1
    have he2 := encode_decodeTriple hd h2.1 h2.2.1 h2.2.2.1
    rw [heq, he2] at he1
    cases t₁; cases t₂
    simp only [Prod.mk.injEq] at he1
    rcases he1 with ⟨ha, hb, hc⟩
    congr 1
    · exact Fin.ext ha.symm
    · exact Fin.ext hb.symm
    · exact Fin.ext hc.symm
  · intro σ hσ
    have hσ' : I.IsSolution σ := (Finset.mem_filter.mp hσ).2
    have ha : (encodeTriple σ).1 < blockM I.n I.d :=
      (encodeBlock_lt hd _).trans_le (Nat.pow_le_pow_right hd (blockN1_le I.n))
    have hb : (encodeTriple σ).2.1 < blockM I.n I.d :=
      (encodeBlock_lt hd _).trans_le (Nat.pow_le_pow_right hd (blockN2_le I.n))
    have hc : (encodeTriple σ).2.2 < blockM I.n I.d :=
      (encodeBlock_lt hd _).trans_le (Nat.pow_le_pow_right hd (blockN3_le I.n))
    let t : Triangle (blockM I.n I.d) :=
      ⟨⟨(encodeTriple σ).1, ha⟩, ⟨(encodeTriple σ).2.1, hb⟩, ⟨(encodeTriple σ).2.2, hc⟩⟩
    refine ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hzero_iff t).mpr ?_⟩,
      decode_encodeTriple hd σ⟩
    refine ⟨encodeBlock_lt hd _, encodeBlock_lt hd _, encodeBlock_lt hd _, ?_⟩
    simpa only [t, decode_encodeTriple hd σ] using hσ'


/-- Semantic characterization of `BinaryConstraint.Satisfies`. -/
theorem BinaryConstraint.satisfies_iff {n d : ℕ} (c : BinaryConstraint n d) (σ : Fin n → Fin d) :
    c.Satisfies σ ↔ (σ c.fst, σ c.snd) ∈ c.permitted := by
  rfl

/-- Card formula for `BinaryCSP.solCount`. -/
theorem BinaryCSP.solCount_eq_card (I : BinaryCSP) :
    I.solCount = (Finset.univ.filter fun σ : Fin I.n → Fin I.d => I.IsSolution σ).card := by
  rfl

/-- Explicit formula for `blockB`. -/
theorem blockB_eq (n : ℕ) : blockB n = (n + 2) / 3 := by rfl

/-- Explicit formula for `blockN1`. -/
theorem blockN1_eq (n : ℕ) : blockN1 n = min n (blockB n) := by rfl

/-- Explicit formula for `blockN2`. -/
theorem blockN2_eq (n : ℕ) : blockN2 n = min (n - blockN1 n) (blockB n) := by rfl

/-- Explicit formula for `blockN3`. -/
theorem blockN3_eq (n : ℕ) : blockN3 n = n - (blockN1 n + blockN2 n) := by rfl

/-- Explicit formula for `blockM`. -/
theorem blockM_eq (n d : ℕ) : blockM n d = d ^ blockB n := by rfl

/-- Explicit formula for `blockOf`. -/
theorem blockOf_eq (n x : ℕ) :
    blockOf n x = if x < blockN1 n then 0 else if x < blockN1 n + blockN2 n then 1 else 2 := by
  rfl

/-- Explicit formula for `blockOff`. -/
theorem blockOff_eq (n k : ℕ) :
    blockOff n k = if k = 0 then 0 else if k = 1 then blockN1 n else blockN1 n + blockN2 n := by
  rfl

/-- Explicit formula for `blockLim`. -/
theorem blockLim_eq (n d k : ℕ) :
    blockLim n d k =
      if k = 0 then d ^ blockN1 n else if k = 1 then d ^ blockN2 n else d ^ blockN3 n := by
  rfl

/-- Explicit formula for `williamsWeight`. -/
theorem williamsWeight_eq (I : BinaryCSP) (rowBlock colBlock rIdx cIdx : ℕ) :
    williamsWeight I rowBlock colBlock rIdx cIdx =
      if rIdx < blockLim I.n I.d rowBlock ∧ cIdx < blockLim I.n I.d colBlock ∧
          ∀ i : Fin I.m, constraintOk I.n I.d rowBlock colBlock rIdx cIdx (I.constraints i)
      then 0 else 1 := by
  rfl

/-- Semantic characterization of `constraintOk`. -/
theorem constraintOk_iff (n d rowBlock colBlock rIdx cIdx : ℕ) (c : BinaryConstraint n d) :
    constraintOk n d rowBlock colBlock rIdx cIdx c ↔
      let bx := blockOf n c.fst.val
      let by_ := blockOf n c.snd.val
      (bx = rowBlock ∨ bx = colBlock) → (by_ = rowBlock ∨ by_ = colBlock) →
        let vx := ((if bx = rowBlock then rIdx else cIdx) /
          d ^ (c.fst.val - if bx = rowBlock then blockOff n rowBlock else blockOff n colBlock)) % d
        let vy := ((if by_ = rowBlock then rIdx else cIdx) /
          d ^ (c.snd.val - if by_ = rowBlock then blockOff n rowBlock else blockOff n colBlock)) % d
        hasPermitted c vx vy := by
  rfl

/-- Semantic characterization of `hasPermitted`. -/
theorem hasPermitted_iff {n d : ℕ} (c : BinaryConstraint n d) (vx vy : ℕ) :
    hasPermitted c vx vy ↔ ∃ (hx : vx < d) (hy : vy < d), (⟨vx, hx⟩, ⟨vy, hy⟩) ∈ c.permitted := by
  rfl

/-- Every word in `I.encode` is bounded by `I.n + I.d + I.m + 1`. -/
theorem BinaryCSP.mem_encode_lt (I : BinaryCSP) {v : ℕ} (hv : v ∈ I.encode) :
    v < I.n + I.d + I.m + 2 := by
  unfold BinaryCSP.encode at hv
  rcases List.mem_append.mp hv with hv | hv
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl <;> omega
  · obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hv
    unfold BinaryConstraint.encode at hi
    rcases List.mem_append.mp hi with hi | hi
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · have := (I.constraints i).fst.isLt; omega
      · have := (I.constraints i).snd.isLt; omega
    · obtain ⟨u, _, hu⟩ := List.mem_flatMap.mp hi
      obtain ⟨v', _, hv'⟩ := List.mem_map.mp hu
      subst hv'
      split_ifs <;> omega

end Cslib.Algorithms.WordRAM.CSP
