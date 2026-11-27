/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Algorithms.Lean.Query.Arith.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Ring

/-!
# Montgomery Batch Inversion and Base-`b` Bulk Exponentiation in `FreeM`

This module formalizes two classical algebraic query algorithms in `Cslib.FreeM`:

1. **Montgomery's batch inversion (`bulkInv`)**: given `n` nonzero elements `a_0, …, a_{n-1}` of a
   field `α`, computes all `n` inverses `a_0⁻¹, …, a_{n-1}⁻¹` using `3 * (n - 1)` multiplications
   and **at most `1` field inversion** (`0` inversions when `n = 0`), by forming prefix products,
   inverting the total product once, and sweeping backward.
2. **Base-`b` bulk exponentiation (`bulkPow`)**: given a ring element `x : α`, radix `b ≥ 2`, digit
   bound `d`, and `n` exponents `e_0, …, e_{n-1} < b ^ d`, precomputes the digit power table
   `x ^ (r * b ^ j)` (`0 ≤ r < b`, `0 ≤ j < d`) and multiplies `d` table entries per output, using
   at most `2 * b * d + n * d` multiplications (`O(n log_n e)` when `b = max 2 n` and
   `d = Nat.log b e + 1`).

## Main definitions

* `CslibFrontier.Query.FieldQuery`: arithmetic query signature extending `+`, `-`, `*` with `.inv`.
* `CslibFrontier.Query.bulkInvList`, `CslibFrontier.Query.bulkInv`: Montgomery batch inversion.
* `CslibFrontier.Query.bulkPow`: base-`b` bulk exponentiation in `FreeM (ArithQuery α)`.

## Main results

* `CslibFrontier.Query.eval_bulkInv`: under the honest field oracle, `bulkInv` computes
  `fun i => (a i)⁻¹` whenever `∀ i, a i ≠ 0`.
* `CslibFrontier.Query.cost_bulkInv_le`: `bulkInv` on `n` elements costs at most
  `3 * n * c_mul + c_inv` (in particular, at most `1` inversion query).
* `CslibFrontier.Query.eval_bulkPow`: under the honest monoid/ring oracle, `bulkPow` computes
  `fun i => x ^ (es i)` whenever `∀ i, es i < b ^ d`.
* `CslibFrontier.Query.cost_bulkPow`: `bulkPow` uses `(b + n) * d` multiplications and `0`
  additions.
-/

public section

namespace CslibFrontier.Query

open Cslib Cslib.Query

/-- Field arithmetic queries: addition, subtraction, multiplication, and multiplicative
inversion. -/
inductive FieldQuery (α : Type) : Type → Type where
  | add (a b : α) : FieldQuery α α
  | sub (a b : α) : FieldQuery α α
  | mul (a b : α) : FieldQuery α α
  | inv (a : α) : FieldQuery α α

namespace FieldQuery

variable {α : Type}

/-- Lift an addition query into `FreeM`. -/
abbrev doAdd (a b : α) : FreeM (FieldQuery α) α := FreeM.lift (.add a b)

/-- Lift a subtraction query into `FreeM`. -/
abbrev doSub (a b : α) : FreeM (FieldQuery α) α := FreeM.lift (.sub a b)

/-- Lift a multiplication query into `FreeM`. -/
abbrev doMul (a b : α) : FreeM (FieldQuery α) α := FreeM.lift (.mul a b)

/-- Lift an inversion query into `FreeM`. -/
abbrev doInv (a : α) : FreeM (FieldQuery α) α := FreeM.lift (.inv a)

/-- Honest oracle interpreting `FieldQuery` via field/ring operations. -/
@[expose] def honest [Add α] [Sub α] [Mul α] [Inv α] {ι : Type} : FieldQuery α ι → ι
  | .add a b => a + b
  | .sub a b => a - b
  | .mul a b => a * b
  | .inv a => a⁻¹

/-- Weighted cost assigning `c_add` to `+`/`-`, `c_mul` to `*`, and `c_inv` to `⁻¹`. -/
@[expose] def weight (c_add c_mul c_inv : ℕ) {ι : Type} : FieldQuery α ι → ℕ
  | .add _ _ => c_add
  | .sub _ _ => c_add
  | .mul _ _ => c_mul
  | .inv _ => c_inv

/-- Embed a division-free `ArithQuery` program into `FieldQuery`. -/
@[expose] def ofArith {β : Type} (p : FreeM (ArithQuery α) β) : FreeM (FieldQuery α) β :=
  p.liftM fun
    | .add a b => doAdd a b
    | .sub a b => doSub a b
    | .mul a b => doMul a b

end FieldQuery

section BulkInv

open FieldQuery

variable {α : Type}

/-- Recursive core of Montgomery batch inversion: given running prefix product `pref` and remaining
list `xs`, returns `(invPref, invList)` where `invPref = pref⁻¹` and `invList` holds the inverses
of `xs`, using `1` inversion at the base and `3` multiplications per list element. -/
@[expose] def bulkInvAux : α → List α → FreeM (FieldQuery α) (α × List α)
  | pref, [] => do
    let invPref ← doInv pref
    return (invPref, [])
  | pref, x :: xs => do
    let pref' ← doMul pref x
    let (invPref', invXs) ← bulkInvAux pref' xs
    let invX ← doMul invPref' pref
    let invPref ← doMul invPref' x
    return (invPref, invX :: invXs)

/-- Montgomery batch inversion on a list `xs : List α`: `0` queries on `[]`, and `3 * (n - 1)`
multiplications plus `1` single inversion on a nonempty list of length `n`. -/
@[expose] def bulkInvList : List α → FreeM (FieldQuery α) (List α)
  | [] => pure []
  | x :: xs => do
    let (invX, invXs) ← bulkInvAux x xs
    return invX :: invXs

private theorem eval_bulkInvAux_field [Field α] (pref : α) (hpref : pref ≠ 0) :
    ∀ (xs : List α), (∀ y ∈ xs, y ≠ 0) →
      (bulkInvAux pref xs).eval honest = (pref⁻¹, xs.map Inv.inv)
  | [], _ => by
    simp [bulkInvAux, doInv, honest]
  | x :: xs, hxs => by
    have hx : x ≠ 0 := hxs x List.mem_cons_self
    have hpref' : pref * x ≠ 0 := mul_ne_zero hpref hx
    have hrest : ∀ y ∈ xs, y ≠ 0 := fun y hy => hxs y (List.mem_cons_of_mem x hy)
    have ih := eval_bulkInvAux_field (pref * x) hpref' xs hrest
    simp only [bulkInvAux, FreeM.eval_bind, doMul, FreeM.eval_lift, honest, ih, FreeM.eval_pure,
      List.map_cons, Prod.mk.injEq, List.cons.injEq, and_true]
    exact ⟨by rw [mul_comm pref x, mul_inv_rev, mul_assoc, inv_mul_cancel₀ hx, mul_one],
      by rw [mul_inv_rev, mul_assoc, inv_mul_cancel₀ hpref, mul_one]⟩

/-- Under the honest field oracle, `bulkInvList` inverts every element of a list of nonzero field
elements. -/
theorem eval_bulkInvList [Field α] (xs : List α) (hxs : ∀ y ∈ xs, y ≠ 0) :
    (bulkInvList xs).eval honest = xs.map Inv.inv := by
  rcases xs with _ | ⟨x, xs⟩
  · rfl
  · have hx : x ≠ 0 := hxs x List.mem_cons_self
    have hrest : ∀ y ∈ xs, y ≠ 0 := fun y hy => hxs y (List.mem_cons_of_mem x hy)
    simp only [bulkInvList, FreeM.eval_bind, eval_bulkInvAux_field x hx xs hrest, FreeM.eval_pure,
      List.map_cons]

private theorem cost_bulkInvAux (oracle : {ι : Type} → FieldQuery α ι → ι)
    (c_add c_mul c_inv : ℕ) :
    ∀ (pref : α) (xs : List α),
      (bulkInvAux pref xs).cost oracle (weight c_add c_mul c_inv) =
        3 * xs.length * c_mul + c_inv
  | pref, [] => by
    simp [bulkInvAux, doInv, weight]
  | pref, x :: xs => by
    simp only [bulkInvAux, FreeM.cost_bind, doMul, FreeM.cost_lift, weight,
      cost_bulkInvAux oracle c_add c_mul c_inv, FreeM.cost_pure, List.length_cons]
    ring

/-- Weighted cost of `bulkInvList`: `0` on `[]`, and `3 * (n - 1) * c_mul + c_inv` on a list of
length `n ≥ 1`. -/
theorem cost_bulkInvList_le (oracle : {ι : Type} → FieldQuery α ι → ι)
    (c_add c_mul c_inv : ℕ) (xs : List α) :
    (bulkInvList xs).cost oracle (weight c_add c_mul c_inv) ≤
      3 * xs.length * c_mul + c_inv := by
  rcases xs with _ | ⟨x, xs⟩
  · simp [bulkInvList]
  · simp only [bulkInvList, FreeM.cost_bind, cost_bulkInvAux, FreeM.cost_pure, List.length_cons,
      add_zero]
    have hmul : 3 * xs.length * c_mul ≤ 3 * (xs.length + 1) * c_mul :=
      Nat.mul_le_mul_right c_mul (by omega)
    omega

/-- Tuple wrapper `bulkInv` on `Fin n → α`. -/
@[expose] def bulkInv [One α] {n : ℕ} (a : Fin n → α) : FreeM (FieldQuery α) (Fin n → α) := do
  let invs ← bulkInvList (List.ofFn a)
  return fun i : Fin n => invs.getD i.val 1

/-- Under the honest field oracle, `bulkInv` computes `fun i => (a i)⁻¹` for all nonzero inputs. -/
theorem eval_bulkInv [Field α] {n : ℕ} (a : Fin n → α) (ha : ∀ i, a i ≠ 0) :
    (bulkInv a).eval honest = fun i => (a i)⁻¹ := by
  funext i
  have hmem : ∀ y ∈ List.ofFn a, y ≠ 0 := by
    intro y hy
    rw [List.mem_ofFn] at hy
    obtain ⟨j, rfl⟩ := hy
    exact ha j
  simp only [bulkInv, FreeM.eval_bind, eval_bulkInvList (List.ofFn a) hmem, FreeM.eval_pure]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (by simp [i.isLt]), Option.map_some, Option.getD_some,
    List.getElem_ofFn]

/-- Weighted cost bound for `bulkInv`: at most `3 * n` multiplications, `0` additions, and `1`
single inversion. -/
theorem cost_bulkInv_le [One α] (oracle : {ι : Type} → FieldQuery α ι → ι)
    (c_add c_mul c_inv : ℕ) {n : ℕ} (a : Fin n → α) :
    (bulkInv a).cost oracle (weight c_add c_mul c_inv) ≤ 3 * n * c_mul + c_inv := by
  simp only [bulkInv, FreeM.cost_bind, FreeM.cost_pure, add_zero]
  simpa [List.length_ofFn] using cost_bulkInvList_le oracle c_add c_mul c_inv (List.ofFn a)

end BulkInv

section BulkPow

open ArithQuery

variable {α : Type}

/-- Compute `[1, y, y^2, …, y^(b-1)]` together with `y^b` using `b` multiplications. -/
@[expose] def powRow [One α] (y : α) : ℕ → α → FreeM (ArithQuery α) (List α × α)
  | 0, cur => pure ([], cur)
  | r + 1, cur => do
    let nxt ← doMul cur y
    let (rest, top) ← powRow y r nxt
    return (cur :: rest, top)

/-- Precompute the `d × b` digit power table `[[1, x, …, x^(b-1)], [1, x^b, …], …]` using `d * b`
multiplications. -/
@[expose] def powTable [One α] (b : ℕ) : ℕ → α → FreeM (ArithQuery α) (List (List α))
  | 0, _ => pure []
  | d + 1, y => do
    let (row, yNext) ← powRow y b 1
    let rows ← powTable b d yNext
    return row :: rows

/-- Evaluate `x ^ e` in base `b` from a precomputed `d × b` digit table using at most `d`
multiplications. -/
@[expose] def evalFromTable [One α] (b : ℕ) :
    List (List α) → ℕ → α → FreeM (ArithQuery α) α
  | [], _, acc => pure acc
  | row :: rows, e, acc => do
    let digit := e % b
    let factor := row.getD digit 1
    let acc' ← doMul acc factor
    evalFromTable b rows (e / b) acc'

/-- Map a monadic `FreeM` function across a list. -/
@[expose] def mapFreeM {F : Type → Type} {β γ : Type} (f : β → FreeM F γ) :
    List β → FreeM F (List γ)
  | [] => pure []
  | x :: xs => do
    let y ← f x
    let ys ← mapFreeM f xs
    return y :: ys

/-- Base-`b` bulk exponentiation of `x : α` at `n` exponents `es : Fin n → ℕ` bounded by `b ^ d`,
using `(b + n) * d` multiplications and `0` additions. -/
@[expose] def bulkPow [One α] {n : ℕ} (b d : ℕ) (x : α) (es : Fin n → ℕ) :
    FreeM (ArithQuery α) (Fin n → α) := do
  let tbl ← powTable b d x
  let vals ← mapFreeM (fun e => evalFromTable b tbl e 1) (List.ofFn es)
  return fun i : Fin n => vals.getD i.val 1

private theorem eval_powRow [Monoid α] [Add α] [Sub α] (y : α) :
    ∀ (r : ℕ) (cur : α),
      (powRow y r cur).eval honest =
        (List.ofFn (fun j : Fin r => cur * y ^ j.val), cur * y ^ r)
  | 0, cur => by
    simp [powRow]
  | r + 1, cur => by
    have ih := eval_powRow y r (cur * y)
    simp only [powRow, FreeM.eval_bind, doMul, FreeM.eval_lift, honest, ih, FreeM.eval_pure,
      Prod.mk.injEq]
    refine ⟨?_, by rw [pow_succ', ← mul_assoc]⟩
    rw [List.ofFn_succ]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, List.cons.injEq, true_and]
    exact congrArg List.ofFn (funext fun j => by rw [pow_succ', ← mul_assoc])

private theorem eval_powTable [Monoid α] [Add α] [Sub α] (b : ℕ) :
    ∀ (d : ℕ) (y : α),
      (powTable b d y).eval honest =
        List.ofFn fun k : Fin d => List.ofFn fun j : Fin b => (y ^ (b ^ k.val)) ^ j.val
  | 0, _ => rfl
  | d + 1, y => by
    have hr := eval_powRow y b 1
    have ht := eval_powTable b d (y ^ b)
    simp only [powTable, FreeM.eval_bind, hr, one_mul, ht, FreeM.eval_pure]
    rw [List.ofFn_succ]
    simp only [Fin.val_zero, pow_zero, pow_one, Fin.val_succ, List.cons.injEq, true_and]
    congr 1
    funext k
    congr 1
    funext j
    rw [pow_succ', pow_mul]

private theorem eval_evalFromTable [CommMonoid α] [Add α] [Sub α] {b : ℕ} (hb : 0 < b) :
    ∀ (d : ℕ) (y : α) (e : ℕ) (acc : α),
      e < b ^ d →
      (evalFromTable b
        (List.ofFn fun k : Fin d => List.ofFn fun j : Fin b => (y ^ (b ^ k.val)) ^ j.val)
        e acc).eval honest = acc * y ^ e
  | 0, y, e, acc, he => by
    have he0 : e = 0 := by simpa using he
    subst he0
    simp [evalFromTable]
  | d + 1, y, e, acc, he => by
    rw [List.ofFn_succ]
    simp only [evalFromTable, Fin.val_zero, pow_zero, pow_one, Fin.val_succ, FreeM.eval_bind,
      doMul, FreeM.eval_lift, honest]
    have hlt_mod : e % b < b := Nat.mod_lt e hb
    have hget : (List.ofFn fun j : Fin b => y ^ j.val).getD (e % b) 1 = y ^ (e % b) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [hlt_mod]),
        Option.getD_some, List.getElem_ofFn]
    have htail : (List.ofFn fun k : Fin d =>
        List.ofFn fun j : Fin b => (y ^ b ^ (k.val + 1)) ^ j.val) =
        (List.ofFn fun k : Fin d =>
          List.ofFn fun j : Fin b => ((y ^ b) ^ b ^ k.val) ^ j.val) := by
      congr 1; funext k; congr 1; funext j; rw [pow_succ', pow_mul]
    have hdiv_lt : e / b < b ^ d := Nat.div_lt_of_lt_mul (by simpa [pow_succ'] using he)
    rw [hget, htail, eval_evalFromTable hb d (y ^ b) (e / b) (acc * y ^ (e % b)) hdiv_lt]
    rw [mul_assoc, ← pow_mul, ← pow_add, Nat.mod_add_div e b]

private theorem eval_mapFreeM {F : Type → Type} {β γ : Type}
    (oracle : {ι : Type} → F ι → ι) (f : β → FreeM F γ) :
    ∀ xs : List β, (mapFreeM f xs).eval oracle = xs.map fun x => (f x).eval oracle
  | [] => rfl
  | x :: xs => by
    simp [mapFreeM, eval_mapFreeM oracle f xs]

/-- **Correctness of Base-`b` Bulk Exponentiation**: for `b ≥ 1` and `∀ i, es i < b ^ d`,
`bulkPow b d x es` evaluates to `fun i => x ^ (es i)` under the honest oracle. -/
theorem eval_bulkPow [CommMonoid α] [Add α] [Sub α] {n b d : ℕ} (hb : 0 < b) (x : α)
    (es : Fin n → ℕ) (hes : ∀ i, es i < b ^ d) :
    (bulkPow b d x es).eval honest = fun i => x ^ (es i) := by
  funext i
  have ht := eval_powTable b d x
  simp only [bulkPow, FreeM.eval_bind, ht, eval_mapFreeM, FreeM.eval_pure]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (by simp [i.isLt]), Option.map_some, Option.getD_some,
    List.getElem_ofFn, eval_evalFromTable hb d x (es i) 1 (hes i), one_mul]

private theorem cost_powRow [One α] (oracle : {ι : Type} → ArithQuery α ι → ι)
    (c_add c_mul : ℕ) (y : α) :
    ∀ (r : ℕ) (cur : α),
      (powRow y r cur).cost oracle (weight c_add c_mul) = r * c_mul
  | 0, _ => by simp [powRow]
  | r + 1, cur => by
    simp only [powRow, FreeM.cost_bind, doMul, FreeM.cost_lift, weight,
      cost_powRow oracle c_add c_mul y r, FreeM.cost_pure]
    ring

private theorem cost_powTable [One α] (oracle : {ι : Type} → ArithQuery α ι → ι)
    (c_add c_mul : ℕ) (b : ℕ) :
    ∀ (d : ℕ) (y : α),
      (powTable b d y).cost oracle (weight c_add c_mul) = d * b * c_mul
  | 0, _ => by simp [powTable]
  | d + 1, y => by
    simp only [powTable, FreeM.cost_bind, cost_powRow, cost_powTable oracle c_add c_mul b d,
      FreeM.cost_pure]
    ring

private theorem cost_evalFromTable [One α] (oracle : {ι : Type} → ArithQuery α ι → ι)
    (c_add c_mul : ℕ) (b : ℕ) :
    ∀ (tbl : List (List α)) (e : ℕ) (acc : α),
      (evalFromTable b tbl e acc).cost oracle (weight c_add c_mul) = tbl.length * c_mul
  | [], _, _ => by simp [evalFromTable]
  | row :: rows, e, acc => by
    simp only [evalFromTable, FreeM.cost_bind, doMul, FreeM.cost_lift, weight,
      cost_evalFromTable oracle c_add c_mul b rows, List.length_cons]
    ring

private theorem length_eval_powTable [One α] (oracle : {ι : Type} → ArithQuery α ι → ι)
    (b : ℕ) :
    ∀ (d : ℕ) (y : α), ((powTable b d y).eval oracle).length = d
  | 0, _ => rfl
  | d + 1, y => by
    simp [powTable, length_eval_powTable oracle b d]

private theorem cost_mapFreeM_const {F : Type → Type} {β γ : Type}
    (oracle : {ι : Type} → F ι → ι) (w : {ι : Type} → F ι → ℕ)
    (f : β → FreeM F γ) (k : ℕ) (hf : ∀ x, (f x).cost oracle w = k) :
    ∀ xs : List β, (mapFreeM f xs).cost oracle w = xs.length * k
  | [] => by simp [mapFreeM]
  | x :: xs => by
    simp only [mapFreeM, FreeM.cost_bind, hf x, cost_mapFreeM_const oracle w f k hf xs,
      FreeM.cost_pure, List.length_cons]
    ring

/-- **Exact Cost of Base-`b` Bulk Exponentiation**: `(b + n) * d` multiplications and `0`
additions (`O(n log_n e)` when `b = max 2 n` and `d = Nat.log b e + 1`). -/
theorem cost_bulkPow [One α] (oracle : {ι : Type} → ArithQuery α ι → ι)
    (c_add c_mul : ℕ) {n : ℕ} (b d : ℕ) (x : α) (es : Fin n → ℕ) :
    (bulkPow b d x es).cost oracle (weight c_add c_mul) = (b + n) * d * c_mul := by
  simp only [bulkPow, FreeM.cost_bind, cost_powTable, FreeM.cost_pure, add_zero]
  rw [cost_mapFreeM_const oracle (weight c_add c_mul) _ (d * c_mul)]
  · simp only [List.length_ofFn]
    ring
  · intro e
    rw [cost_evalFromTable, length_eval_powTable]

end BulkPow

end CslibFrontier.Query
