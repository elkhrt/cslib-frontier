/-
Copyright (c) 2026 Google DeepMind. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Google DeepMind
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.EqualityOracle

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Reducing `k`-Hamming Distance Submatrices to the Equality Oracle

This module proves that every `N × N` submatrix of the `k`-Hamming distance communication matrix
`HD_k^n` (for arbitrarily large ambient dimension `n`) has deterministic `Equality`-oracle
complexity `O(k log log N)`, together with
the classical `O(log n)` `Equality`-oracle binary-search protocol for `Greater-Than`, all under
standard Lean axioms.

The proof constructs a compressed binary coordinate-separating tree over the at most `2 N` row and
column strings and takes its heavy–light decomposition. Every root-to-leaf path traverses at most
`⌊log₂ (2 N)⌋` light edges, so Alice and Bob locate their lowest common ancestor (whose branching
coordinate witnesses a genuine bit difference `a x i ≠ b y i`) using one binary search over the
light-edge prefix (`O(log log N)` `Equality` queries) and one `Greater-Than` comparison of exit
depths along the shared heavy path (`O(log log N)` `Equality` queries). The party exiting first
locally flips coordinate `i`, decrementing `hammingDist (a x) (b y)` by `1`, and induction on `k`
completes the protocol.

## Main results

* `CslibFrontier.Communication.eqOracleComplexity_greaterThan_fin_le`: `Greater-Than` on `Fin M` has
  `D^Eq ≤ ⌈log₂ ⌈log₂ M⌉⌉ + 2`.
* `CslibFrontier.Communication.eqOracleComplexity_greaterThan_le`: `n`-bit `Greater-Than` has
  `D^Eq ≤ ⌈log₂ n⌉ + 2`.
* `CslibFrontier.Communication.eqOracleComplexity_hammingSubmatrix_le`: every submatrix
  `(x, y) ↦ decide (hammingDist (a x) (b y) ≤ k)` on `X × Y` with `max |X| |Y| ≤ N` and `2 ≤ N`
  satisfies `D^Eq ≤ 1 + k * (2 * ⌈log₂ (⌈log₂ (2 * N)⌉ + 1)⌉ + 3)`.
* `CslibFrontier.Communication.eqOracleComplexity_le_mul_hammingOracleComplexity`:
oracle-elimination
  inequality `D^Eq(f) ≤ D^{HD_k}(f) * (1 + k * (2 * ⌈log₂ (⌈log₂ (2 * |X|)⌉ + 1)⌉ + 3))`.
-/

public section

open Finset Cslib Cslib.Communication

namespace CslibFrontier.Communication

section BinarySearch

variable {X Y Z : Type*}

/-- Binary search over `{lo, …, lo + len}` for the largest index `j` satisfying a monotone
decreasing `Equality`-testable predicate `pa j x = pb j y`, assuming `pa lo x = pb lo y`. -/
private noncomputable def bsearchLast {α : ℕ → Type*} [∀ j, Finite (α j)]
    (pa : ∀ j, X → α j) (pb : ∀ j, Y → α j)
    (cont : ℕ → OracleProtocol eqOracle X Y Z) :
    (fuel lo len : ℕ) → OracleProtocol eqOracle X Y Z
  | 0, lo, _ => cont lo
  | fuel + 1, lo, len =>
      if len = 0 then cont lo
      else
        let half := len / 2
        let mid := lo + half + 1
        eqQuery (pa mid) (pb mid)
          (bsearchLast pa pb cont fuel lo half)
          (bsearchLast pa pb cont fuel mid (len - half - 1))

private theorem eval_bsearchLast {α : ℕ → Type*} [∀ j, Finite (α j)]
    (pa : ∀ j, X → α j) (pb : ∀ j, Y → α j)
    (cont : ℕ → OracleProtocol eqOracle X Y Z)
    {fuel lo len : ℕ} {x : X} {y : Y}
    (hfuel : len + 1 ≤ 2 ^ fuel)
    (hmono : ∀ j₁ j₂, j₁ ≤ j₂ → pa j₂ x = pb j₂ y → pa j₁ x = pb j₁ y)
    (hlo : pa lo x = pb lo y)
    (hhi : ∀ j, lo + len < j → pa j x ≠ pb j y) :
    ∃ jstar, lo ≤ jstar ∧ jstar ≤ lo + len ∧
      pa jstar x = pb jstar y ∧ pa (jstar + 1) x ≠ pb (jstar + 1) y ∧
      (bsearchLast pa pb cont fuel lo len).eval x y = (cont jstar).eval x y := by
  classical
  induction fuel generalizing lo len with
  | zero =>
    have hlen : len = 0 := by simp at hfuel; omega
    subst hlen
    exact ⟨lo, le_rfl, le_rfl, hlo, hhi (lo + 1) (by omega), rfl⟩
  | succ fuel ih =>
    simp only [bsearchLast]
    split_ifs with hlen0
    · subst hlen0
      exact ⟨lo, le_rfl, le_rfl, hlo, hhi (lo + 1) (by omega), rfl⟩
    · set half := len / 2
      set mid := lo + half + 1
      have hpow : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by rw [pow_succ]; ring
      have hfuel_l : half + 1 ≤ 2 ^ fuel := by omega
      have hfuel_r : len - half - 1 + 1 ≤ 2 ^ fuel := by omega
      rw [eval_eqQuery]
      by_cases hmid : pa mid x = pb mid y
      · simp only [decide_eq_true hmid, Bool.cond_true]
        have hhi' : ∀ j, mid + (len - half - 1) < j → pa j x ≠ pb j y := by
          intro j hj; exact hhi j (by omega)
        obtain ⟨jstar, h1, h2, h3, h4, h5⟩ := ih hfuel_r hmid hhi'
        exact ⟨jstar, by omega, by omega, h3, h4, h5⟩
      · simp only [decide_eq_false hmid, Bool.cond_false]
        have hhi' : ∀ j, lo + half < j → pa j x ≠ pb j y := by
          intro j hj hcontra
          exact hmid (hmono mid j (by omega) hcontra)
        obtain ⟨jstar, h1, h2, h3, h4, h5⟩ := ih hfuel_l hlo hhi'
        exact ⟨jstar, h1, by omega, h3, h4, h5⟩

private theorem depth_bsearchLast_le {α : ℕ → Type*} [∀ j, Finite (α j)]
    (pa : ∀ j, X → α j) (pb : ∀ j, Y → α j)
    {cont : ℕ → OracleProtocol eqOracle X Y Z} {d : ℕ}
    (hcont : ∀ j, (cont j).depth ≤ d) (fuel lo len : ℕ) :
    (bsearchLast pa pb cont fuel lo len).depth ≤ fuel + d := by
  induction fuel generalizing lo len with
  | zero => simpa [bsearchLast] using hcont lo
  | succ fuel ih =>
    simp only [bsearchLast]
    split_ifs
    · exact (hcont lo).trans (by omega)
    · rw [depth_eqQuery]
      have h₁ := ih lo (len / 2)
      have h₂ := ih (lo + len / 2 + 1) (len - len / 2 - 1)
      omega

/-- `Equality`-oracle protocol comparing two distinct `B`-bit big-endian natural numbers
`da x ≠ db y` (both `< 2 ^ B`), branching to `onLt` when `da x < db y` and `onGt` when
`db y < da x`, using at most `Nat.clog 2 (B + 1) + 1` queries. -/
private noncomputable def compareDistinctNat (B : ℕ) (da : X → ℕ) (db : Y → ℕ)
    (onLt onGt : OracleProtocol eqOracle X Y Z) : OracleProtocol eqOracle X Y Z :=
  -- `pa j x = pb j y` iff `j ≤ B` and the top `j` bits (`B - 1, …, B - j`) of `da x, db y` agree.
  let pa : ∀ j : ℕ, X → Option (Fin j → Bool) ⊕ Bool := fun j x ↦
    if j ≤ B then Sum.inl (some fun t ↦ (da x).testBit (B - 1 - t.1)) else Sum.inr false
  let pb : ∀ j : ℕ, Y → Option (Fin j → Bool) ⊕ Bool := fun j y ↦
    if j ≤ B then Sum.inl (some fun t ↦ (db y).testBit (B - 1 - t.1)) else Sum.inr true
  let fuel := Nat.clog 2 (B + 1)
  bsearchLast pa pb
    (fun jstar ↦
      -- First differing bit is at position `B - 1 - jstar`; `da x < db y ↔ bit(da x) = false`.
      eqQuery (fun x ↦ (da x).testBit (B - 1 - jstar)) (fun _ ↦ false) onGt onLt)
    fuel 0 B

private theorem nat_lt_of_msb_diff {a b pos : ℕ}
    (ha : a.testBit pos = false) (hb : b.testBit pos = true)
    (hhi : ∀ k, pos < k → a.testBit k = b.testBit k) : a < b := by
  have hdiv : a / 2 ^ (pos + 1) = b / 2 ^ (pos + 1) := by
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
    exact hhi _ (by omega)
  have hpow : 2 ^ (pos + 1) = 2 * 2 ^ pos := by rw [pow_succ]; ring
  have ha_bit : a / 2 ^ pos % 2 = 0 := by
    have := ha; rw [Nat.testBit_eq_decide_div_mod_eq] at this; simp at this; omega
  have hb_bit : b / 2 ^ pos % 2 = 1 := by
    have := hb; rw [Nat.testBit_eq_decide_div_mod_eq] at this; simpa using this
  have ha_mod : a % 2 ^ (pos + 1) < 2 ^ pos := by
    have h1 := Nat.div_add_mod a (2 ^ pos)
    have h2 := Nat.div_add_mod (a / 2 ^ pos) 2
    have h3 : a % 2 ^ pos < 2 ^ pos := Nat.mod_lt a (by positivity)
    have hq : a = 2 ^ (pos + 1) * (a / 2 ^ pos / 2) + a % 2 ^ pos := by
      calc a = 2 ^ pos * (2 * (a / 2 ^ pos / 2) + a / 2 ^ pos % 2) + a % 2 ^ pos := by
            rw [h2]; exact h1.symm
        _ = 2 ^ (pos + 1) * (a / 2 ^ pos / 2) + a % 2 ^ pos := by rw [ha_bit, hpow]; ring
    have hmod : a % 2 ^ (pos + 1) = a % 2 ^ pos := by
      conv_lhs => rw [hq]
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    omega
  have hb_mod : 2 ^ pos ≤ b % 2 ^ (pos + 1) := by
    have h1 := Nat.div_add_mod b (2 ^ pos)
    have h2 := Nat.div_add_mod (b / 2 ^ pos) 2
    have h3 : b % 2 ^ pos < 2 ^ pos := Nat.mod_lt b (by positivity)
    have hq : b = 2 ^ (pos + 1) * (b / 2 ^ pos / 2) + (2 ^ pos + b % 2 ^ pos) := by
      calc b = 2 ^ pos * (2 * (b / 2 ^ pos / 2) + b / 2 ^ pos % 2) + b % 2 ^ pos := by
            rw [h2]; exact h1.symm
        _ = 2 ^ (pos + 1) * (b / 2 ^ pos / 2) + (2 ^ pos + b % 2 ^ pos) := by
            rw [hb_bit, hpow]; ring
    have hmod : b % 2 ^ (pos + 1) = 2 ^ pos + b % 2 ^ pos := by
      conv_lhs => rw [hq]
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    omega
  have hadm := (Nat.div_add_mod a (2 ^ (pos + 1))).symm
  have hbdm := (Nat.div_add_mod b (2 ^ (pos + 1))).symm
  rw [hdiv] at hadm
  omega

private theorem eval_compareDistinctNat (B : ℕ) (da : X → ℕ) (db : Y → ℕ)
    (onLt onGt : OracleProtocol eqOracle X Y Z) {x : X} {y : Y}
    (ha : da x < 2 ^ B) (hb : db y < 2 ^ B) (hne : da x ≠ db y) :
    (compareDistinctNat B da db onLt onGt).eval x y =
      if da x < db y then onLt.eval x y else onGt.eval x y := by
  classical
  let pa : ∀ j : ℕ, X → Option (Fin j → Bool) ⊕ Bool := fun j x ↦
    if j ≤ B then Sum.inl (some fun t ↦ (da x).testBit (B - 1 - t.1)) else Sum.inr false
  let pb : ∀ j : ℕ, Y → Option (Fin j → Bool) ⊕ Bool := fun j y ↦
    if j ≤ B then Sum.inl (some fun t ↦ (db y).testBit (B - 1 - t.1)) else Sum.inr true
  have hiff : ∀ j, pa j x = pb j y ↔
      j ≤ B ∧ ∀ t < j, (da x).testBit (B - 1 - t) = (db y).testBit (B - 1 - t) := by
    intro j
    by_cases hj : j ≤ B
    · simp only [pa, pb, hj, ↓reduceIte, Sum.inl.injEq, Option.some.injEq, funext_iff, true_and]
      exact ⟨fun h t ht ↦ h ⟨t, ht⟩, fun h ⟨t, ht⟩ ↦ h t ht⟩
    · simp [pa, pb, hj]
  have hmono : ∀ j₁ j₂, j₁ ≤ j₂ → pa j₂ x = pb j₂ y → pa j₁ x = pb j₁ y := by
    intro j₁ j₂ h12 h2
    obtain ⟨hj2, hall⟩ := (hiff j₂).mp h2
    exact (hiff j₁).mpr ⟨h12.trans hj2, fun t ht ↦ hall t (ht.trans_le h12)⟩
  have hlo : pa 0 x = pb 0 y := (hiff 0).mpr ⟨Nat.zero_le B, fun _ ht ↦ absurd ht (by omega)⟩
  have hhi : ∀ j, 0 + B < j → pa j x ≠ pb j y := by
    intro j hj hcontra
    have := ((hiff j).mp hcontra).1
    omega
  have hfuel : B + 1 ≤ 2 ^ Nat.clog 2 (B + 1) := Nat.le_pow_clog (by norm_num) (B + 1)
  obtain ⟨jstar, _, hjB, hok, hbad, heval⟩ :=
    eval_bsearchLast pa pb _ hfuel hmono hlo hhi
  simp only [compareDistinctNat]
  rw [heval, eval_eqQuery]
  have hnotB : jstar ≠ B := by
    intro heq
    rw [heq] at hok
    obtain ⟨_, hall⟩ := (hiff B).mp hok
    apply hne
    apply Nat.eq_of_testBit_eq
    intro k
    by_cases hk : k < B
    · simpa [show B - 1 - (B - 1 - k) = k by omega] using hall (B - 1 - k) (by omega)
    · have h1 : da x < 2 ^ k := ha.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
      have h2 : db y < 2 ^ k := hb.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
      rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]
  have hjlt : jstar < B := by omega
  obtain ⟨_, hagree⟩ := (hiff jstar).mp hok
  have hdiff : (da x).testBit (B - 1 - jstar) ≠ (db y).testBit (B - 1 - jstar) := by
    intro heq_bit
    apply hbad
    refine (hiff (jstar + 1)).mpr ⟨by omega, fun t ht ↦ ?_⟩
    rcases (Nat.lt_succ_iff_lt_or_eq.mp ht) with hlt | rfl
    · exact hagree t hlt
    · exact heq_bit
  set pos := B - 1 - jstar
  have hhigher : ∀ k, pos < k → (da x).testBit k = (db y).testBit k := by
    intro k hk
    by_cases hkB : k < B
    · simpa [show B - 1 - (B - 1 - k) = k by omega] using hagree (B - 1 - k) (by omega)
    · have h1 : da x < 2 ^ k := ha.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
      have h2 : db y < 2 ^ k := hb.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
      rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]
  cases hba : (da x).testBit pos <;> cases hbb : (db y).testBit pos
  · exact absurd (hba.trans hbb.symm) hdiff
  · have hlt : da x < db y := nat_lt_of_msb_diff hba hbb hhigher
    simp [hlt]
  · have hgt : db y < da x :=
      nat_lt_of_msb_diff hbb hba (fun k hk ↦ (hhigher k hk).symm)
    have hnlt : ¬da x < db y := Nat.not_lt.mpr hgt.le
    simp [hnlt]
  · exact absurd (hba.trans hbb.symm) hdiff

private theorem depth_compareDistinctNat_le (B : ℕ) (da : X → ℕ) (db : Y → ℕ)
    {onLt onGt : OracleProtocol eqOracle X Y Z} {d : ℕ}
    (hLt : onLt.depth ≤ d) (hGt : onGt.depth ≤ d) :
    (compareDistinctNat B da db onLt onGt).depth ≤ Nat.clog 2 (B + 1) + 1 + d := by
  unfold compareDistinctNat
  have h := depth_bsearchLast_le
    (d := d + 1)
    (pa := fun j (x : X) ↦
      if j ≤ B then Sum.inl (some fun t : Fin j ↦ (da x).testBit (B - 1 - t.1))
      else Sum.inr false)
    (pb := fun j (y : Y) ↦
      if j ≤ B then Sum.inl (some fun t : Fin j ↦ (db y).testBit (B - 1 - t.1))
      else Sum.inr true)
    (cont := fun jstar ↦
      eqQuery (fun x ↦ (da x).testBit (B - 1 - jstar)) (fun _ ↦ false) onGt onLt)
    (fun _ ↦ by rw [depth_eqQuery]; omega) (Nat.clog 2 (B + 1)) 0 B
  exact h.trans (by omega)

/-- Deterministic `Equality`-oracle complexity of `Greater-Than` on `Fin M`:
`D^Eq(GT_M) ≤ ⌈log₂ (⌈log₂ M⌉ + 1)⌉ + 2`. -/
theorem eqOracleComplexity_greaterThan_fin_le (M : ℕ) :
    eqOracleComplexity (fun x y : Fin M ↦ greaterThan x y) ≤
      Nat.clog 2 (Nat.clog 2 M + 1) + 2 := by
  let B := Nat.clog 2 M
  have hBM : M ≤ 2 ^ B := Nat.le_pow_clog (by norm_num) M
  let p : OracleProtocol eqOracle (Fin M) (Fin M) Bool :=
    eqQuery id id
      (compareDistinctNat B (fun x ↦ x.1) (fun y ↦ y.1) (.output false) (.output true))
      (.output false)
  have hev : p.eval = fun x y : Fin M ↦ greaterThan x y := by
    ext x y
    simp only [p, eval_eqQuery, id_eq, greaterThan]
    by_cases hxy : x = y
    · simp [hxy]
    · simp only [decide_eq_false hxy, Bool.cond_false]
      rw [eval_compareDistinctNat B (fun x : Fin M ↦ x.1) (fun y : Fin M ↦ y.1) _ _
        (x.2.trans_le hBM) (y.2.trans_le hBM) (Fin.val_ne_of_ne hxy)]
      by_cases hlt : x.1 < y.1
      · have hngt : ¬y < x := not_lt.mpr (Fin.le_def.mpr hlt.le)
        simp [hlt, hngt]
      · have hgt : y < x := Fin.lt_def.mpr (by have := Fin.val_ne_of_ne hxy; omega)
        simp [hlt, hgt]
  have hd : p.depth ≤ Nat.clog 2 (B + 1) + 2 := by
    simp only [p, depth_eqQuery, OracleProtocol.depth_output, Nat.max_zero]
    have hc := depth_compareDistinctNat_le B (fun x : Fin M ↦ x.1) (fun y : Fin M ↦ y.1)
      (onLt := .output false) (onGt := .output true) (d := 0) (by simp) (by simp)
    omega
  exact (eqOracleComplexity_le_depth hev).trans hd

/-- Deterministic `Equality`-oracle complexity of `n`-bit `Greater-Than`:
`D^Eq(GT_n) ≤ ⌈log₂ (n + 1)⌉ + 2 = O(log n)`. -/
theorem eqOracleComplexity_greaterThan_le (n : ℕ) :
    eqOracleComplexity
        (fun x y : BitString n ↦ greaterThan (BitString.equivFin n x) (BitString.equivFin n y)) ≤
      Nat.clog 2 (n + 1) + 2 := by
  have hclog : Nat.clog 2 (2 ^ n) = n := Nat.clog_pow 2 n (by norm_num)
  calc eqOracleComplexity
        (fun x y : BitString n ↦ greaterThan (BitString.equivFin n x) (BitString.equivFin n y))
      ≤ eqOracleComplexity (fun a b : Fin (2 ^ n) ↦ greaterThan a b) :=
        eqOracleComplexity_comap_le _ (BitString.equivFin n) (BitString.equivFin n)
    _ ≤ Nat.clog 2 (Nat.clog 2 (2 ^ n) + 1) + 2 := eqOracleComplexity_greaterThan_fin_le (2 ^ n)
    _ = Nat.clog 2 (n + 1) + 2 := by rw [hclog]

end BinarySearch

section HeavyLightSeparatingTree

/-- Compressed binary coordinate-separating tree for a finite set of `n`-bit strings. -/
private inductive SepTree (n : ℕ) where
  | leaf
  | branch (coord : Fin n) (left right : SepTree n)

namespace SepTree

private def weight {n : ℕ} : SepTree n → ℕ
  | leaf => 1
  | branch _ l r => l.weight + r.weight

private theorem weight_pos {n : ℕ} (t : SepTree n) : 0 < t.weight := by
  induction t with
  | leaf => exact Nat.one_pos
  | branch _ _ _ ihl _ => simp [weight]; omega

/-- `t.Separates S` holds when no two distinct strings in `S` reach the same leaf of `t`. -/
private def Separates {n : ℕ} : SepTree n → Finset (BitString n) → Prop
  | leaf, S => S.card ≤ 1
  | branch i l r, S =>
      l.Separates (S.filter fun w ↦ w i = false) ∧
      r.Separates (S.filter fun w ↦ w i = true)

private theorem exists_split_coord {n : ℕ} {S : Finset (BitString n)} (h1 : 1 < S.card) :
    ∃ i : Fin n,
      (S.filter fun w ↦ w i = false).card < S.card ∧
      (S.filter fun w ↦ w i = true).card < S.card ∧
      0 < (S.filter fun w ↦ w i = false).card ∧
      0 < (S.filter fun w ↦ w i = true).card ∧
      (S.filter fun w ↦ w i = false).card + (S.filter fun w ↦ w i = true).card = S.card := by
  classical
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h1
  obtain ⟨i, hi⟩ := Function.ne_iff.mp huv
  let S₀ := S.filter (fun w ↦ w i = false)
  let S₁ := S.filter (fun w ↦ w i = true)
  have hsum : S₀.card + S₁.card = S.card := by
    have hdisj : Disjoint S₀ S₁ :=
      Finset.disjoint_filter.mpr (fun _ _ h₀ h₁ ↦ by rw [h₀] at h₁; cases h₁)
    have hunion : S₀ ∪ S₁ = S := by
      ext w; simp only [S₀, S₁, Finset.mem_union, Finset.mem_filter]; cases w i <;> simp
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  have hpos₀ : 0 < S₀.card := by
    cases hui : u i
    · exact Finset.card_pos.mpr ⟨u, Finset.mem_filter.mpr ⟨hu, hui⟩⟩
    · have hvi : v i = false := by cases h : v i <;> simp_all
      exact Finset.card_pos.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, hvi⟩⟩
  have hpos₁ : 0 < S₁.card := by
    cases hui : u i
    · have hvi : v i = true := by cases h : v i <;> simp_all
      exact Finset.card_pos.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, hvi⟩⟩
    · exact Finset.card_pos.mpr ⟨u, Finset.mem_filter.mpr ⟨hu, hui⟩⟩
  have hlt0 : S₀.card < S.card := by omega
  have hlt1 : S₁.card < S.card := by omega
  exact ⟨i, hlt0, hlt1, hpos₀, hpos₁, hsum⟩

/-- Build a compressed separating tree for any `S : Finset (BitString n)` with
`weight ≤ max S.card 1`. -/
private noncomputable def build {n : ℕ} (S : Finset (BitString n)) :
    { t : SepTree n // t.Separates S ∧ t.weight ≤ max S.card 1 } :=
  if hcard : S.card ≤ 1 then
    ⟨leaf, hcard, by simp [weight]⟩
  else
    let i : Fin n := (exists_split_coord (not_le.mp hcard)).choose
    have hi := (exists_split_coord (not_le.mp hcard)).choose_spec
    have hlt0 : (S.filter fun w ↦ w i = false).card < S.card := hi.1
    have hlt1 : (S.filter fun w ↦ w i = true).card < S.card := hi.2.1
    let tl := build (S.filter fun w ↦ w i = false)
    let tr := build (S.filter fun w ↦ w i = true)
    ⟨branch i tl.1 tr.1, ⟨tl.2.1, tr.2.1⟩, by
      have hwl' : tl.1.weight ≤ (S.filter fun w ↦ w i = false).card :=
        tl.2.2.trans (Nat.max_le.mpr ⟨le_rfl, hi.2.2.1⟩)
      have hwr' : tr.1.weight ≤ (S.filter fun w ↦ w i = true).card :=
        tr.2.2.trans (Nat.max_le.mpr ⟨le_rfl, hi.2.2.2.1⟩)
      have hs : (S.filter fun w ↦ w i = false).card +
          (S.filter fun w ↦ w i = true).card = S.card := hi.2.2.2.2
      have hmS : S.card ≤ max S.card 1 := Nat.le_max_left _ _
      simp only [weight]; omega⟩
termination_by S.card
decreasing_by all_goals assumption

/-- Heavy direction at an internal node: `true` iff `left.weight < right.weight`. -/
private def heavyDir {n : ℕ} (l r : SepTree n) : Bool :=
  decide (l.weight < r.weight)

private def child {n : ℕ} (l r : SepTree n) (b : Bool) : SepTree n :=
  cond b r l

private theorem two_mul_weight_light_le' {n : ℕ} (l r : SepTree n) :
    2 * (child l r (!heavyDir l r)).weight ≤ l.weight + r.weight := by
  by_cases h : l.weight < r.weight
  · simp only [heavyDir, decide_eq_true h, Bool.not_true, child, Bool.cond_false]
    omega
  · simp only [heavyDir, decide_eq_false h, Bool.not_false, child, Bool.cond_true]
    omega

/-- Walk the heavy path starting at `t` for string `w : BitString n`: returns `(steps, exitCoord,
nextLightSubtree?)`, where `steps` is the number of heavy edges traversed, `exitCoord` is `some i`
if `w` exits via a light edge at coordinate `i` (`none` at a leaf), and `nextLightSubtree?` is the
light child entered (with root-to-node light-turn path `List Bool` extended by nothing — every
node entered via a light edge is uniquely identified by its root-to-node path `List Bool`!). -/
private def walkHeavy {n : ℕ} (w : BitString n) :
    SepTree n → List Bool → ℕ × Option (Fin n) × Option (SepTree n × List Bool)
  | leaf, _ => (0, none, none)
  | branch i l r, path =>
      let hd := heavyDir l r
      if w i = hd then
        let res :=
          if hd = true then walkHeavy w r (path ++ [true])
          else walkHeavy w l (path ++ [false])
        (res.1 + 1, res.2.1, res.2.2)
      else
        (0, some i, some (child l r (!hd), path ++ [!hd]))

private theorem walkHeavy_branch_heavy {n : ℕ} (w : BitString n) (i : Fin n) (l r : SepTree n)
    (path : List Bool) (hw : w i = heavyDir l r) :
    walkHeavy w (branch i l r) path =
      let res := walkHeavy w (child l r (heavyDir l r)) (path ++ [heavyDir l r])
      (res.1 + 1, res.2.1, res.2.2) := by
  simp only [walkHeavy, hw, ↓reduceIte]
  cases hd : heavyDir l r <;> simp [child]

private theorem walkHeavy_branch_light {n : ℕ} (w : BitString n) (i : Fin n) (l r : SepTree n)
    (path : List Bool) (hw : w i ≠ heavyDir l r) :
    walkHeavy w (branch i l r) path =
      (0, some i, some (child l r (!heavyDir l r), path ++ [!heavyDir l r])) := by
  simp only [walkHeavy, hw, ↓reduceIte]

private theorem walkHeavy_steps_lt_weight {n : ℕ} (w : BitString n) (t : SepTree n)
    (path : List Bool) : (walkHeavy w t path).1 < t.weight := by
  induction t generalizing path with
  | leaf => simp [walkHeavy, weight]
  | branch i l r ihl ihr =>
    by_cases h : w i = heavyDir l r
    · rw [walkHeavy_branch_heavy w i l r path h]
      cases hd : heavyDir l r
      · have ih := ihl (path ++ [false]); have hrp := r.weight_pos
        simp only [child, Bool.cond_false, weight] at ih ⊢; omega
      · have ih := ihr (path ++ [true]); have hlp := l.weight_pos
        simp only [child, Bool.cond_true, weight] at ih ⊢; omega
    · rw [walkHeavy_branch_light w i l r path h]
      have := l.weight_pos; have := r.weight_pos
      simp only [weight]; omega

private theorem walkHeavy_next_weight {n : ℕ} (w : BitString n) (t : SepTree n) (path : List Bool)
    {t' : SepTree n} {path' : List Bool}
    (hnxt : (walkHeavy w t path).2.2 = some (t', path')) :
    2 * t'.weight ≤ t.weight := by
  induction t generalizing path with
  | leaf => simp [walkHeavy] at hnxt
  | branch i l r ihl ihr =>
    by_cases h : w i = heavyDir l r
    · rw [walkHeavy_branch_heavy w i l r path h] at hnxt
      cases hd : heavyDir l r
      · rw [hd] at hnxt; simp only [child, Bool.cond_false] at hnxt
        have ih := ihl (path ++ [false]) hnxt; have := r.weight_pos
        simp only [weight]; omega
      · rw [hd] at hnxt; simp only [child, Bool.cond_true] at hnxt
        have ih := ihr (path ++ [true]) hnxt; have := l.weight_pos
        simp only [weight]; omega
    · rw [walkHeavy_branch_light w i l r path h] at hnxt
      simp only [Option.some.injEq, Prod.mk.injEq] at hnxt
      rw [← hnxt.1, weight]
      exact two_mul_weight_light_le' l r

/-- Comparing `walkHeavy u t path` and `walkHeavy v t path` for two distinct strings `u ≠ v` in a
subset `S` separated by `t`:
- if `du = dv`, then BOTH exit via the SAME light child `some (t', path')` and `u, v` belong to the
  filtered subset `S'` separated by `t'`;
- if `du < dv`, then `ecu = some i` for some `i` with `u i ≠ v i`;
- if `dv < du`, then `ecv = some i` for some `i` with `u i ≠ v i`. -/
private theorem walkHeavy_compare {n : ℕ} {t : SepTree n} {S : Finset (BitString n)}
    (hsep : t.Separates S) {u v : BitString n} (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v)
    (path : List Bool) :
    let ru := walkHeavy u t path
    let rv := walkHeavy v t path
    (ru.1 = rv.1 → ∃ t' path' S', ru.2.2 = some (t', path') ∧ rv.2.2 = some (t', path') ∧
      t'.Separates S' ∧ u ∈ S' ∧ v ∈ S') ∧
    (ru.1 < rv.1 → ∃ i, ru.2.1 = some i ∧ u i ≠ v i) ∧
    (rv.1 < ru.1 → ∃ i, rv.2.1 = some i ∧ u i ≠ v i) := by
  induction t generalizing S path with
  | leaf =>
    exfalso
    have h2 : 1 < S.card := Finset.one_lt_card.mpr ⟨u, hu, v, hv, huv⟩
    simp only [Separates] at hsep
    omega
  | branch i l r ihl ihr =>
    obtain ⟨hsep_l, hsep_r⟩ := hsep
    set hd := heavyDir l r
    have hchild_sep : ∀ b : Bool,
        (child l r b).Separates (S.filter fun w ↦ w i = b) := by
      intro b; cases b <;> [exact hsep_l; exact hsep_r]
    by_cases hui : u i = hd <;> by_cases hvi : v i = hd
    · -- Both `u` and `v` take the heavy edge.
      have ih := (show ∀ (b : Bool), b = hd →
          let ru := walkHeavy u (child l r b) (path ++ [b])
          let rv := walkHeavy v (child l r b) (path ++ [b])
          (ru.1 = rv.1 → ∃ t' path' S', ru.2.2 = some (t', path') ∧ rv.2.2 = some (t', path') ∧
            t'.Separates S' ∧ u ∈ S' ∧ v ∈ S') ∧
          (ru.1 < rv.1 → ∃ j, ru.2.1 = some j ∧ u j ≠ v j) ∧
          (rv.1 < ru.1 → ∃ j, rv.2.1 = some j ∧ u j ≠ v j) from fun b hb ↦ by
        cases b
        · exact ihl hsep_l (Finset.mem_filter.mpr ⟨hu, hb ▸ hui⟩)
            (Finset.mem_filter.mpr ⟨hv, hb ▸ hvi⟩) (path ++ [false])
        · exact ihr hsep_r (Finset.mem_filter.mpr ⟨hu, hb ▸ hui⟩)
            (Finset.mem_filter.mpr ⟨hv, hb ▸ hvi⟩) (path ++ [true])) (heavyDir l r) rfl
      dsimp only at ih ⊢
      rw [walkHeavy_branch_heavy u i l r path hui, walkHeavy_branch_heavy v i l r path hvi]
      dsimp only
      exact ⟨fun h ↦ ih.1 (by omega), fun h ↦ ih.2.1 (by omega), fun h ↦ ih.2.2 (by omega)⟩
    · dsimp only
      rw [walkHeavy_branch_heavy u i l r path hui, walkHeavy_branch_light v i l r path hvi]
      refine ⟨fun h ↦ by dsimp only at h; omega, fun h ↦ by dsimp only at h; omega,
        fun _ ↦ ⟨i, rfl, ?_⟩⟩
      intro heq; exact hvi (heq ▸ hui)
    · dsimp only
      rw [walkHeavy_branch_light u i l r path hui, walkHeavy_branch_heavy v i l r path hvi]
      refine ⟨fun h ↦ by dsimp only at h; omega, fun _ ↦ ⟨i, rfl, ?_⟩,
        fun h ↦ by dsimp only at h; omega⟩
      intro heq; exact hui (heq.trans hvi)
    · have hu' : u i = !hd := by cases hu0 : u i <;> cases h : hd <;> simp_all
      have hv' : v i = !hd := by cases hv0 : v i <;> cases h : hd <;> simp_all
      dsimp only
      rw [walkHeavy_branch_light u i l r path hui, walkHeavy_branch_light v i l r path hvi]
      refine ⟨fun _ ↦ ⟨child l r (!hd), path ++ [!hd], S.filter (fun w ↦ w i = !hd),
        rfl, rfl, hchild_sep (!hd), Finset.mem_filter.mpr ⟨hu, hu'⟩,
        Finset.mem_filter.mpr ⟨hv, hv'⟩⟩,
        fun h ↦ by dsimp only at h; omega, fun h ↦ by dsimp only at h; omega⟩

/-- A heavy-path segment record `(headPath, heavySteps, exitCoord)`. -/
private abbrev Seg (n : ℕ) := List Bool × ℕ × Option (Fin n)

/-- Full heavy–light trace of `w : BitString n` through `t`: list of segments from root to leaf. -/
private def hlTrace {n : ℕ} (w : BitString n) (t : SepTree n) (path : List Bool) :
    List (Seg n) :=
  let r := walkHeavy w t path
  match h : r.2.2 with
  | none => [(path, r.1, r.2.1)]
  | some (t', path') =>
      have : t'.weight < t.weight := by
        have h2 := walkHeavy_next_weight w t path h
        have hp := t'.weight_pos
        omega
      (path, r.1, r.2.1) :: hlTrace w t' path'
termination_by t.weight

private theorem hlTrace_eq_of_none {n : ℕ} (w : BitString n) (t : SepTree n) (path : List Bool)
    (h : (walkHeavy w t path).2.2 = none) :
    hlTrace w t path = [(path, (walkHeavy w t path).1, (walkHeavy w t path).2.1)] := by
  rw [hlTrace]; dsimp only; split
  · rfl
  · next _ _ h' => rw [h] at h'; cases h'

private theorem hlTrace_eq_of_some {n : ℕ} (w : BitString n) (t t' : SepTree n)
    (path path' : List Bool) (h : (walkHeavy w t path).2.2 = some (t', path')) :
    hlTrace w t path =
      (path, (walkHeavy w t path).1, (walkHeavy w t path).2.1) :: hlTrace w t' path' := by
  conv_lhs => rw [hlTrace]
  dsimp only; split
  · next h' => rw [h] at h'; cases h'
  · next t₁ p₁ h' =>
    rw [h] at h'; simp only [Option.some.injEq, Prod.mk.injEq] at h'
    rw [h'.1, h'.2]

private theorem hlTrace_getElem_zero {n : ℕ} (w : BitString n) (t : SepTree n) (path : List Bool)
    (h0 : 0 < (hlTrace w t path).length) :
    (hlTrace w t path)[0] = (path, (walkHeavy w t path).1, (walkHeavy w t path).2.1) := by
  cases h : (walkHeavy w t path).2.2 with
  | none => simp [hlTrace_eq_of_none w t path h]
  | some p => simp [hlTrace_eq_of_some w t p.1 path p.2 h]

private theorem hlTrace_length_pow {n : ℕ} (w : BitString n) (t : SepTree n) (path : List Bool) :
    2 ^ ((hlTrace w t path).length - 1) ≤ t.weight := by
  cases h : (walkHeavy w t path).2.2 with
  | none =>
    rw [hlTrace_eq_of_none w t path h]
    exact t.weight_pos
  | some p =>
    rcases p with ⟨t', path'⟩
    have h2 := walkHeavy_next_weight w t path h
    have hlt : t'.weight < t.weight := by have := t'.weight_pos; omega
    have ih := hlTrace_length_pow w t' path'
    have hne : 1 ≤ (hlTrace w t' path').length := by
      cases h' : (walkHeavy w t' path').2.2 with
      | none => simp [hlTrace_eq_of_none w t' path' h']
      | some q => simp [hlTrace_eq_of_some w t' q.1 path' q.2 h']
    rw [hlTrace_eq_of_some w t t' path path' h]
    have hlen : ((path, (walkHeavy w t path).1, (walkHeavy w t path).2.1) ::
        hlTrace w t' path').length - 1 = (hlTrace w t' path').length - 1 + 1 := by
      simp; omega
    rw [hlen, pow_succ]
    omega
termination_by t.weight

private theorem hlTrace_steps_lt {n : ℕ} (w : BitString n) (t : SepTree n) (path : List Bool)
    (seg : Seg n) (hseg : seg ∈ hlTrace w t path) : seg.2.1 < t.weight := by
  rw [hlTrace] at hseg
  dsimp only at hseg
  split at hseg
  · simp only [List.mem_singleton] at hseg
    rw [hseg]
    exact walkHeavy_steps_lt_weight w t path
  · next t' path' h =>
    have h2 := walkHeavy_next_weight w t path h
    have hlt : t'.weight < t.weight := by have := t'.weight_pos; omega
    simp only [List.mem_cons] at hseg
    rcases hseg with rfl | hmem
    · exact walkHeavy_steps_lt_weight w t path
    · exact (hlTrace_steps_lt w t' path' seg hmem).trans hlt
termination_by t.weight

private theorem hlTrace_head {n : ℕ} (w : BitString n) (t : SepTree n) (path : List Bool) :
    ((hlTrace w t path).take 1).map Prod.fst = [path] ∧ 1 ≤ (hlTrace w t path).length := by
  rw [hlTrace]
  dsimp only
  split <;> simp

/-- Key heavy–light LCA lemma: if `u ≠ v ∈ S` are separated by `t`, and `j` is the maximum index
such that `hlTrace u t path` and `hlTrace v t path` both have length `> j` and share the same first
`j + 1` segment heads, then their `j`-th segments `(hu, du, ecu)` and `(hv, dv, ecv)` satisfy
`du ≠ dv`, with `ecu = some i` (`u i ≠ v i`) if `du < dv` and `ecv = some i` (`u i ≠ v i`) if
`dv < du`. -/
private theorem hlTrace_lca {n : ℕ} {t : SepTree n} {S : Finset (BitString n)}
    (hsep : t.Separates S) {u v : BitString n} (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v)
    (path : List Bool) (j : ℕ)
    (hj_u : j < (hlTrace u t path).length)
    (hj_v : j < (hlTrace v t path).length)
    (hpref : ((hlTrace u t path).take (j + 1)).map Prod.fst =
        ((hlTrace v t path).take (j + 1)).map Prod.fst)
    (hmax : ¬(j + 1 < (hlTrace u t path).length ∧ j + 1 < (hlTrace v t path).length ∧
        ((hlTrace u t path).take (j + 2)).map Prod.fst =
          ((hlTrace v t path).take (j + 2)).map Prod.fst)) :
    let su := (hlTrace u t path)[j]
    let sv := (hlTrace v t path)[j]
    su.2.1 ≠ sv.2.1 ∧
      (su.2.1 < sv.2.1 → ∃ i, su.2.2 = some i ∧ u i ≠ v i) ∧
      (sv.2.1 < su.2.1 → ∃ i, sv.2.2 = some i ∧ u i ≠ v i) := by
  have hcmp := walkHeavy_compare hsep hu hv huv path
  cases j with
  | zero =>
    have hsu := hlTrace_getElem_zero u t path hj_u
    have hsv := hlTrace_getElem_zero v t path hj_v
    simp only [hsu, hsv]
    refine ⟨fun heq ↦ ?_, hcmp.2.1, hcmp.2.2⟩
    obtain ⟨t', path', _, hnu, hnv, _, _, _⟩ := hcmp.1 heq
    apply hmax
    have hlu := hlTrace_eq_of_some u t t' path path' hnu
    have hlv := hlTrace_eq_of_some v t t' path path' hnv
    have h1u := hlTrace_head u t' path'
    have h1v := hlTrace_head v t' path'
    rw [hlu, hlv]
    refine ⟨by simp; omega, by simp; omega, ?_⟩
    simp [List.take_succ_cons, h1u.1, h1v.1]
  | succ j =>
    have hex_u : ∃ tu pu, (walkHeavy u t path).2.2 = some (tu, pu) := by
      cases h : (walkHeavy u t path).2.2 with
      | none =>
        have : (hlTrace u t path).length = 1 := by simp [hlTrace_eq_of_none u t path h]
        omega
      | some p => exact ⟨p.1, p.2, rfl⟩
    have hex_v : ∃ tv pv, (walkHeavy v t path).2.2 = some (tv, pv) := by
      cases h : (walkHeavy v t path).2.2 with
      | none =>
        have : (hlTrace v t path).length = 1 := by simp [hlTrace_eq_of_none v t path h]
        omega
      | some p => exact ⟨p.1, p.2, rfl⟩
    obtain ⟨tu, pu, hnu⟩ := hex_u
    obtain ⟨tv, pv, hnv⟩ := hex_v
    have hlu := hlTrace_eq_of_some u t tu path pu hnu
    have hlv := hlTrace_eq_of_some v t tv path pv hnv
    have hpupv : pu = pv := by
      have hju0 : 0 < (hlTrace u tu pu).length := by simp [hlu] at hj_u; omega
      have hjv0 : 0 < (hlTrace v tv pv).length := by simp [hlv] at hj_v; omega
      have hhead_u : ((hlTrace u tu pu)[0]'hju0).1 = pu := by
        rw [hlTrace_getElem_zero u tu pu hju0]
      have hhead_v : ((hlTrace v tv pv)[0]'hjv0).1 = pv := by
        rw [hlTrace_getElem_zero v tv pv hjv0]
      have htail : ((hlTrace u tu pu).take (j + 1)).map Prod.fst =
          ((hlTrace v tv pv).take (j + 1)).map Prod.fst := by
        simpa [hlu, hlv, List.take_succ_cons] using hpref
      have h0 := congr_arg (fun l ↦ l[0]?) htail
      simp only [List.getElem?_map, List.getElem?_take, Nat.zero_lt_succ, ↓reduceIte,
        List.getElem?_eq_getElem hju0, List.getElem?_eq_getElem hjv0, Option.map_some,
        Option.some.injEq] at h0
      exact hhead_u.symm.trans (h0.trans hhead_v)
    have hlen_path : ∀ (w : BitString n) (s : SepTree n) (p : List Bool) {s' p'},
        (walkHeavy w s p).2.2 = some (s', p') →
          p'.length = p.length + (walkHeavy w s p).1 + 1 := by
      intro w s
      induction s with
      | leaf => intro p _ _ h; simp [walkHeavy] at h
      | branch i l r ihl ihr =>
        intro p s' p' h
        by_cases hw : w i = heavyDir l r
        · rw [walkHeavy_branch_heavy w i l r p hw] at h ⊢
          cases hd : heavyDir l r
          · simp only [hd, child, Bool.cond_false] at h ⊢
            have ih := ihl (p ++ [false]) h; simp at ih; omega
          · simp only [hd, child, Bool.cond_true] at h ⊢
            have ih := ihr (p ++ [true]) h; simp at ih; omega
        · rw [walkHeavy_branch_light w i l r p hw] at h ⊢
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.2]; simp
    have hdu_eq_dv : (walkHeavy u t path).1 = (walkHeavy v t path).1 := by
      have h1 := hlen_path u t path hnu
      have h2 := hlen_path v t path hnv
      rw [hpupv] at h1
      omega
    obtain ⟨t', path', S', hnu', hnv', hsep', hu', hv'⟩ := hcmp.1 hdu_eq_dv
    have htu1 : tu = t' := by rw [hnu] at hnu'; exact (Prod.mk.inj (Option.some.inj hnu')).1
    have htu2 : pu = path' := by rw [hnu] at hnu'; exact (Prod.mk.inj (Option.some.inj hnu')).2
    have htv1 : tv = t' := by rw [hnv] at hnv'; exact (Prod.mk.inj (Option.some.inj hnv')).1
    rw [htu1, htu2] at hlu hnu
    rw [htv1, ← hpupv, htu2] at hlv
    have hlt_w : t'.weight < t.weight := by
      have h2 := walkHeavy_next_weight u t path hnu
      have := t'.weight_pos; omega
    have hj_u' : j < (hlTrace u t' path').length := by simp [hlu] at hj_u; omega
    have hj_v' : j < (hlTrace v t' path').length := by simp [hlv] at hj_v; omega
    have hpref' : ((hlTrace u t' path').take (j + 1)).map Prod.fst =
        ((hlTrace v t' path').take (j + 1)).map Prod.fst := by
      simpa [hlu, hlv, List.take_succ_cons] using hpref
    have hmax' : ¬(j + 1 < (hlTrace u t' path').length ∧ j + 1 < (hlTrace v t' path').length ∧
        ((hlTrace u t' path').take (j + 2)).map Prod.fst =
          ((hlTrace v t' path').take (j + 2)).map Prod.fst) := by
      intro hc
      apply hmax
      simp only [hlu, hlv, List.length_cons, List.take_succ_cons, List.map_cons,
        List.cons.injEq, true_and]
      exact ⟨by omega, by omega, hc.2.2⟩
    have ih := hlTrace_lca hsep' hu' hv' huv path' j hj_u' hj_v' hpref' hmax'
    simpa [hlu, hlv] using ih
termination_by t.weight

end SepTree

/-- Flip the bit at `ec : Option (Fin n)` of `w : BitString n` (no-op on `none`). -/
private def flipOpt {n : ℕ} (w : BitString n) : Option (Fin n) → BitString n
  | none => w
  | some i => Function.update w i (!w i)

private theorem hammingDist_flipOpt_left {n : ℕ} {u v : BitString n} {i : Fin n}
    (h : u i ≠ v i) : hammingDist (flipOpt u (some i)) v + 1 = hammingDist u v := by
  classical
  have heq : u i = !v i := by cases h1 : u i <;> cases h2 : v i <;> simp_all
  have h1 : Finset.univ.filter (fun j : Fin n ↦ u j ≠ v j) =
      insert i (Finset.univ.filter fun j : Fin n ↦ flipOpt u (some i) j ≠ v j) := by
    ext j
    by_cases hji : j = i
    · subst hji; simp [flipOpt, h]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, hji, false_or]
      rw [flipOpt, Function.update_of_ne hji]
  have hnot : i ∉ Finset.univ.filter (fun j : Fin n ↦ flipOpt u (some i) j ≠ v j) := by
    simp [flipOpt, heq]
  simp only [hammingDist, h1, Finset.card_insert_of_notMem hnot]

private theorem hammingDist_flipOpt_right {n : ℕ} {u v : BitString n} {i : Fin n}
    (h : u i ≠ v i) : hammingDist u (flipOpt v (some i)) + 1 = hammingDist u v := by
  rw [hammingDist_comm, hammingDist_flipOpt_left h.symm, hammingDist_comm]

/-- Encode the first `j + 1` segment heads of `segs` into a finite type of bounded lists of length
`≤ M` for an `Equality`-oracle query. -/
private def headPrefix {n : ℕ} (M : ℕ) (segs : List (SepTree.Seg n)) (j : ℕ) (side : Bool) :
    (Fin (j + 1) → Σ len : Fin (M + 1), Fin len.1 → Bool) ⊕ Bool :=
  if hj : j < segs.length then
    if hM : ∀ t : Fin (j + 1), (segs[t.1]'(Nat.lt_of_lt_of_le t.2 hj)).1.length ≤ M then
      Sum.inl fun t ↦
        let l := (segs[t.1]'(Nat.lt_of_lt_of_le t.2 hj)).1
        ⟨⟨l.length, Nat.lt_succ_of_le (hM t)⟩, fun r ↦ l[r.1]'(r.2)⟩
    else Sum.inr side
  else
    Sum.inr side

private theorem fin_heq_apply {n₁ n₂ : ℕ} (hn : n₁ = n₂) {f₁ : Fin n₁ → Bool}
    {f₂ : Fin n₂ → Bool} (hf : HEq f₁ f₂) (q : ℕ) (h₁ : q < n₁) (h₂ : q < n₂) :
    f₁ ⟨q, h₁⟩ = f₂ ⟨q, h₂⟩ := by
  subst hn
  cases eq_of_heq hf
  rfl

private theorem sigma_list_mk {M : ℕ} {l₁ l₂ : List Bool} (hl : l₁ = l₂)
    (h₁ : l₁.length < M + 1) (h₂ : l₂.length < M + 1) :
    (⟨⟨l₁.length, h₁⟩, fun q : Fin l₁.length ↦ l₁[q.1]⟩ :
      Σ len : Fin (M + 1), Fin len.1 → Bool) =
    ⟨⟨l₂.length, h₂⟩, fun q : Fin l₂.length ↦ l₂[q.1]⟩ := by
  subst hl
  rfl

private theorem sigma_list_eq {M : ℕ} {l₁ l₂ : List Bool}
    (h₁ : l₁.length < M + 1) (h₂ : l₂.length < M + 1)
    (hp : (⟨⟨l₁.length, h₁⟩, fun q : Fin l₁.length ↦ l₁[q.1]⟩ :
            Σ len : Fin (M + 1), Fin len.1 → Bool) =
          ⟨⟨l₂.length, h₂⟩, fun q : Fin l₂.length ↦ l₂[q.1]⟩) : l₁ = l₂ := by
  have hll : l₁.length = l₂.length := by simpa using congr_arg (fun s ↦ s.1.1) hp
  refine List.ext_getElem hll (fun q hq₁ hq₂ ↦ ?_)
  exact fin_heq_apply hll (Sigma.mk.inj_iff.mp hp).2 q hq₁ hq₂

private theorem headPrefix_eq_iff {n M : ℕ} {su sv : List (SepTree.Seg n)}
    (hMu : ∀ s ∈ su, s.1.length ≤ M) (hMv : ∀ s ∈ sv, s.1.length ≤ M) (j : ℕ) :
    headPrefix M su j false = headPrefix M sv j true ↔
      j < su.length ∧ j < sv.length ∧
        (su.take (j + 1)).map Prod.fst = (sv.take (j + 1)).map Prod.fst := by
  by_cases hju : j < su.length <;> by_cases hjv : j < sv.length
  · have hbu : ∀ t : Fin (j + 1), (su[t.1]'(Nat.lt_of_lt_of_le t.2 hju)).1.length ≤ M :=
      fun _ ↦ hMu _ (List.getElem_mem _)
    have hbv : ∀ t : Fin (j + 1), (sv[t.1]'(Nat.lt_of_lt_of_le t.2 hjv)).1.length ≤ M :=
      fun _ ↦ hMv _ (List.getElem_mem _)
    have hlhs : headPrefix M su j false = Sum.inl (fun t : Fin (j + 1) ↦
        let l := (su[t.1]'(Nat.lt_of_lt_of_le t.2 hju)).1
        (⟨⟨l.length, Nat.lt_succ_of_le (hbu t)⟩, fun r ↦ l[r.1]'(r.2)⟩ :
          Σ len : Fin (M + 1), Fin len.1 → Bool)) := by
      unfold headPrefix
      simp only [hju, ↓reduceDIte]
      split_ifs <;> rfl
    have hrhs : headPrefix M sv j true = Sum.inl (fun t : Fin (j + 1) ↦
        let l := (sv[t.1]'(Nat.lt_of_lt_of_le t.2 hjv)).1
        (⟨⟨l.length, Nat.lt_succ_of_le (hbv t)⟩, fun r ↦ l[r.1]'(r.2)⟩ :
          Σ len : Fin (M + 1), Fin len.1 → Bool)) := by
      unfold headPrefix
      simp only [hjv, ↓reduceDIte]
      split_ifs <;> rfl
    rw [hlhs, hrhs]
    simp only [Sum.inl.injEq, hju, hjv, true_and, funext_iff]
    constructor
    · intro h
      refine List.ext_getElem (by simp; omega) (fun t ht₁ ht₂ ↦ ?_)
      simp only [List.length_map, List.length_take] at ht₁
      have htj : t < j + 1 := by omega
      simp only [List.getElem_map, List.getElem_take]
      exact sigma_list_eq (Nat.lt_succ_of_le (hbu ⟨t, htj⟩))
        (Nat.lt_succ_of_le (hbv ⟨t, htj⟩)) (h ⟨t, htj⟩)
    · intro h ⟨t, htj⟩
      have hget := congr_arg (fun l ↦ l[t]?) h
      simp only [List.getElem?_map, List.getElem?_take, htj, ↓reduceIte,
        List.getElem?_eq_getElem (by omega : t < su.length),
        List.getElem?_eq_getElem (by omega : t < sv.length), Option.map_some,
        Option.some.injEq] at hget
      exact sigma_list_mk hget _ _
  · simp only [headPrefix, hjv, ↓reduceDIte, false_and, and_false, iff_false]
    split_ifs <;> simp
  · simp only [headPrefix, hju, ↓reduceDIte, false_and, iff_false]
    split_ifs <;> simp
  · simp [headPrefix, hju, hjv]

private theorem hlTrace_path_len_le {n : ℕ} (w : BitString n) (t : SepTree n) (path : List Bool)
    (s : SepTree.Seg n) (hs : s ∈ SepTree.hlTrace w t path) :
    s.1.length ≤ path.length + t.weight := by
  have hlen_next : ∀ (q : SepTree n) (p : List Bool) {q' p'},
      (SepTree.walkHeavy w q p).2.2 = some (q', p') →
        p'.length + q'.weight ≤ p.length + q.weight := by
    intro q
    induction q with
    | leaf => intro p _ _ h; simp [SepTree.walkHeavy] at h
    | branch i l r ihl ihr =>
      intro p q' p' h
      by_cases hw : w i = SepTree.heavyDir l r
      · rw [SepTree.walkHeavy_branch_heavy w i l r p hw] at h
        cases hd : SepTree.heavyDir l r
        · simp only [hd, SepTree.child, Bool.cond_false] at h
          have ih := ihl (p ++ [false]) h; have := r.weight_pos
          simp only [List.length_append, List.length_singleton, SepTree.weight] at ih ⊢; omega
        · simp only [hd, SepTree.child, Bool.cond_true] at h
          have ih := ihr (p ++ [true]) h; have := l.weight_pos
          simp only [List.length_append, List.length_singleton, SepTree.weight] at ih ⊢; omega
      · rw [SepTree.walkHeavy_branch_light w i l r p hw] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        have h2 := SepTree.two_mul_weight_light_le' l r
        have hqp : 0 < q'.weight := q'.weight_pos
        rw [← h.2, List.length_append, List.length_singleton, SepTree.weight]
        rw [h.1] at h2
        omega
  cases h : (SepTree.walkHeavy w t path).2.2 with
  | none =>
    rw [SepTree.hlTrace_eq_of_none w t path h, List.mem_singleton] at hs
    subst hs; exact Nat.le_add_right _ _
  | some pr =>
    rcases pr with ⟨t', path'⟩
    have hlt : t'.weight < t.weight := by
      have h2 := SepTree.walkHeavy_next_weight w t path h
      have := t'.weight_pos; omega
    rw [SepTree.hlTrace_eq_of_some w t t' path path' h, List.mem_cons] at hs
    rcases hs with rfl | hmem
    · exact Nat.le_add_right _ _
    · exact (hlTrace_path_len_le w t' path' s hmem).trans (hlen_next t path h)
termination_by t.weight

/-- Per-step `Equality`-oracle overhead for peeling one bit of Hamming distance on an `N × N`
submatrix: `2 * ⌈log₂ (⌈log₂ (2 * N)⌉ + 1)⌉ + 2`. -/
@[expose]
def hammingStepCost (N : ℕ) : ℕ :=
  2 * Nat.clog 2 (Nat.clog 2 (2 * N) + 1) + 2

/-- **Reducing `k`-Hamming Distance submatrices to `Equality` oracles**
: for every `k, n, N : ℕ` with `1 ≤ N`,
every pair of finite types `X, Y` with `card X ≤ N` and `card Y ≤ N`, and all maps
`a : X → BitString n`, `b : Y → BitString n` (with no restriction on `n`), the submatrix
`M(x, y) = decide (hammingDist (a x) (b y) ≤ k)` satisfies
`D^Eq(M) ≤ 1 + k * hammingStepCost N = O(k log log N)`.
-/
theorem eqOracleComplexity_hammingSubmatrix_le {X Y : Type*} [Fintype X] [Fintype Y]
    (k n N : ℕ) (hN : 1 ≤ N) (hX : Fintype.card X ≤ N) (hY : Fintype.card Y ≤ N)
    (a : X → BitString n) (b : Y → BitString n) :
    eqOracleComplexity (fun x y ↦ decide (hammingDist (a x) (b y) ≤ k)) ≤
      1 + k * hammingStepCost N := by
  classical
  induction k generalizing a b with
  | zero =>
    let p : OracleProtocol eqOracle X Y Bool :=
      OracleProtocol.query n a b (.output false) (.output true)
    have hev : p.eval = fun x y ↦ decide (hammingDist (a x) (b y) ≤ 0) := by
      ext x y
      simp only [p, OracleProtocol.eval_query, eqOracle_apply, equality, Nat.le_zero,
        hammingDist_eq_zero]
      by_cases h : a x = b y <;> simp [h]
    exact (eqOracleComplexity_le_depth hev).trans (by simp [p])
  | succ k ih =>
    let V : Finset (BitString n) := Finset.univ.image a ∪ Finset.univ.image b
    have hV_card : V.card ≤ 2 * N := by
      calc V.card ≤ (Finset.univ.image a).card + (Finset.univ.image b).card :=
            Finset.card_union_le _ _
        _ ≤ Fintype.card X + Fintype.card Y :=
            add_le_add Finset.card_image_le Finset.card_image_le
        _ ≤ 2 * N := by omega
    let built := SepTree.build V
    let T := built.1
    have hT_sep : T.Separates V := built.2.1
    have hT_wt : T.weight ≤ 2 * N := built.2.2.trans (max_le hV_card (by omega))
    let B := Nat.clog 2 (2 * N)
    have h2NB : 2 * N ≤ 2 ^ B := Nat.le_pow_clog (by norm_num) (2 * N)
    let fuel := Nat.clog 2 (B + 1)
    have hfuel : B + 1 ≤ 2 ^ fuel := Nat.le_pow_clog (by norm_num) (B + 1)
    let trA : X → List (SepTree.Seg n) := fun x ↦ SepTree.hlTrace (a x) T []
    let trB : Y → List (SepTree.Seg n) := fun y ↦ SepTree.hlTrace (b y) T []
    let pa : ∀ j : ℕ, X → _ := fun j x ↦ headPrefix (2 * N) (trA x) j false
    let pb : ∀ j : ℕ, Y → _ := fun j y ↦ headPrefix (2 * N) (trB y) j true
    let stepA : ℕ → X → ℕ := fun j x ↦
      match (trA x)[j]? with | some s => s.2.1 | none => 0
    let stepB : ℕ → Y → ℕ := fun j y ↦
      match (trB y)[j]? with | some s => s.2.1 | none => 0
    let flipA : ℕ → X → BitString n := fun j x ↦
      match (trA x)[j]? with | some s => flipOpt (a x) s.2.2 | none => a x
    let flipB : ℕ → Y → BitString n := fun j y ↦
      match (trB y)[j]? with | some s => flipOpt (b y) s.2.2 | none => b y
    have hexLt : ∀ j : ℕ, ∃ q : OracleProtocol eqOracle X Y Bool,
        q.eval = (fun x y ↦ decide (hammingDist (flipA j x) (b y) ≤ k)) ∧
        q.depth ≤ 1 + k * hammingStepCost N :=
      fun j ↦ eqOracleComplexity_le_iff.mp (ih (flipA j) b)
    have hexGt : ∀ j : ℕ, ∃ q : OracleProtocol eqOracle X Y Bool,
        q.eval = (fun x y ↦ decide (hammingDist (a x) (flipB j y) ≤ k)) ∧
        q.depth ≤ 1 + k * hammingStepCost N :=
      fun j ↦ eqOracleComplexity_le_iff.mp (ih a (flipB j))
    choose qLt hqLt_eval hqLt_depth using hexLt
    choose qGt hqGt_eval hqGt_depth using hexGt
    let search : OracleProtocol eqOracle X Y Bool :=
      bsearchLast pa pb
        (fun j ↦ compareDistinctNat B (stepA j) (stepB j) (qLt j) (qGt j))
        fuel 0 B
    let p : OracleProtocol eqOracle X Y Bool :=
      OracleProtocol.query n a b search (.output true)
    have hev : p.eval = fun x y ↦ decide (hammingDist (a x) (b y) ≤ k + 1) := by
      ext x y
      simp only [p, OracleProtocol.eval_query, eqOracle_apply, equality]
      by_cases hxy : a x = b y
      · simp [hxy]
      · simp only [decide_eq_false hxy, Bool.cond_false]
        have hMu : ∀ s ∈ trA x, s.1.length ≤ 2 * N := fun s hs ↦
          (hlTrace_path_len_le (a x) T [] s hs).trans (by simpa using hT_wt)
        have hMv : ∀ s ∈ trB y, s.1.length ≤ 2 * N := fun s hs ↦
          (hlTrace_path_len_le (b y) T [] s hs).trans (by simpa using hT_wt)
        have hlen_u : (trA x).length - 1 ≤ B := by
          have hp := (SepTree.hlTrace_length_pow (a x) T []).trans (hT_wt.trans h2NB)
          exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hp
        have hmono : ∀ j₁ j₂, j₁ ≤ j₂ → pa j₂ x = pb j₂ y → pa j₁ x = pb j₁ y := by
          intro j₁ j₂ h12 h2
          obtain ⟨hu2, hv2, hp2⟩ := (headPrefix_eq_iff hMu hMv j₂).mp h2
          refine (headPrefix_eq_iff hMu hMv j₁).mpr ⟨by omega, by omega, ?_⟩
          have htk := congr_arg (List.take (j₁ + 1)) hp2
          simpa [← List.map_take, List.take_take, show min (j₁ + 1) (j₂ + 1) = j₁ + 1 by omega]
            using htk
        have hlo : pa 0 x = pb 0 y := by
          have h1u := SepTree.hlTrace_head (a x) T []
          have h1v := SepTree.hlTrace_head (b y) T []
          exact (headPrefix_eq_iff hMu hMv 0).mpr
            ⟨h1u.2, h1v.2, h1u.1.trans h1v.1.symm⟩
        have hhi : ∀ j, 0 + B < j → pa j x ≠ pb j y := by
          intro j hj hcontra
          obtain ⟨hju, _, _⟩ := (headPrefix_eq_iff hMu hMv j).mp hcontra
          omega
        obtain ⟨jstar, _, _, hok, hbad, hseval⟩ :=
          eval_bsearchLast pa pb _ hfuel hmono hlo hhi
        change search.eval x y = _
        rw [hseval]
        obtain ⟨hju, hjv, hpref⟩ := (headPrefix_eq_iff hMu hMv jstar).mp hok
        have hmax := mt (headPrefix_eq_iff hMu hMv (jstar + 1)).mpr hbad
        have huV : a x ∈ V :=
          Finset.mem_union_left _ (Finset.mem_image_of_mem a (Finset.mem_univ x))
        have hvV : b y ∈ V :=
          Finset.mem_union_right _ (Finset.mem_image_of_mem b (Finset.mem_univ y))
        obtain ⟨hdne, hlt_case, hgt_case⟩ :=
          SepTree.hlTrace_lca hT_sep huV hvV hxy [] jstar hju hjv hpref hmax
        have hsa : stepA jstar x = (trA x)[jstar].2.1 := by
          simp [stepA, List.getElem?_eq_getElem hju]
        have hsb : stepB jstar y = (trB y)[jstar].2.1 := by
          simp [stepB, List.getElem?_eq_getElem hjv]
        have ha_lt : stepA jstar x < 2 ^ B := by
          rw [hsa]
          exact (SepTree.hlTrace_steps_lt (a x) T [] _ (List.getElem_mem hju)).trans_le
            (hT_wt.trans h2NB)
        have hb_lt : stepB jstar y < 2 ^ B := by
          rw [hsb]
          exact (SepTree.hlTrace_steps_lt (b y) T [] _ (List.getElem_mem hjv)).trans_le
            (hT_wt.trans h2NB)
        rw [eval_compareDistinctNat B (stepA jstar) (stepB jstar) _ _ ha_lt hb_lt
          (fun h ↦ hdne (hsa.symm.trans (h.trans hsb)))]
        split_ifs with hlt
        · rw [hsa, hsb] at hlt
          obtain ⟨i, hi_ec, hi_ne⟩ := hlt_case hlt
          rw [congr_fun₂ (hqLt_eval jstar) x y]
          have hfa : flipA jstar x = flipOpt (a x) (some i) := by
            simp only [flipA, List.getElem?_eq_getElem hju]
            exact congr_arg (flipOpt (a x)) hi_ec
          rw [hfa, decide_eq_decide]
          have hdec := hammingDist_flipOpt_left hi_ne
          omega
        · have hgt : (trB y)[jstar].2.1 < (trA x)[jstar].2.1 := by
            have hdne' : (trA x)[jstar].2.1 ≠ (trB y)[jstar].2.1 := hdne
            rw [hsa, hsb] at hlt; omega
          obtain ⟨i, hi_ec, hi_ne⟩ := hgt_case hgt
          rw [congr_fun₂ (hqGt_eval jstar) x y]
          have hfb : flipB jstar y = flipOpt (b y) (some i) := by
            simp only [flipB, List.getElem?_eq_getElem hjv]
            exact congr_arg (flipOpt (b y)) hi_ec
          rw [hfb, decide_eq_decide]
          have hdec := hammingDist_flipOpt_right hi_ne
          omega
    have hdepth : p.depth ≤ 1 + (k + 1) * hammingStepCost N := by
      have hcmp_d : ∀ j, (compareDistinctNat B (stepA j) (stepB j) (qLt j) (qGt j)).depth ≤
          fuel + 1 + (1 + k * hammingStepCost N) :=
        fun j ↦ depth_compareDistinctNat_le B _ _ (hqLt_depth j) (hqGt_depth j)
      have hs_d : search.depth ≤ fuel + (fuel + 1 + (1 + k * hammingStepCost N)) :=
        depth_bsearchLast_le pa pb hcmp_d fuel 0 B
      have hstep : 2 * fuel + 2 = hammingStepCost N := rfl
      simp only [p, OracleProtocol.depth_query, OracleProtocol.depth_output, Nat.max_zero]
      rw [Nat.succ_mul]
      omega
    exact (eqOracleComplexity_le_depth hev).trans hdepth

/-- **Oracle elimination from `HD_k` to `Equality`**: for every finite Boolean communication
problem `f : X → Y → Bool` with `max |X| |Y| ≤ N` and `1 ≤ N`, and every `k : ℕ`,
`D^Eq(f) ≤ D^{HD_k}(f) * (1 + k * hammingStepCost N)`. -/
theorem eqOracleComplexity_le_mul_hammingOracleComplexity {X Y : Type*} [Fintype X] [Fintype Y]
    (k N : ℕ) (hN : 1 ≤ N) (hX : Fintype.card X ≤ N) (hY : Fintype.card Y ≤ N)
    (f : X → Y → Bool) :
    eqOracleComplexity f ≤ hammingOracleComplexity k f * (1 + k * hammingStepCost N) :=
  eqOracleComplexity_le_hammingOracleComplexity_mul k f (fun m a b ↦
    eqOracleComplexity_hammingSubmatrix_le k m N hN hX hY a b)

end HeavyLightSeparatingTree

end CslibFrontier.Communication
