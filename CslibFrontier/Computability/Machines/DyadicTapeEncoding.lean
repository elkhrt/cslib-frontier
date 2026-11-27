module

public import Mathlib.Computability.TuringMachine.Tape
public import Mathlib.Data.Dyadic.Basic
public import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Dyadic Rational Encoding of Binary Turing Tapes

Canonical bijection between finitely supported binary Turing machine tapes `Turing.Tape Bool`
and the nonnegative dyadic rationals `{ q : Dyadic // 0 ≤ q }`, together with exact arithmetic
laws for head motion, cell marking/erasing, and parity reading.

## Main definitions

- `CslibFrontier.Computability.Machines.listBlankToNat`
- `CslibFrontier.Computability.Machines.natToListBlank`
- `CslibFrontier.Computability.Machines.listBlankToDyadicFrac`
- `CslibFrontier.Computability.Machines.tapeToDyadic`
- `CslibFrontier.Computability.Machines.tapeToDyadicEquiv`

## Main results

- `CslibFrontier.Computability.Machines.tapeToDyadic_move_left`
- `CslibFrontier.Computability.Machines.tapeToDyadic_move_right`
- `CslibFrontier.Computability.Machines.tapeToDyadic_write_true`
- `CslibFrontier.Computability.Machines.tapeToDyadic_write_false`
- `CslibFrontier.Computability.Machines.head_eq_true_iff_floor_mod_two`
-/

public section

namespace CslibFrontier.Computability.Machines

open Turing

/-- The dyadic rational `1/2`. -/
def dyadicHalf : Dyadic := Dyadic.ofOdd 1 1 (by decide)

@[simp]
theorem dyadicHalf_toRat : dyadicHalf.toRat = (1 / 2 : ℚ) := by
  change ({ num := 1, den := 2 ^ 1, den_nz := _, reduced := _ } : ℚ) = 1 / 2
  rw [← Rat.num_div_den { num := 1, den := 2 ^ 1, den_nz := _, reduced := _ }]
  norm_num

private theorem dyadic_toRat_zero : (0 : Dyadic).toRat = 0 := rfl

private theorem dyadic_toRat_two : (2 : Dyadic).toRat = 2 := by
  have h : (2 : Dyadic) = ((2 : ℕ) : Dyadic) := by norm_cast
  rw [h, Dyadic.toRat_natCast]
  norm_num

@[simp]
theorem two_mul_dyadicHalf : (2 : Dyadic) * dyadicHalf = 1 := by
  rw [← Dyadic.toRat_inj, Dyadic.toRat_mul, dyadic_toRat_two, dyadicHalf_toRat, Dyadic.toRat_one]
  norm_num

@[simp]
theorem dyadicHalf_mul_two : dyadicHalf * (2 : Dyadic) = 1 := by
  rw [mul_comm, two_mul_dyadicHalf]

theorem dyadicHalf_mul_toRat (q : Dyadic) : (dyadicHalf * q).toRat = q.toRat / 2 := by
  rw [Dyadic.toRat_mul, dyadicHalf_toRat]
  ring

theorem dyadicHalf_nonneg : (0 : Dyadic) ≤ dyadicHalf := by
  rw [← Dyadic.toRat_le_toRat_iff, dyadic_toRat_zero, dyadicHalf_toRat]
  norm_num

theorem dyadicHalf_pos : (0 : Dyadic) < dyadicHalf := by
  rw [← Dyadic.toRat_lt_toRat_iff, dyadic_toRat_zero, dyadicHalf_toRat]
  norm_num

private def listBoolToNat : List Bool → ℕ
  | [] => 0
  | b :: l => b.toNat + 2 * listBoolToNat l

private theorem listBoolToNat_blankExtends {l₁ l₂ : List Bool}
    (h : Turing.BlankExtends l₁ l₂) : listBoolToNat l₁ = listBoolToNat l₂ := by
  rcases h with ⟨k, rfl⟩
  induction l₁ with
  | nil =>
    simp only [List.nil_append]
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [List.replicate_succ, listBoolToNat]
      rw [← ih]
      rfl
  | cons b l ih =>
    simp only [List.cons_append, listBoolToNat, ih]

/-- Binary natural-number encoding of a finitely supported half-tape `Turing.ListBlank Bool`. -/
def listBlankToNat (l : ListBlank Bool) : ℕ :=
  l.liftOn listBoolToNat fun _ _ h ↦ listBoolToNat_blankExtends h

@[simp]
theorem listBlankToNat_mk (l : List Bool) :
    listBlankToNat (ListBlank.mk l) = l.foldr (fun b acc ↦ b.toNat + 2 * acc) 0 := by
  change listBoolToNat l = _
  induction l with
  | nil => rfl
  | cons b l ih => simp [listBoolToNat, ih]

@[simp]
theorem listBlankToNat_empty : listBlankToNat (∅ : ListBlank Bool) = 0 := by
  change listBoolToNat [] = 0
  rfl

@[simp]
theorem listBlankToNat_cons (b : Bool) (l : ListBlank Bool) :
    listBlankToNat (l.cons b) = b.toNat + 2 * listBlankToNat l := by
  refine ListBlank.induction_on l fun xs ↦ ?_
  rw [ListBlank.cons_mk]
  change listBoolToNat (b :: xs) = b.toNat + 2 * listBoolToNat xs
  rfl

theorem listBlankToNat_head_tail (l : ListBlank Bool) :
    listBlankToNat l = l.head.toNat + 2 * listBlankToNat l.tail := by
  conv_lhs => rw [← ListBlank.cons_head_tail l]
  exact listBlankToNat_cons l.head l.tail

private def natToListBool : ℕ → List Bool
  | 0 => []
  | n + 1 => (decide ((n + 1) % 2 = 1)) :: natToListBool ((n + 1) / 2)

/-- Binary decoding of a natural number into a finitely supported half-tape. -/
def natToListBlank (n : ℕ) : ListBlank Bool :=
  ListBlank.mk (natToListBool n)

@[simp]
theorem natToListBlank_zero : natToListBlank 0 = (∅ : ListBlank Bool) := by
  simp only [natToListBlank, natToListBool]
  rfl

theorem listBlankToNat_natToListBlank (n : ℕ) : listBlankToNat (natToListBlank n) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => rw [natToListBlank_zero, listBlankToNat_empty]
    | succ m =>
      have hlt : (m + 1) / 2 < m + 1 := Nat.div_lt_self (Nat.succ_pos m) (by decide)
      have hcons : natToListBlank (m + 1) =
          (natToListBlank ((m + 1) / 2)).cons (decide ((m + 1) % 2 = 1)) := by
        simp only [natToListBlank, natToListBool, ListBlank.cons_mk]
      rw [hcons, listBlankToNat_cons, ih _ hlt]
      have hmod : (decide ((m + 1) % 2 = 1)).toNat = (m + 1) % 2 := by
        rcases Nat.mod_two_eq_zero_or_one (m + 1) with h | h <;> simp [h]
      rw [hmod, Nat.mod_add_div]

theorem natToListBlank_listBlankToNat (l : ListBlank Bool) :
    natToListBlank (listBlankToNat l) = l := by
  suffices h : ∀ n (l : ListBlank Bool), listBlankToNat l = n → natToListBlank n = l from
    h _ l rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro l hl
    cases n with
    | zero =>
      rw [natToListBlank_zero]
      refine ListBlank.ext fun i ↦ ?_
      induction i generalizing l with
      | zero =>
        rw [ListBlank.nth_zero, ListBlank.nth_zero]
        have hht := listBlankToNat_head_tail l
        rw [hl] at hht
        have h0 : l.head.toNat = 0 := by omega
        have hfalse : l.head = false := by
          cases hb : l.head
          · rfl
          · simp [hb] at h0
        rw [hfalse]
        rfl
      | succ i ihi =>
        rw [ListBlank.nth_succ, ListBlank.nth_succ]
        have hht := listBlankToNat_head_tail l
        rw [hl] at hht
        have htail : listBlankToNat l.tail = 0 := by omega
        have hrem : (∅ : ListBlank Bool).tail = ∅ := rfl
        rw [hrem]
        exact ihi l.tail htail
    | succ m =>
      have hht := listBlankToNat_head_tail l
      rw [hl] at hht
      have hmod : (m + 1) % 2 = l.head.toNat := by
        have hb : l.head.toNat < 2 := by cases l.head <;> decide
        omega
      have hdiv : (m + 1) / 2 = listBlankToNat l.tail := by
        have hb : l.head.toNat < 2 := by cases l.head <;> decide
        omega
      have hlt : (m + 1) / 2 < m + 1 := Nat.div_lt_self (Nat.succ_pos m) (by decide)
      have hcons : natToListBlank (m + 1) =
          (natToListBlank ((m + 1) / 2)).cons (decide ((m + 1) % 2 = 1)) := by
        simp only [natToListBlank, natToListBool, ListBlank.cons_mk]
      rw [hcons, ih _ hlt l.tail hdiv.symm]
      have hhead : decide ((m + 1) % 2 = 1) = l.head := by
        rw [hmod]
        cases l.head <;> decide
      rw [hhead, ListBlank.cons_head_tail]

/-- The bijection between finitely supported binary half-tapes and natural numbers. -/
def listBlankNatEquiv : ListBlank Bool ≃ ℕ where
  toFun := listBlankToNat
  invFun := natToListBlank
  left_inv := natToListBlank_listBlankToNat
  right_inv := listBlankToNat_natToListBlank

private def listBoolToDyadicFrac : List Bool → Dyadic
  | [] => 0
  | b :: l => dyadicHalf * ((b.toNat : Dyadic) + listBoolToDyadicFrac l)

private theorem listBoolToDyadicFrac_blankExtends {l₁ l₂ : List Bool}
    (h : Turing.BlankExtends l₁ l₂) : listBoolToDyadicFrac l₁ = listBoolToDyadicFrac l₂ := by
  rcases h with ⟨k, rfl⟩
  induction l₁ with
  | nil =>
    simp only [List.nil_append]
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [List.replicate_succ, listBoolToDyadicFrac]
      rw [← ih]
      change (0 : Dyadic) = dyadicHalf * ((0 : Dyadic) + 0)
      rw [add_zero, mul_zero]
  | cons b l ih =>
    simp only [List.cons_append, listBoolToDyadicFrac, ih]

/-- Fractional dyadic encoding in `[0, 1)` of a right half-tape. -/
def listBlankToDyadicFrac (r : ListBlank Bool) : Dyadic :=
  r.liftOn listBoolToDyadicFrac fun _ _ h ↦ listBoolToDyadicFrac_blankExtends h

@[simp]
theorem listBlankToDyadicFrac_empty : listBlankToDyadicFrac (∅ : ListBlank Bool) = 0 := by
  change listBoolToDyadicFrac [] = 0
  rfl

@[simp]
theorem listBlankToDyadicFrac_cons (b : Bool) (r : ListBlank Bool) :
    listBlankToDyadicFrac (r.cons b) =
      dyadicHalf * ((b.toNat : Dyadic) + listBlankToDyadicFrac r) := by
  refine ListBlank.induction_on r fun xs ↦ ?_
  rw [ListBlank.cons_mk]
  change listBoolToDyadicFrac (b :: xs) =
    dyadicHalf * ((b.toNat : Dyadic) + listBoolToDyadicFrac xs)
  rfl

theorem listBlankToDyadicFrac_head_tail (r : ListBlank Bool) :
    listBlankToDyadicFrac r =
      dyadicHalf * ((r.head.toNat : Dyadic) + listBlankToDyadicFrac r.tail) := by
  conv_lhs => rw [← ListBlank.cons_head_tail r]
  exact listBlankToDyadicFrac_cons r.head r.tail

theorem two_mul_listBlankToDyadicFrac (r : ListBlank Bool) :
    (2 : Dyadic) * listBlankToDyadicFrac r =
      (r.head.toNat : Dyadic) + listBlankToDyadicFrac r.tail := by
  rw [listBlankToDyadicFrac_head_tail, ← mul_assoc, two_mul_dyadicHalf, one_mul]

theorem listBlankToDyadicFrac_nonneg (r : ListBlank Bool) :
    (0 : Dyadic) ≤ listBlankToDyadicFrac r := by
  refine ListBlank.induction_on r fun xs ↦ ?_
  change 0 ≤ listBoolToDyadicFrac xs
  induction xs with
  | nil => exact le_refl 0
  | cons b l ih =>
    simp only [listBoolToDyadicFrac]
    exact mul_nonneg dyadicHalf_nonneg (add_nonneg (Nat.cast_nonneg _) ih)

theorem listBlankToDyadicFrac_lt_one (r : ListBlank Bool) :
    listBlankToDyadicFrac r < 1 := by
  refine ListBlank.induction_on r fun xs ↦ ?_
  change listBoolToDyadicFrac xs < 1
  induction xs with
  | nil => exact zero_lt_one
  | cons b l ih =>
    simp only [listBoolToDyadicFrac]
    rw [← Dyadic.toRat_lt_toRat_iff, Dyadic.toRat_mul, dyadicHalf_toRat, Dyadic.toRat_add,
      Dyadic.toRat_natCast, Dyadic.toRat_one]
    have hlt : (listBoolToDyadicFrac l).toRat < 1 := by
      simpa [Dyadic.toRat_one] using (Dyadic.toRat_lt_toRat_iff).2 ih
    have hb : (b.toNat : ℚ) ≤ 1 := by cases b <;> norm_num
    linarith

/-- Every dyadic rational has a rational representation `m / 2^k` for some `m : ℤ` and `k : ℕ`. -/
theorem dyadic_exists_int_div_two_pow (q : Dyadic) :
    ∃ (m : ℤ) (k : ℕ), q.toRat = (m : ℚ) / (2 ^ k : ℕ) := by
  cases q with
  | zero => exact ⟨0, 0, by simp⟩
  | ofOdd n e hn =>
    rcases e with k | k
    · refine ⟨n, k, ?_⟩
      rw [← Rat.num_div_den (Dyadic.ofOdd n (Int.ofNat k) hn).toRat]
      rfl
    · refine ⟨n * (2 ^ (k + 1) : ℕ), 0, ?_⟩
      change ((n * (2 ^ (k + 1) : ℕ) : ℤ) : ℚ) = _
      simp

private theorem dyadic_toRat_eq_zero_of_lt_one {q : Dyadic} (h0 : 0 ≤ q) (h1 : q < 1)
    (hm : ∃ m : ℤ, q.toRat = (m : ℚ)) : q = 0 := by
  rcases hm with ⟨m, hm⟩
  have h0' : (0 : ℚ) ≤ q.toRat := by
    simpa [dyadic_toRat_zero] using (Dyadic.toRat_le_toRat_iff).2 h0
  have h1' : q.toRat < (1 : ℚ) := by
    simpa [Dyadic.toRat_one] using (Dyadic.toRat_lt_toRat_iff).2 h1
  rw [hm] at h0' h1'
  have hm0 : m = 0 := by
    have hle : (0 : ℤ) ≤ m := by exact_mod_cast h0'
    have hlt : m < 1 := by exact_mod_cast h1'
    omega
  rw [← Dyadic.toRat_eq_zero_iff, hm, hm0, Int.cast_zero]

private theorem exists_listBlank_of_dyadic_unitInterval :
    ∀ (k : ℕ) (q : Dyadic), 0 ≤ q → q < 1 →
      (∃ m : ℤ, q.toRat = (m : ℚ) / (2 ^ k : ℕ)) →
      ∃ r : ListBlank Bool, listBlankToDyadicFrac r = q := by
  intro k
  induction k with
  | zero =>
    intro q h0 h1 ⟨m, hm⟩
    refine ⟨∅, ?_⟩
    rw [listBlankToDyadicFrac_empty]
    exact (dyadic_toRat_eq_zero_of_lt_one h0 h1 ⟨m, by simpa using hm⟩).symm
  | succ k ih =>
    intro q h0 h1 ⟨m, hm⟩
    have h0q : (0 : ℚ) ≤ q.toRat := by
      simpa [dyadic_toRat_zero] using (Dyadic.toRat_le_toRat_iff).2 h0
    have h1q : q.toRat < 1 := by
      simpa [Dyadic.toRat_one] using (Dyadic.toRat_lt_toRat_iff).2 h1
    set b : Bool := decide (dyadicHalf ≤ q)
    set q' : Dyadic := (2 : Dyadic) * q - (b.toNat : Dyadic)
    have hq'_nonneg : 0 ≤ q' := by
      rw [← Dyadic.toRat_le_toRat_iff, dyadic_toRat_zero, Dyadic.toRat_sub, Dyadic.toRat_mul,
        dyadic_toRat_two, Dyadic.toRat_natCast]
      by_cases h : dyadicHalf ≤ q
      · have hq : (1 / 2 : ℚ) ≤ q.toRat := by
          have := (Dyadic.toRat_le_toRat_iff).2 h
          rwa [dyadicHalf_toRat] at this
        simp only [b, decide_eq_true_eq.mpr h, Bool.toNat_true, Nat.cast_one]
        linarith
      · simp only [b, decide_eq_false h, Bool.toNat_false, Nat.cast_zero, sub_zero]
        linarith
    have hq'_lt_one : q' < 1 := by
      rw [← Dyadic.toRat_lt_toRat_iff, Dyadic.toRat_sub, Dyadic.toRat_mul, dyadic_toRat_two,
        Dyadic.toRat_natCast, Dyadic.toRat_one]
      by_cases h : dyadicHalf ≤ q
      · simp only [b, decide_eq_true_eq.mpr h, Bool.toNat_true, Nat.cast_one]
        linarith
      · have hq : q.toRat < (1 / 2 : ℚ) := by
          have := (Dyadic.toRat_lt_toRat_iff).2 (lt_of_not_ge h)
          rwa [dyadicHalf_toRat] at this
        simp only [b, decide_eq_false h, Bool.toNat_false, Nat.cast_zero, sub_zero]
        linarith
    have hq'_rat : ∃ m' : ℤ, q'.toRat = (m' : ℚ) / (2 ^ k : ℕ) := by
      refine ⟨m - (b.toNat : ℤ) * (2 ^ k : ℕ), ?_⟩
      rw [Dyadic.toRat_sub, Dyadic.toRat_mul, dyadic_toRat_two, Dyadic.toRat_natCast, hm]
      have hpow : ((2 ^ (k + 1) : ℕ) : ℚ) = 2 * ((2 ^ k : ℕ) : ℚ) := by
        push_cast [pow_succ]
        ring
      have hpow_ne : ((2 ^ k : ℕ) : ℚ) ≠ 0 := by positivity
      rw [hpow]
      push_cast
      field_simp [hpow_ne]
    obtain ⟨r', hr'⟩ := ih q' hq'_nonneg hq'_lt_one hq'_rat
    refine ⟨r'.cons b, ?_⟩
    rw [listBlankToDyadicFrac_cons, hr']
    rw [← Dyadic.toRat_inj, Dyadic.toRat_mul, dyadicHalf_toRat, Dyadic.toRat_add,
      Dyadic.toRat_natCast, Dyadic.toRat_sub, Dyadic.toRat_mul, dyadic_toRat_two,
      Dyadic.toRat_natCast]
    ring

theorem listBlankToDyadicFrac_injective : Function.Injective listBlankToDyadicFrac := by
  intro r₁ r₂ h
  suffices ∀ (n : ℕ) (r₁ r₂ : ListBlank Bool),
      listBlankToDyadicFrac r₁ = listBlankToDyadicFrac r₂ → r₁.nth n = r₂.nth n from
    ListBlank.ext fun n ↦ this n r₁ r₂ h
  intro n
  induction n with
  | zero =>
    intro r₁ r₂ h
    rw [ListBlank.nth_zero, ListBlank.nth_zero]
    have h2 : (2 : Dyadic) * listBlankToDyadicFrac r₁ = (2 : Dyadic) * listBlankToDyadicFrac r₂ :=
      congrArg ((2 : Dyadic) * ·) h
    rw [two_mul_listBlankToDyadicFrac, two_mul_listBlankToDyadicFrac] at h2
    have hr := congrArg Dyadic.toRat h2
    rw [Dyadic.toRat_add, Dyadic.toRat_add, Dyadic.toRat_natCast, Dyadic.toRat_natCast] at hr
    have h1a : (0 : ℚ) ≤ (listBlankToDyadicFrac r₁.tail).toRat := by
      simpa [dyadic_toRat_zero] using
        (Dyadic.toRat_le_toRat_iff).2 (listBlankToDyadicFrac_nonneg r₁.tail)
    have h1b : (listBlankToDyadicFrac r₁.tail).toRat < 1 := by
      simpa [Dyadic.toRat_one] using
        (Dyadic.toRat_lt_toRat_iff).2 (listBlankToDyadicFrac_lt_one r₁.tail)
    have h2a : (0 : ℚ) ≤ (listBlankToDyadicFrac r₂.tail).toRat := by
      simpa [dyadic_toRat_zero] using
        (Dyadic.toRat_le_toRat_iff).2 (listBlankToDyadicFrac_nonneg r₂.tail)
    have h2b : (listBlankToDyadicFrac r₂.tail).toRat < 1 := by
      simpa [Dyadic.toRat_one] using
        (Dyadic.toRat_lt_toRat_iff).2 (listBlankToDyadicFrac_lt_one r₂.tail)
    cases hb₁ : r₁.head <;> cases hb₂ : r₂.head <;> simp_all <;> linarith
  | succ n ih =>
    intro r₁ r₂ h
    rw [ListBlank.nth_succ, ListBlank.nth_succ]
    apply ih
    have hhead : r₁.head = r₂.head := by
      have h2 : (2 : Dyadic) * listBlankToDyadicFrac r₁ = (2 : Dyadic) * listBlankToDyadicFrac r₂ :=
        congrArg ((2 : Dyadic) * ·) h
      rw [two_mul_listBlankToDyadicFrac, two_mul_listBlankToDyadicFrac] at h2
      have hr := congrArg Dyadic.toRat h2
      rw [Dyadic.toRat_add, Dyadic.toRat_add, Dyadic.toRat_natCast, Dyadic.toRat_natCast] at hr
      have h1a : (0 : ℚ) ≤ (listBlankToDyadicFrac r₁.tail).toRat := by
        simpa [dyadic_toRat_zero] using
          (Dyadic.toRat_le_toRat_iff).2 (listBlankToDyadicFrac_nonneg r₁.tail)
      have h1b : (listBlankToDyadicFrac r₁.tail).toRat < 1 := by
        simpa [Dyadic.toRat_one] using
          (Dyadic.toRat_lt_toRat_iff).2 (listBlankToDyadicFrac_lt_one r₁.tail)
      have h2a : (0 : ℚ) ≤ (listBlankToDyadicFrac r₂.tail).toRat := by
        simpa [dyadic_toRat_zero] using
          (Dyadic.toRat_le_toRat_iff).2 (listBlankToDyadicFrac_nonneg r₂.tail)
      have h2b : (listBlankToDyadicFrac r₂.tail).toRat < 1 := by
        simpa [Dyadic.toRat_one] using
          (Dyadic.toRat_lt_toRat_iff).2 (listBlankToDyadicFrac_lt_one r₂.tail)
      cases hb₁ : r₁.head <;> cases hb₂ : r₂.head <;> simp_all <;> linarith
    have h2 : (2 : Dyadic) * listBlankToDyadicFrac r₁ = (2 : Dyadic) * listBlankToDyadicFrac r₂ :=
      congrArg ((2 : Dyadic) * ·) h
    rw [two_mul_listBlankToDyadicFrac, two_mul_listBlankToDyadicFrac, hhead] at h2
    exact add_left_cancel h2

/-- The bijection between finitely supported right half-tapes and dyadic rationals in `[0, 1)`. -/
noncomputable def listBlankDyadicFracEquiv :
    ListBlank Bool ≃ { q : Dyadic // 0 ≤ q ∧ q < 1 } :=
  Equiv.ofBijective
    (fun r ↦ ⟨listBlankToDyadicFrac r, listBlankToDyadicFrac_nonneg r,
      listBlankToDyadicFrac_lt_one r⟩)
    ⟨fun _ _ h ↦ listBlankToDyadicFrac_injective (congrArg Subtype.val h),
     fun ⟨q, h0, h1⟩ ↦ by
       obtain ⟨m, k, hm⟩ := dyadic_exists_int_div_two_pow q
       obtain ⟨r, hr⟩ := exists_listBlank_of_dyadic_unitInterval k q h0 h1 ⟨m, hm⟩
       exact ⟨r, Subtype.ext hr⟩⟩

/-- The dyadic rational encoding of a binary Turing tape `T : Turing.Tape Bool`. -/
def tapeToDyadic (T : Tape Bool) : Dyadic :=
  ((2 * listBlankToNat T.left + T.head.toNat : ℕ) : Dyadic) + listBlankToDyadicFrac T.right

theorem tapeToDyadic_nonneg (T : Tape Bool) : (0 : Dyadic) ≤ tapeToDyadic T :=
  add_nonneg (Nat.cast_nonneg _) (listBlankToDyadicFrac_nonneg T.right)

theorem floor_tapeToDyadic (T : Tape Bool) :
    ⌊(tapeToDyadic T).toRat⌋ = (2 * listBlankToNat T.left + T.head.toNat : ℤ) := by
  rw [tapeToDyadic, Dyadic.toRat_add, Dyadic.toRat_natCast]
  have h0 : (0 : ℚ) ≤ (listBlankToDyadicFrac T.right).toRat := by
    simpa [dyadic_toRat_zero] using
      (Dyadic.toRat_le_toRat_iff).2 (listBlankToDyadicFrac_nonneg T.right)
  have h1 : (listBlankToDyadicFrac T.right).toRat < 1 := by
    simpa [Dyadic.toRat_one] using
      (Dyadic.toRat_lt_toRat_iff).2 (listBlankToDyadicFrac_lt_one T.right)
  rw [Int.floor_eq_iff]
  constructor
  · push_cast
    linarith
  · push_cast
    linarith

/-- Reading the current cell of `T` corresponds to checking parity of `⌊(tapeToDyadic T).toRat⌋`. -/
theorem head_eq_true_iff_floor_mod_two (T : Tape Bool) :
    T.head = true ↔ ⌊(tapeToDyadic T).toRat⌋ % 2 = 1 := by
  rw [floor_tapeToDyadic]
  cases T.head <;> simp

/-- Moving the reading head to the left divides the dyadic tape coordinate by `2`. -/
theorem tapeToDyadic_move_left (T : Tape Bool) :
    tapeToDyadic (T.move Dir.left) = dyadicHalf * tapeToDyadic T := by
  rcases T with ⟨a, L, R⟩
  simp only [Tape.move, tapeToDyadic, listBlankToDyadicFrac_cons]
  rw [← Dyadic.toRat_inj]
  have hL : listBlankToNat L = L.head.toNat + 2 * listBlankToNat L.tail :=
    listBlankToNat_head_tail L
  rw [hL]
  simp only [Dyadic.toRat_add, Dyadic.toRat_mul, Dyadic.toRat_natCast, dyadicHalf_toRat]
  push_cast
  ring

/-- Moving the reading head to the left adds `-(1/2) * q` to the dyadic coordinate `q`. -/
theorem tapeToDyadic_move_left_sub (T : Tape Bool) :
    tapeToDyadic (T.move Dir.left) = tapeToDyadic T + (-dyadicHalf) * tapeToDyadic T := by
  rw [tapeToDyadic_move_left, ← Dyadic.toRat_inj]
  simp only [Dyadic.toRat_add, Dyadic.toRat_mul, Dyadic.toRat_neg, dyadicHalf_toRat]
  ring

/-- Moving the reading head to the right multiplies the dyadic tape coordinate by `2`. -/
theorem tapeToDyadic_move_right (T : Tape Bool) :
    tapeToDyadic (T.move Dir.right) = (2 : Dyadic) * tapeToDyadic T := by
  rcases T with ⟨a, L, R⟩
  simp only [Tape.move, tapeToDyadic, listBlankToNat_cons]
  rw [← Dyadic.toRat_inj]
  have hR := congrArg Dyadic.toRat (two_mul_listBlankToDyadicFrac R)
  rw [Dyadic.toRat_mul, dyadic_toRat_two, Dyadic.toRat_add, Dyadic.toRat_natCast] at hR
  simp only [Dyadic.toRat_add, Dyadic.toRat_mul, dyadic_toRat_two, Dyadic.toRat_natCast]
  push_cast
  linarith

/-- Moving the reading head to the right adds `q` to the dyadic coordinate `q`. -/
theorem tapeToDyadic_move_right_add (T : Tape Bool) :
    tapeToDyadic (T.move Dir.right) = tapeToDyadic T + tapeToDyadic T := by
  rw [tapeToDyadic_move_right, two_mul]

/-- Replacing `0` (`false`) by `1` (`true`) at the head cell adds `1` to the dyadic coordinate. -/
theorem tapeToDyadic_write_true (T : Tape Bool) (h : T.head = false) :
    tapeToDyadic (T.write true) = tapeToDyadic T + 1 := by
  rcases T with ⟨a, L, R⟩
  simp only at h
  subst h
  simp only [Tape.write, tapeToDyadic, Bool.toNat_true, Bool.toNat_false, add_zero]
  rw [← Dyadic.toRat_inj]
  simp only [Dyadic.toRat_add, Dyadic.toRat_natCast, Dyadic.toRat_one]
  push_cast
  ring

/-- Replacing `1` (`true`) by `0` (`false`) at the head cell subtracts `1`. -/
theorem tapeToDyadic_write_false (T : Tape Bool) (h : T.head = true) :
    tapeToDyadic (T.write false) = tapeToDyadic T - 1 := by
  rcases T with ⟨a, L, R⟩
  simp only at h
  subst h
  simp only [Tape.write, tapeToDyadic, Bool.toNat_false, Bool.toNat_true, add_zero]
  rw [← Dyadic.toRat_inj]
  simp only [Dyadic.toRat_add, Dyadic.toRat_sub, Dyadic.toRat_natCast, Dyadic.toRat_one]
  push_cast
  ring

/-- The dyadic tape encoding `tapeToDyadic` is injective. -/
theorem tapeToDyadic_injective : Function.Injective tapeToDyadic := by
  intro T₁ T₂ h
  have hfloor : ⌊(tapeToDyadic T₁).toRat⌋ = ⌊(tapeToDyadic T₂).toRat⌋ := by
    rw [h]
  rw [floor_tapeToDyadic, floor_tapeToDyadic] at hfloor
  have hnat : 2 * listBlankToNat T₁.left + T₁.head.toNat =
      2 * listBlankToNat T₂.left + T₂.head.toNat := by
    omega
  have hhead : T₁.head = T₂.head := by
    cases hb₁ : T₁.head <;> cases hb₂ : T₂.head <;> simp_all <;> omega
  have hleft : T₁.left = T₂.left := by
    apply listBlankNatEquiv.injective
    change listBlankToNat T₁.left = listBlankToNat T₂.left
    rw [hhead] at hnat
    omega
  have hright : T₁.right = T₂.right := by
    apply listBlankToDyadicFrac_injective
    have h' := h
    simp only [tapeToDyadic, hleft, hhead] at h'
    exact add_left_cancel h'
  rcases T₁ with ⟨a₁, L₁, R₁⟩
  rcases T₂ with ⟨a₂, L₂, R₂⟩
  simp only at hhead hleft hright
  subst hhead; subst hleft; subst hright
  rfl

/-- Every nonnegative dyadic rational is the dyadic coordinate of a unique binary Turing tape. -/
theorem tapeToDyadic_surjective (q : Dyadic) (hq : 0 ≤ q) :
    ∃ T : Tape Bool, tapeToDyadic T = q := by
  set n : ℤ := ⌊q.toRat⌋
  have hn_nonneg : 0 ≤ n :=
    Int.floor_nonneg.mpr (by simpa [dyadic_toRat_zero] using (Dyadic.toRat_le_toRat_iff).2 hq)
  set m : ℕ := n.toNat
  have hm_eq : (m : ℤ) = n := Int.toNat_of_nonneg hn_nonneg
  set r : Dyadic := q - (m : Dyadic)
  have hr_nonneg : 0 ≤ r := by
    rw [← Dyadic.toRat_le_toRat_iff, dyadic_toRat_zero, Dyadic.toRat_sub, Dyadic.toRat_natCast]
    have hle : (n : ℚ) ≤ q.toRat := Int.floor_le q.toRat
    have hmn : (m : ℚ) = (n : ℚ) := by exact_mod_cast hm_eq
    linarith
  have hr_lt_one : r < 1 := by
    rw [← Dyadic.toRat_lt_toRat_iff, Dyadic.toRat_sub, Dyadic.toRat_natCast, Dyadic.toRat_one]
    have hlt : q.toRat < (n : ℚ) + 1 := Int.lt_floor_add_one q.toRat
    have hmn : (m : ℚ) = (n : ℚ) := by exact_mod_cast hm_eq
    linarith
  obtain ⟨R, hR⟩ := listBlankDyadicFracEquiv.surjective ⟨r, hr_nonneg, hr_lt_one⟩
  have hR' : listBlankToDyadicFrac R = r := congrArg Subtype.val hR
  refine ⟨⟨decide (m % 2 = 1), natToListBlank (m / 2), R⟩, ?_⟩
  simp only [tapeToDyadic, listBlankToNat_natToListBlank, hR']
  have hmod : (decide (m % 2 = 1)).toNat = m % 2 := by
    rcases Nat.mod_two_eq_zero_or_one m with h | h <;> simp [h]
  rw [hmod, Nat.div_add_mod]
  exact add_sub_cancel (m : Dyadic) q

/-- The canonical bijection between binary Turing tapes and nonnegative dyadic rationals. -/
noncomputable def tapeToDyadicEquiv : Tape Bool ≃ { q : Dyadic // 0 ≤ q } :=
  Equiv.ofBijective
    (fun T ↦ ⟨tapeToDyadic T, tapeToDyadic_nonneg T⟩)
    ⟨fun _ _ h ↦ tapeToDyadic_injective (congrArg Subtype.val h),
     fun ⟨q, hq⟩ ↦ by
       obtain ⟨T, hT⟩ := tapeToDyadic_surjective q hq
       exact ⟨T, Subtype.ext hT⟩⟩

@[simp]
theorem tapeToDyadicEquiv_apply (T : Tape Bool) :
    (tapeToDyadicEquiv T).val = tapeToDyadic T := by
  rfl

@[simp]
theorem tapeToDyadic_tapeToDyadicEquiv_symm (q : { q : Dyadic // 0 ≤ q }) :
    tapeToDyadic (tapeToDyadicEquiv.symm q) = q.val := by
  rw [← tapeToDyadicEquiv_apply, tapeToDyadicEquiv.apply_symm_apply]

end CslibFrontier.Computability.Machines
