module

public import CslibFrontier.Computability.Communication.DirectProduct.AMSearch
import CslibFrontier.Probability.IID
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Strong Direct Product Theorems for Disjointness and Arthur-Merlin Protocols

Parallel binary-search reduction from `k`-fold intersection search `SEARCH_n^(k)` to `k`-fold
Nondisjointness `NDISJ_n^(k)`, yielding strong direct product theorems:

* `composeBinSearch`: parallel binary-search composition turning an AM protocol for `NDISJ_n^(k)`
  into an AM protocol for `SEARCH_n^(k)` with logarithmic communication overhead.
* `sdpt_am_ndisjK`: strong direct product theorem for AM protocols with ambiguity `2 ^ (ε k)`
  computing `NDISJ_n^(k)`.
* `sdpt_ndisjK` and `sdpt_disjK`: strong direct product theorems for bounded-communication
  public-coin randomized protocols computing `NDISJ_n^(k)` and `DISJ_n^(k)`.
* `unambiguous_am_ndisj_lower_bound`: linear `Ω(n)` communication lower bound for unambiguous
  (`t = 1`) AM protocols computing single-instance `NDISJ_n`.
-/

public section

namespace CslibFrontier.Computability.Communication

open Cslib Finset Cslib.Communication

/-! ### Parallel Binary Search Reduction (`SEARCH_n^(k)` ≤ `NDISJ_n^(k)`) and & 11 -/

/-- Mask a bit string `x : BitString n` to the half-open interval `[L, R)`. -/
private def maskInterval {n : ℕ} (L R : ℕ) (x : BitString n) : BitString n :=
  fun j => if L ≤ j.val ∧ j.val < R then x j else false

/-- Left-half mask of a vector of intervals `iv : Fin k → ℕ × ℕ`. -/
private def maskLeftVec {n k : ℕ} (iv : Fin k → ℕ × ℕ) (x : Fin k → BitString n) :
    Fin k → BitString n :=
  fun i => maskInterval (iv i).1 (((iv i).1 + (iv i).2) / 2) (x i)

/-- Update intervals after a binary-search step with answer `b : BitString k`. -/
private def nextIntervals {k : ℕ} (iv : Fin k → ℕ × ℕ) (b : BitString k) : Fin k → ℕ × ℕ :=
  fun i =>
    let M := ((iv i).1 + (iv i).2) / 2
    if b i = true then ((iv i).1, M) else (M, (iv i).2)

/-- Sequence of intervals determined by round answers `bs : Fin s → BitString k`, starting from
`(0, n)` on every block. -/
private def runIntervals (n k : ℕ) : {r : ℕ} → (Fin r → BitString k) → Fin k → ℕ × ℕ
  | 0, _ => fun _ => (0, n)
  | r + 1, bs => nextIntervals (runIntervals n k (fun j : Fin r => bs j.castSucc)) (bs (Fin.last r))

/-- Interval length shrinks by half at each step: after `r` steps, `R - L ≤ ceil(n / 2 ^ r)`. -/
private theorem runIntervals_bounds (n k : ℕ) :
    ∀ {r : ℕ} (bs : Fin r → BitString k) (i : Fin k),
      (runIntervals n k bs i).1 ≤ (runIntervals n k bs i).2 ∧
      (runIntervals n k bs i).2 ≤ n ∧
      (runIntervals n k bs i).2 - (runIntervals n k bs i).1 ≤ (n + 2 ^ r - 1) / 2 ^ r
  | 0, _, _ => by
    simp only [runIntervals, pow_zero, Nat.div_one]
    omega
  | r + 1, bs, i => by
    have ih := runIntervals_bounds n k (fun j : Fin r => bs j.castSucc) i
    set iv := runIntervals n k (fun j : Fin r => bs j.castSucc) i
    set L := iv.1
    set R := iv.2
    set M := (L + R) / 2
    have hceil : ((n + 2 ^ r - 1) / 2 ^ r + 1) / 2 ≤ (n + 2 ^ (r + 1) - 1) / 2 ^ (r + 1) := by
      have hp : 0 < 2 ^ r := Nat.two_pow_pos r
      have h1 : (n + 2 ^ r - 1) / 2 ^ r + 1 = (n + 2 * 2 ^ r - 1) / 2 ^ r := by
        have h : n + 2 * 2 ^ r - 1 = (n + 2 ^ r - 1) + 2 ^ r := by omega
        rw [h, Nat.add_div_right _ hp]
      rw [pow_succ', h1, Nat.div_div_eq_div_mul, mul_comm]
    simp only [runIntervals, nextIntervals]
    have hLR : L ≤ R := ih.1
    have hRn : R ≤ n := ih.2.1
    have hdiff : R - L ≤ (n + 2 ^ r - 1) / 2 ^ r := ih.2.2
    have hM1 : M - L ≤ (R - L + 1) / 2 := by omega
    have hM2 : R - M ≤ (R - L + 1) / 2 := by omega
    have hstep1 : M - L ≤ (n + 2 ^ (r + 1) - 1) / 2 ^ (r + 1) :=
      hM1.trans ((Nat.div_le_div_right (by omega)).trans hceil)
    have hstep2 : R - M ≤ (n + 2 ^ (r + 1) - 1) / 2 ^ (r + 1) :=
      hM2.trans ((Nat.div_le_div_right (by omega)).trans hceil)
    dsimp only [L, R, M, iv] at hLR hRn hstep1 hstep2
    split_ifs
    · exact ⟨by omega, by omega, hstep1⟩
    · exact ⟨by omega, by omega, hstep2⟩

/-- Deterministic true binary-search transcript on input `(x, y)` for `s` halving steps. -/
private def trueSearchAnswers {n k : ℕ} (x y : Fin k → BitString n) :
    (r : ℕ) → Fin r → BitString k
  | 0 => Fin.elim0
  | r + 1 =>
    let prev := trueSearchAnswers x y r
    let iv := runIntervals n k prev
    Fin.snoc prev (ndisjK n k (maskLeftVec iv x) (maskLeftVec iv y))

/-- Prefix consistency of `trueSearchAnswers`. -/
private theorem trueSearchAnswers_castSucc {n k : ℕ} (x y : Fin k → BitString n) (r : ℕ)
    (j : Fin r) :
    trueSearchAnswers x y (r + 1) j.castSucc = trueSearchAnswers x y r j := by
  simp [trueSearchAnswers, Fin.snoc_castSucc]

/-- Invariant of `trueSearchAnswers`: if `x i` and `y i` intersect, then after `r` halving steps,
the interval `runIntervals n k (trueSearchAnswers x y r) i` still contains an intersecting index. -/
private theorem trueSearchAnswers_inv {n k : ℕ} (x y : Fin k → BitString n) (i : Fin k)
    (hnd : ndisj (x i) (y i) = true) :
    ∀ r : ℕ, ∃ j : Fin n,
      (runIntervals n k (trueSearchAnswers x y r) i).1 ≤ j.val ∧
      j.val < (runIntervals n k (trueSearchAnswers x y r) i).2 ∧
      x i j = true ∧ y i j = true
  | 0 => by
    obtain ⟨j, hxj, hyj⟩ := ndisj_eq_true_iff_exists.mp hnd
    exact ⟨j, Nat.zero_le _, j.isLt, hxj, hyj⟩
  | r + 1 => by
    obtain ⟨j, hjL, hjR, hxj, hyj⟩ := trueSearchAnswers_inv x y i hnd r
    have hprev : (fun t : Fin r => trueSearchAnswers x y (r + 1) t.castSucc) =
        trueSearchAnswers x y r := funext fun t => trueSearchAnswers_castSucc x y r t
    have hlast : trueSearchAnswers x y (r + 1) (Fin.last r) =
        ndisjK n k (maskLeftVec (runIntervals n k (trueSearchAnswers x y r)) x)
          (maskLeftVec (runIntervals n k (trueSearchAnswers x y r)) y) := by
      simp [trueSearchAnswers, Fin.snoc_last]
    set iv := runIntervals n k (trueSearchAnswers x y r)
    set L := (iv i).1
    set R := (iv i).2
    set M := (L + R) / 2
    simp only [runIntervals, hprev, hlast, nextIntervals]
    by_cases hleft : ndisj (maskLeftVec iv x i) (maskLeftVec iv y i) = true
    · simp only [ndisjK_apply, hleft, ↓reduceIte]
      obtain ⟨j', hxj', hyj'⟩ := ndisj_eq_true_iff_exists.mp hleft
      simp only [maskLeftVec, maskInterval] at hxj' hyj'
      by_cases hbd : L ≤ j'.val ∧ j'.val < M
      · simp only [L, R, M] at hbd
        rw [ite_eq_left hbd] at hxj' hyj'
        exact ⟨j', hbd.1, hbd.2, hxj', hyj'⟩
      · simp only [L, R, M] at hbd
        rw [ite_eq_right hbd] at hxj'
        exact Bool.noConfusion hxj'
    · have hfalse : ndisj (maskLeftVec iv x i) (maskLeftVec iv y i) = false :=
        Bool.eq_false_iff.mpr hleft
      simp only [ndisjK_apply, hfalse, Bool.false_eq_true, ↓reduceIte]
      have hjM : M ≤ j.val := by
        by_contra hlt
        push Not at hlt
        have hbd : (iv i).1 ≤ j.val ∧ j.val < ((iv i).1 + (iv i).2) / 2 := ⟨hjL, hlt⟩
        have htrue : ndisj (maskLeftVec iv x i) (maskLeftVec iv y i) = true := by
          rw [ndisj_eq_true_iff_exists]
          exact ⟨j, by simp [maskLeftVec, maskInterval, hbd, hxj],
            by simp [maskLeftVec, maskInterval, hbd, hyj]⟩
        rw [htrue] at hfalse
        exact Bool.noConfusion hfalse
      exact ⟨j, hjM, hjR, hxj, hyj⟩

/-- Index tuple type for the parallel binary-search composition of `s + 1` nondeterministic
protocols. -/
private abbrev BinSearchIdx {n k s : ℕ}
    (Ps : Fin (s + 1) → NondetProtocol (Fin k → BitString n) (Fin k → BitString n) (BitString k)) :=
  (∀ j : Fin (s + 1), Fin (Ps j).size) ×
    (Fin k → BitString ((n + 2 ^ s - 1) / 2 ^ s)) ×
    (Fin k → BitString ((n + 2 ^ s - 1) / 2 ^ s))

/-- Round answers extracted from a rectangle-index tuple `idx`. -/
private def binSearchRoundAns {n k s : ℕ}
    (Ps : Fin (s + 1) → NondetProtocol (Fin k → BitString n) (Fin k → BitString n) (BitString k))
    (idx : ∀ j : Fin (s + 1), Fin (Ps j).size) (r : ℕ) (hr : r ≤ s) : Fin r → BitString k :=
  fun t => (Ps ⟨t.val + 1, by omega⟩).output (idx ⟨t.val + 1, by omega⟩)

/-- Round intervals determined by a rectangle-index tuple `idx`. -/
private def binSearchRoundIv {n k s : ℕ}
    (Ps : Fin (s + 1) → NondetProtocol (Fin k → BitString n) (Fin k → BitString n) (BitString k))
    (idx : ∀ j : Fin (s + 1), Fin (Ps j).size) (r : ℕ) (hr : r ≤ s) : Fin k → ℕ × ℕ :=
  runIntervals n k (binSearchRoundAns Ps idx r hr)

/-- Alice side of the composed binary-search rectangle indexed by `tup`. -/
private def binSearchAlice {n k s : ℕ}
    (Ps : Fin (s + 1) → NondetProtocol (Fin k → BitString n) (Fin k → BitString n) (BitString k))
    (tup : BinSearchIdx Ps) : Set (Fin k → BitString n) :=
  let L := (n + 2 ^ s - 1) / 2 ^ s
  let idx := tup.1
  let ux := tup.2.1
  let finalIv := binSearchRoundIv Ps idx s le_rfl
  {x | x ∈ (Ps 0).alice (idx 0) ∧
    (∀ t : Fin s, maskLeftVec (binSearchRoundIv Ps idx t.val t.isLt.le) x ∈
      (Ps t.succ).alice (idx t.succ)) ∧
    (∀ i : Fin k, ∀ d : Fin L,
      ux i d = if h : (finalIv i).1 + d.val < n then x i ⟨(finalIv i).1 + d.val, h⟩ else false)}

/-- Bob side of the composed binary-search rectangle indexed by `tup`. -/
private def binSearchBob {n k s : ℕ}
    (Ps : Fin (s + 1) → NondetProtocol (Fin k → BitString n) (Fin k → BitString n) (BitString k))
    (tup : BinSearchIdx Ps) : Set (Fin k → BitString n) :=
  let L := (n + 2 ^ s - 1) / 2 ^ s
  let idx := tup.1
  let uy := tup.2.2
  let finalIv := binSearchRoundIv Ps idx s le_rfl
  {y | y ∈ (Ps 0).bob (idx 0) ∧
    (∀ t : Fin s, maskLeftVec (binSearchRoundIv Ps idx t.val t.isLt.le) y ∈
      (Ps t.succ).bob (idx t.succ)) ∧
    (∀ i : Fin k, ∀ d : Fin L,
      uy i d = if h : (finalIv i).1 + d.val < n then y i ⟨(finalIv i).1 + d.val, h⟩ else false)}

/-- Output label of the composed binary-search rectangle indexed by `tup`. -/
private def binSearchOut {n k s : ℕ}
    (Ps : Fin (s + 1) → NondetProtocol (Fin k → BitString n) (Fin k → BitString n) (BitString k))
    (tup : BinSearchIdx Ps) : Fin k → Option (Fin n) :=
  let L := (n + 2 ^ s - 1) / 2 ^ s
  let idx := tup.1
  let ux := tup.2.1
  let uy := tup.2.2
  let finalIv := binSearchRoundIv Ps idx s le_rfl
  fun i =>
    if (Ps 0).output (idx 0) i = false then none
    else
      match (List.finRange L).find? (fun d => ux i d && uy i d) with
      | none => none
      | some d =>
        if h : (finalIv i).1 + d.val < n then some ⟨(finalIv i).1 + d.val, h⟩ else none

/-- Canonical equivalence indexing `BinSearchIdx Ps` by `Fin (Fintype.card (BinSearchIdx Ps))`. -/
private noncomputable def binSearchEquiv {n k s : ℕ}
    (Ps : Fin (s + 1) → NondetProtocol (Fin k → BitString n) (Fin k → BitString n) (BitString k)) :
    Fin (Fintype.card (BinSearchIdx Ps)) ≃ BinSearchIdx Ps :=
  (Fintype.equivFin (BinSearchIdx Ps)).symm

/-- Given `s + 1` nondeterministic protocols `Ps : Fin (s + 1) → NondetProtocol ...` for
`NDISJ_n^(k)`, compose them via `s` parallel binary-search rounds plus the trivial protocol on the
remaining `L = ceil(n / 2^s)` bits per block. -/
private noncomputable def composeBinSearch {n k s : ℕ}
    (Ps : Fin (s + 1) → NondetProtocol (Fin k → BitString n) (Fin k → BitString n) (BitString k)) :
    NondetProtocol (Fin k → BitString n) (Fin k → BitString n) (Fin k → Option (Fin n)) where
  size := Fintype.card (BinSearchIdx Ps)
  alice r := binSearchAlice Ps (binSearchEquiv Ps r)
  bob r := binSearchBob Ps (binSearchEquiv Ps r)
  output r := binSearchOut Ps (binSearchEquiv Ps r)

/-- Communication bound of `composeBinSearch`: `(s + 1) * c + 2 * k * ceil(n / 2^s)`. -/
private theorem composeBinSearch_hasComm {n k s c : ℕ}
    {Ps : Fin (s + 1) → NondetProtocol (Fin k → BitString n) (Fin k → BitString n) (BitString k)}
    (hcomm : ∀ j, (Ps j).HasComm c) :
    (composeBinSearch Ps).HasComm ((s + 1) * c + 2 * k * ((n + 2 ^ s - 1) / 2 ^ s)) := by
  set L := (n + 2 ^ s - 1) / 2 ^ s
  rw [NondetProtocol.hasComm_iff]
  unfold composeBinSearch
  dsimp only [BinSearchIdx]
  simp only [Fintype.card_prod, Fintype.card_pi, Fintype.card_bool, prod_const, card_univ,
    Fintype.card_fin]
  have hprod : ∏ j : Fin (s + 1), (Ps j).size ≤ 2 ^ ((s + 1) * c) := by
    calc ∏ j : Fin (s + 1), (Ps j).size
        ≤ ∏ _j : Fin (s + 1), 2 ^ c := prod_le_prod fun j _ => hcomm j
      _ = (2 ^ c) ^ (s + 1) := by rw [prod_const, card_univ, Fintype.card_fin]
      _ = 2 ^ ((s + 1) * c) := by rw [← pow_mul, mul_comm]
  have h2L : (2 ^ L) ^ k * (2 ^ L) ^ k = 2 ^ (2 * k * L) := by
    rw [← pow_mul, ← pow_add]
    congr 1; ring
  rw [h2L, pow_add]
  exact Nat.mul_le_mul_right _ hprod

/-- Ambiguity bound of `composeBinSearch`: at most `t ^ (s + 1)`. -/
private theorem composeBinSearch_hasAmbiguity {n k s t : ℕ}
    {Ps : Fin (s + 1) → NondetProtocol (Fin k → BitString n) (Fin k → BitString n) (BitString k)}
    (hamb : ∀ j, (Ps j).HasAmbiguity t) :
    (composeBinSearch Ps).HasAmbiguity (t ^ (s + 1)) := by
  classical
  intro x y
  -- Since `ux` and `uy` are uniquely determined by `(idx, x, y)`, count valid `idx` by induction
  -- on prefix length `m ≤ s + 1`.
  let validIdx (idx : ∀ j : Fin (s + 1), Fin (Ps j).size) : Prop :=
    (x ∈ (Ps 0).alice (idx 0) ∧ y ∈ (Ps 0).bob (idx 0)) ∧
    ∀ t : Fin s,
      maskLeftVec (binSearchRoundIv Ps idx t.val t.isLt.le) x ∈ (Ps t.succ).alice (idx t.succ) ∧
      maskLeftVec (binSearchRoundIv Ps idx t.val t.isLt.le) y ∈ (Ps t.succ).bob (idx t.succ)
  have hle_idx : (composeBinSearch Ps).ambiguityAt x y ≤
      #{idx : ∀ j : Fin (s + 1), Fin (Ps j).size | validIdx idx} := by
    rw [NondetProtocol.ambiguityAt_eq_card]
    unfold composeBinSearch
    refine Finset.card_le_card_of_injOn (fun r => (binSearchEquiv Ps r).1) ?_ ?_
    · intro r hr
      obtain ⟨hx, hy⟩ := (mem_filter.mp hr).2
      exact mem_filter.mpr ⟨mem_univ _, ⟨hx.1, hy.1⟩, fun t => ⟨hx.2.1 t, hy.2.1 t⟩⟩
    · intro r₁ hr₁ r₂ hr₂ heq
      obtain ⟨hx₁, hy₁⟩ := (mem_filter.mp hr₁).2
      obtain ⟨hx₂, hy₂⟩ := (mem_filter.mp hr₂).2
      apply (binSearchEquiv Ps).injective
      refine Prod.ext heq (Prod.ext ?_ ?_)
      · funext i d
        have h1 := hx₁.2.2 i d
        have h2 := hx₂.2.2 i d
        dsimp only at heq
        rw [h1, h2, heq]
      · funext i d
        have h1 := hy₁.2.2 i d
        have h2 := hy₂.2.2 i d
        dsimp only at heq
        rw [h1, h2, heq]
  -- Count valid prefixes of length `m` (`1 ≤ m ≤ s + 1`) by induction on `m`.
  have hprefix : ∀ (m : ℕ) (hm : m ≤ s),
      #{pref : ∀ j : Fin (m + 1), Fin (Ps ⟨j.val, by omega⟩).size |
        (x ∈ (Ps 0).alice (pref 0) ∧ y ∈ (Ps 0).bob (pref 0)) ∧
        ∀ t : Fin m,
          let prevAns : Fin t.val → BitString k := fun u =>
            (Ps ⟨u.val + 1, by omega⟩).output (pref ⟨u.val + 1, by omega⟩)
          let iv := runIntervals n k prevAns
          maskLeftVec iv x ∈ (Ps ⟨t.val + 1, by omega⟩).alice (pref ⟨t.val + 1, by omega⟩) ∧
          maskLeftVec iv y ∈ (Ps ⟨t.val + 1, by omega⟩).bob (pref ⟨t.val + 1, by omega⟩)} ≤
        t ^ (m + 1) := by
    intro m
    induction m with
    | zero =>
      intro _
      rw [pow_one]
      refine le_trans ?_ (hamb 0 x y)
      rw [NondetProtocol.ambiguityAt_eq_card]
      refine Finset.card_le_card_of_injOn (fun pref => pref 0) ?_ ?_
      · intro pref hp
        exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hp).2.1⟩
      · intro p₁ _ p₂ _ h
        funext j; rw [Fin.eq_zero j]; exact h
    | succ m ih =>
      intro hm
      let PPrev := univ.filter fun pref : ∀ j : Fin (m + 1), Fin (Ps ⟨j.val, by omega⟩).size =>
        (x ∈ (Ps 0).alice (pref 0) ∧ y ∈ (Ps 0).bob (pref 0)) ∧
        ∀ t : Fin m,
          let prevAns : Fin t.val → BitString k := fun u =>
            (Ps ⟨u.val + 1, by omega⟩).output (pref ⟨u.val + 1, by omega⟩)
          let iv := runIntervals n k prevAns
          maskLeftVec iv x ∈ (Ps ⟨t.val + 1, by omega⟩).alice (pref ⟨t.val + 1, by omega⟩) ∧
          maskLeftVec iv y ∈ (Ps ⟨t.val + 1, by omega⟩).bob (pref ⟨t.val + 1, by omega⟩)
      let PNext := univ.filter fun pref : ∀ j : Fin (m + 2), Fin (Ps ⟨j.val, by omega⟩).size =>
        (x ∈ (Ps 0).alice (pref 0) ∧ y ∈ (Ps 0).bob (pref 0)) ∧
        ∀ t : Fin (m + 1),
          let prevAns : Fin t.val → BitString k := fun u =>
            (Ps ⟨u.val + 1, by omega⟩).output (pref ⟨u.val + 1, by omega⟩)
          let iv := runIntervals n k prevAns
          maskLeftVec iv x ∈ (Ps ⟨t.val + 1, by omega⟩).alice (pref ⟨t.val + 1, by omega⟩) ∧
          maskLeftVec iv y ∈ (Ps ⟨t.val + 1, by omega⟩).bob (pref ⟨t.val + 1, by omega⟩)
      let lastChoices (pref : ∀ j : Fin (m + 1), Fin (Ps ⟨j.val, by omega⟩).size) :
          Finset (Fin (Ps ⟨m + 1, by omega⟩).size) :=
        let prevAns : Fin m → BitString k := fun u =>
          (Ps ⟨u.val + 1, by omega⟩).output (pref ⟨u.val + 1, by omega⟩)
        let iv := runIntervals n k prevAns
        univ.filter fun r =>
          maskLeftVec iv x ∈ (Ps ⟨m + 1, by omega⟩).alice r ∧
          maskLeftVec iv y ∈ (Ps ⟨m + 1, by omega⟩).bob r
      have hcard_next : PNext.card ≤ ∑ pref ∈ PPrev, (lastChoices pref).card := by
        rw [← card_sigma]
        refine Finset.card_le_card_of_injOn
          (fun pref => ⟨fun j => pref j.castSucc, pref (Fin.last (m + 1))⟩) ?_ ?_
        · intro pref hp
          obtain ⟨h0, ht⟩ := (mem_filter.mp hp).2
          refine mem_sigma.mpr ⟨mem_filter.mpr ⟨mem_univ _, h0, fun t => ht t.castSucc⟩, ?_⟩
          exact mem_filter.mpr ⟨mem_univ _, ht (Fin.last m)⟩
        · intro p₁ _ p₂ _ heq
          have hinit : (fun j : Fin (m + 1) => p₁ j.castSucc) =
              fun j : Fin (m + 1) => p₂ j.castSucc :=
            congrArg Sigma.fst heq
          have hlast : p₁ (Fin.last (m + 1)) = p₂ (Fin.last (m + 1)) :=
            congrArg Sigma.snd heq
          funext j
          refine Fin.lastCases ?_ (fun j' => ?_) j
          · exact hlast
          · exact congrFun hinit j'
      have hchoice_le : ∀ pref ∈ PPrev, (lastChoices pref).card ≤ t := fun pref _ =>
        hamb ⟨m + 1, by omega⟩ _ _
      calc
        PNext.card ≤ ∑ pref ∈ PPrev, (lastChoices pref).card := hcard_next
        _ ≤ ∑ _pref ∈ PPrev, t := sum_le_sum hchoice_le
        _ = PPrev.card * t := by rw [sum_const, smul_eq_mul]
        _ ≤ t ^ (m + 1) * t := Nat.mul_le_mul_right t (ih (by omega))
        _ = t ^ (m + 2) := (pow_succ t (m + 1)).symm
  have hfull := hprefix s le_rfl
  exact hle_idx.trans hfull

/-- Correctness of `composeBinSearch`: if `Ps 0` accepts the true `ndisjK` answer on `(x, y)` and
each `Ps (t + 1)` accepts the true `ndisjK` answer on the true round-`t` left-half masked input,
then `composeBinSearch Ps` accepts a valid `SearchKRel n k` answer on `(x, y)`. -/
private theorem composeBinSearch_accepts {n k s : ℕ}
    (Ps : Fin (s + 1) → NondetProtocol (Fin k → BitString n) (Fin k → BitString n) (BitString k))
    (x y : Fin k → BitString n)
    (h0 : (Ps 0).Accepts (fun u v o => ndisjK n k u v = o) x y)
    (hsteps : ∀ t : Fin s,
      (Ps t.succ).Accepts (fun u v o => ndisjK n k u v = o)
        (maskLeftVec (runIntervals n k (trueSearchAnswers x y t.val)) x)
        (maskLeftVec (runIntervals n k (trueSearchAnswers x y t.val)) y)) :
    (composeBinSearch Ps).Accepts (SearchKRel n k) x y := by
  classical
  set L := (n + 2 ^ s - 1) / 2 ^ s
  obtain ⟨r0, hx0, hy0, ho0⟩ := h0
  have hstep_ex : ∀ t : Fin s, ∃ r : Fin (Ps t.succ).size,
      maskLeftVec (runIntervals n k (trueSearchAnswers x y t.val)) x ∈ (Ps t.succ).alice r ∧
      maskLeftVec (runIntervals n k (trueSearchAnswers x y t.val)) y ∈ (Ps t.succ).bob r ∧
      ndisjK n k (maskLeftVec (runIntervals n k (trueSearchAnswers x y t.val)) x)
        (maskLeftVec (runIntervals n k (trueSearchAnswers x y t.val)) y) = (Ps t.succ).output r :=
    fun t => hsteps t
  let idx : ∀ j : Fin (s + 1), Fin (Ps j).size :=
    Fin.cases r0 (fun t => (hstep_ex t).choose)
  have hidx0 : idx 0 = r0 := rfl
  have hidx_succ : ∀ t : Fin s, idx t.succ = (hstep_ex t).choose := fun _ => rfl
  have hans_eq : ∀ (r : ℕ) (hr : r ≤ s),
      binSearchRoundAns Ps idx r hr = trueSearchAnswers x y r := by
    intro r
    induction r with
    | zero => intro _; funext u; exact u.elim0
    | succ r ih =>
      intro hr
      funext u
      refine Fin.lastCases ?_ (fun u' => ?_) u
      · have hspec := (hstep_ex ⟨r, by omega⟩).choose_spec.2.2
        have hl : trueSearchAnswers x y (r + 1) (Fin.last r) =
            ndisjK n k (maskLeftVec (runIntervals n k (trueSearchAnswers x y r)) x)
              (maskLeftVec (runIntervals n k (trueSearchAnswers x y r)) y) := by
          simp [trueSearchAnswers, Fin.snoc_last]
        have hfin : (⟨(Fin.last r).val + 1, by omega⟩ : Fin (s + 1)) =
            (⟨r, by omega⟩ : Fin s).succ := Fin.ext rfl
        dsimp only [binSearchRoundAns]
        rw [hl, hfin, hidx_succ, ← hspec]
      · rw [trueSearchAnswers_castSucc]
        exact congrFun (ih (by omega)) u'
  set finalIv := runIntervals n k (trueSearchAnswers x y s)
  let ux : Fin k → BitString L := fun i d =>
    if h : (finalIv i).1 + d.val < n then x i ⟨(finalIv i).1 + d.val, h⟩ else false
  let uy : Fin k → BitString L := fun i d =>
    if h : (finalIv i).1 + d.val < n then y i ⟨(finalIv i).1 + d.val, h⟩ else false
  let tup : BinSearchIdx Ps := (idx, ux, uy)
  refine ⟨(binSearchEquiv Ps).symm tup, ?_, ?_, ?_⟩
  · -- Alice side membership.
    dsimp only [composeBinSearch]
    rw [Equiv.apply_symm_apply]
    dsimp only [binSearchAlice, tup]
    refine ⟨hx0, fun t => ?_, fun i d => ?_⟩
    · have hspec := (hstep_ex t).choose_spec.1
      have heq : binSearchRoundIv Ps idx t.val t.isLt.le =
          runIntervals n k (trueSearchAnswers x y t.val) := by
        unfold binSearchRoundIv; rw [hans_eq t.val t.isLt.le]
      rw [heq, hidx_succ]
      exact hspec
    · have heq : binSearchRoundIv Ps idx s le_rfl = finalIv := by
        unfold binSearchRoundIv; rw [hans_eq s le_rfl]
      dsimp only [ux]
      rw [heq]
  · -- Bob side membership.
    dsimp only [composeBinSearch]
    rw [Equiv.apply_symm_apply]
    dsimp only [binSearchBob, tup]
    refine ⟨hy0, fun t => ?_, fun i d => ?_⟩
    · have hspec := (hstep_ex t).choose_spec.2.1
      have heq : binSearchRoundIv Ps idx t.val t.isLt.le =
          runIntervals n k (trueSearchAnswers x y t.val) := by
        unfold binSearchRoundIv; rw [hans_eq t.val t.isLt.le]
      rw [heq, hidx_succ]
      exact hspec
    · have heq : binSearchRoundIv Ps idx s le_rfl = finalIv := by
        unfold binSearchRoundIv; rw [hans_eq s le_rfl]
      dsimp only [uy]
      rw [heq]
  · -- Output satisfies `SearchKRel n k x y`.
    dsimp only [composeBinSearch]
    rw [Equiv.apply_symm_apply]
    intro i
    have heq : binSearchRoundIv Ps idx s le_rfl = finalIv := by
      unfold binSearchRoundIv; rw [hans_eq s le_rfl]
    have h0i : (Ps 0).output (idx 0) i = ndisj (x i) (y i) := by
      rw [hidx0, ← ho0]; rfl
    dsimp only [binSearchOut, tup]
    rw [h0i]
    cases hnd : ndisj (x i) (y i)
    · simp only [↓reduceIte]
      exact ndisj_eq_false_iff_disjoint.mp hnd
    · simp only [Bool.true_eq_false, ↓reduceIte]
      obtain ⟨j, hjL, hjR, hxj, hyj⟩ := trueSearchAnswers_inv x y i hnd s
      have hbd := runIntervals_bounds n k (trueSearchAnswers x y s) i
      have hd_lt : j.val - (finalIv i).1 < L := by
        dsimp only [finalIv, L] at hjL hjR hbd ⊢
        omega
      let d₀ : Fin L := ⟨j.val - (finalIv i).1, hd_lt⟩
      have hd₀_true : (ux i d₀ && uy i d₀) = true := by
        have hsum : (finalIv i).1 + d₀.val = j.val := by dsimp only [d₀, finalIv] at hjL ⊢; omega
        have hlt : (finalIv i).1 + d₀.val < n := hsum ▸ j.isLt
        have hfin : (⟨(finalIv i).1 + d₀.val, hlt⟩ : Fin n) = j := Fin.ext hsum
        simp [ux, uy, hlt, hfin, hxj, hyj]
      have hfind_some : ((List.finRange L).find? (fun d => ux i d && uy i d)).isSome = true := by
        rw [List.find?_isSome]
        exact ⟨d₀, List.mem_finRange d₀, hd₀_true⟩
      obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hfind_some
      have hpred : (ux i d && uy i d) = true :=
        List.find?_some (p := fun d => ux i d && uy i d) hd
      have hux : ux i d = true := (Bool.and_eq_true _ _).mp hpred |>.1
      have huy : uy i d = true := (Bool.and_eq_true _ _).mp hpred |>.2
      have hlt : (finalIv i).1 + d.val < n := by
        by_contra hge
        simp [ux, hge] at hux
      rw [heq, hd]
      simp only [hlt, ↓reduceDIte]
      simp only [ux, uy, hlt, ↓reduceDIte] at hux huy
      exact ⟨hux, huy⟩

/-- Outer measure of a product of coordinate events under `Cslib.Probability.PMF.iid μ m`. -/
private theorem toOuterMeasure_iid_pi {α : Type*} (μ : PMF α) :
    ∀ {m : ℕ} (E : Fin m → Set α),
      ((Cslib.Probability.PMF.iid μ m).toOuterMeasure {v | ∀ j, v j ∈ E j}).toReal =
        ∏ j : Fin m, (μ.toOuterMeasure (E j)).toReal
  | 0, E => by
    have hset : ({v : Fin 0 → α | ∀ j, v j ∈ E j} : Set (Fin 0 → α)) = Set.univ := by
      ext v; simp
    rw [hset, Cslib.Probability.PMF.iid, PMF.toOuterMeasure_apply, Fin.prod_univ_zero]
    simp [Subsingleton.elim (default : Fin 0 → α) Fin.elim0]
  | m + 1, E => by
    classical
    rw [Cslib.Probability.PMF.iid]
    change ((μ.bind fun a => (Cslib.Probability.PMF.iid μ m).map (Fin.cons a)).toOuterMeasure
      {v | ∀ j, v j ∈ E j}).toReal = _
    rw [PMF.toOuterMeasure_bind_apply, Fin.prod_univ_succ]
    have hinner : ∀ a : α,
        ((Cslib.Probability.PMF.iid μ m).map (Fin.cons a)).toOuterMeasure {v | ∀ j, v j ∈ E j} =
          if a ∈ E 0 then
            (Cslib.Probability.PMF.iid μ m).toOuterMeasure {w | ∀ j : Fin m, w j ∈ E j.succ}
          else 0 := by
      intro a
      rw [PMF.toOuterMeasure_map_apply]
      by_cases ha : a ∈ E 0
      · simp only [ha, ↓reduceIte]
        congr 1; ext w
        simp only [Set.mem_preimage, Set.mem_ofPred_eq]
        constructor
        · intro h j; simpa using h j.succ
        · intro h j; exact Fin.cases (by simpa using ha) (fun j' => by simpa using h j') j
      · simp only [ha, ↓reduceIte]
        have hempty : Fin.cons a ⁻¹' {v | ∀ j, v j ∈ E j} = ∅ := by
          ext w; simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          intro h; exact ha (by simpa using h 0)
        rw [hempty, MeasureTheory.measure_empty]
    simp_rw [hinner]
    have hsplit : ∑' a : α, μ a *
        (if a ∈ E 0 then
          (Cslib.Probability.PMF.iid μ m).toOuterMeasure {w | ∀ j : Fin m, w j ∈ E j.succ}
        else 0) =
        μ.toOuterMeasure (E 0) *
          (Cslib.Probability.PMF.iid μ m).toOuterMeasure {w | ∀ j : Fin m, w j ∈ E j.succ} := by
      conv_rhs => rw [PMF.toOuterMeasure_apply]
      rw [← ENNReal.tsum_mul_right]
      refine tsum_congr fun a => ?_
      by_cases ha : a ∈ E 0 <;> simp [ha]
    rw [hsplit, ENNReal.toReal_mul, toOuterMeasure_iid_pi μ (fun j => E j.succ)]

/-- Number of binary-search halving rounds `sBinSearch` chosen so `2 / 2 ^ s ≤ betaSearch / 4`. -/
@[expose] def sBinSearch : ℕ := 54

/-- Threshold `n1NDisj` for `n` so `2 / n1NDisj ≤ betaSearch / 4`. -/
@[expose] def n1NDisj : ℕ := 2 ^ 54

/-- Explicit constants. -/
@[expose] noncomputable def alphaNDisj : ℝ := alphaSearch / ((sBinSearch + 1 : ℕ) : ℝ)

/-- Explicit communication-rate constant. -/
@[expose] noncomputable def betaNDisj : ℝ :=
  min (betaSearch / (2 * ((sBinSearch + 1 : ℕ) : ℝ))) (1 / (2 * (n1NDisj : ℝ)))

/-- Explicit ambiguity exponent constant for limited-ambiguity AM protocols. -/
@[expose] noncomputable def epsAM : ℝ := epsSearch / ((sBinSearch + 1 : ℕ) : ℝ)

/-- `alphaNDisj ∈ (0, 1]`. -/
theorem alphaNDisj_mem : 0 < alphaNDisj ∧ alphaNDisj ≤ 1 := by
  unfold alphaNDisj sBinSearch
  rw [alphaSearch_val]
  norm_num

/-- `betaNDisj ∈ (0, 1]`. -/
theorem betaNDisj_mem : 0 < betaNDisj ∧ betaNDisj ≤ 1 := by
  unfold betaNDisj sBinSearch n1NDisj
  refine ⟨lt_min (div_pos betaSearch_mem.1 (by norm_num)) (by positivity),
    (min_le_right _ _).trans (by norm_num)⟩

/-- `epsAM > 0`. -/
theorem epsAM_pos : 0 < epsAM := by
  unfold epsAM sBinSearch
  rw [epsSearch_val]
  norm_num

/-- **Master SDPT for Limited-Ambiguity AM Protocols Computing `NDISJ_n^(k)`**:
explicit-constant strong direct product bound for AM protocols. -/
theorem am_ndisjK_bound {n k c t : ℕ} (hn : 1 ≤ n)
    (hc : (c : ℝ) ≤ betaNDisj * (k : ℝ) * (n : ℝ))
    (ht : (t : ℝ) ≤ (2 : ℝ) ^ (epsAM * (k : ℝ)))
    {μ : AMProtocol (Fin k → BitString n) (Fin k → BitString n) (BitString k)}
    (hcomm : μ.HasComm c) (hamb : μ.HasAmbiguity t) {σ : ℝ}
    (hsolves : μ.SolvesWithSuccess σ (fun x y o => ndisjK n k x y = o)) :
    σ ≤ (2 : ℝ) ^ (-alphaNDisj * (k : ℝ)) := by
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · simp only [Nat.cast_zero, mul_zero, Real.rpow_zero]
    exact AMProtocol.solvesWithSuccess_le_one hsolves
  by_cases hsmall : n ≤ n1NDisj
  · have hβ : betaNDisj ≤ 1 / (2 * (n1NDisj : ℝ)) := min_le_right _ _
    have hc_half : (c : ℝ) ≤ (k : ℝ) / 2 := by
      have hnR : (n : ℝ) ≤ (n1NDisj : ℝ) := by exact_mod_cast hsmall
      have hn1pos : (0 : ℝ) < n1NDisj := by unfold n1NDisj; positivity
      calc (c : ℝ) ≤ betaNDisj * (k : ℝ) * (n : ℝ) := hc
        _ ≤ (1 / (2 * (n1NDisj : ℝ))) * (k : ℝ) * (n1NDisj : ℝ) := by gcongr
        _ = (k : ℝ) / 2 := by field_simp
    have hcnt := am_ndisjK_small_n_bound hn hcomm hsolves
    refine hcnt.trans (Real.rpow_le_rpow_of_exponent_le one_le_two ?_)
    unfold alphaNDisj sBinSearch
    rw [alphaSearch_val]
    linarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k]
  · push Not at hsmall
    by_cases hσ0 : σ ≤ 0
    · exact hσ0.trans (by positivity)
    push Not at hσ0
    -- Build the composed AM protocol `μ'` for `SearchKRel n k` via `sBinSearch + 1` i.i.d. draws.
    let μ' : AMProtocol (Fin k → BitString n) (Fin k → BitString n) (Fin k → Option (Fin n)) :=
      (Cslib.Probability.PMF.iid μ (sBinSearch + 1)).map composeBinSearch
    set c' := (sBinSearch + 1) * c + 2 * k * ((n + 2 ^ sBinSearch - 1) / 2 ^ sBinSearch)
    set t' := t ^ (sBinSearch + 1)
    have hcomm' : μ'.HasComm c' := by
      intro Q hQ
      rw [PMF.support_map] at hQ
      obtain ⟨Ps, hPs, rfl⟩ := hQ
      rw [← Cslib.Probability.PMF.piFin_const, Cslib.Probability.PMF.mem_support_piFin_iff] at hPs
      exact composeBinSearch_hasComm fun j => hcomm (Ps j) (hPs j)
    have hamb' : μ'.HasAmbiguity t' := by
      intro Q hQ
      rw [PMF.support_map] at hQ
      obtain ⟨Ps, hPs, rfl⟩ := hQ
      rw [← Cslib.Probability.PMF.piFin_const, Cslib.Probability.PMF.mem_support_piFin_iff] at hPs
      exact composeBinSearch_hasAmbiguity fun j => hamb (Ps j) (hPs j)
    have hsolves' : μ'.SolvesWithSuccess (σ ^ (sBinSearch + 1)) (SearchKRel n k) := by
      intro x y
      rw [AMProtocol.successProb_eq_toOuterMeasure, PMF.toOuterMeasure_map_apply]
      let E : Fin (sBinSearch + 1) →
          Set (NondetProtocol (Fin k → BitString n) (Fin k → BitString n) (BitString k)) :=
        Fin.cases {P | P.Accepts (fun u v o => ndisjK n k u v = o) x y}
          (fun t => {P | P.Accepts (fun u v o => ndisjK n k u v = o)
            (maskLeftVec (runIntervals n k (trueSearchAnswers x y t.val)) x)
            (maskLeftVec (runIntervals n k (trueSearchAnswers x y t.val)) y)})
      have hsub : {Ps : Fin (sBinSearch + 1) → _ | ∀ j, Ps j ∈ E j} ⊆
          composeBinSearch ⁻¹' {Q | Q.Accepts (SearchKRel n k) x y} := by
        intro Ps hPs
        exact composeBinSearch_accepts Ps x y (hPs 0) (fun t => hPs t.succ)
      have hmono := Cslib.Probability.PMF.toOuterMeasure_toReal_mono
        (Cslib.Probability.PMF.iid μ (sBinSearch + 1)) hsub
      rw [toOuterMeasure_iid_pi μ E] at hmono
      refine le_trans ?_ hmono
      calc
        σ ^ (sBinSearch + 1) = ∏ _j : Fin (sBinSearch + 1), σ := by
          rw [prod_const, card_univ, Fintype.card_fin]
        _ ≤ ∏ j : Fin (sBinSearch + 1), (μ.toOuterMeasure (E j)).toReal := by
          gcongr with j _
          refine Fin.cases ?_ (fun t => ?_) j
          · exact hsolves x y
          · exact hsolves _ _
    -- Verify `c' ≤ betaSearch * k * n` and `t' ≤ 2 ^ (epsSearch * k)`.
    have hbetaSearch_ge : (1 : ℝ) / (2 ^ 51 : ℝ) ≤ betaSearch := betaSearch_ge
    have hc' : (c' : ℝ) ≤ betaSearch * (k : ℝ) * (n : ℝ) := by
      have hdiv_le : (((n + 2 ^ sBinSearch - 1) / 2 ^ sBinSearch : ℕ) : ℝ) ≤
          (n : ℝ) / (2 : ℝ) ^ sBinSearch + 1 := by
        have hnat : (n + 2 ^ sBinSearch - 1) / 2 ^ sBinSearch * 2 ^ sBinSearch ≤
            n + 2 ^ sBinSearch :=
          (Nat.div_mul_le_self (n + 2 ^ sBinSearch - 1) (2 ^ sBinSearch)).trans (Nat.sub_le _ _)
        have hR : (((n + 2 ^ sBinSearch - 1) / 2 ^ sBinSearch : ℕ) : ℝ) * (2 : ℝ) ^ sBinSearch ≤
            (n : ℝ) + (2 : ℝ) ^ sBinSearch := by exact_mod_cast hnat
        have hpos : (0 : ℝ) < (2 : ℝ) ^ sBinSearch := by positivity
        have := (le_div_iff₀ hpos).mpr hR
        rw [add_div, div_self hpos.ne'] at this
        exact this
      have hβ1 : betaNDisj ≤ betaSearch / (2 * ((sBinSearch + 1 : ℕ) : ℝ)) := min_le_left _ _
      have hterm1 : ((sBinSearch + 1 : ℕ) : ℝ) * (c : ℝ) ≤
        (betaSearch / 2) * (k : ℝ) * (n : ℝ) := by
        have hs_pos : (0 : ℝ) < ((sBinSearch + 1 : ℕ) : ℝ) := by positivity
        calc
          ((sBinSearch + 1 : ℕ) : ℝ) * (c : ℝ)
            ≤ ((sBinSearch + 1 : ℕ) : ℝ) * (betaNDisj * (k : ℝ) * (n : ℝ)) := by gcongr
          _ ≤ ((sBinSearch + 1 : ℕ) : ℝ) *
                (betaSearch / (2 * ((sBinSearch + 1 : ℕ) : ℝ)) * (k : ℝ) * (n : ℝ)) := by gcongr
          _ = (betaSearch / 2) * (k : ℝ) * (n : ℝ) := by field_simp
      have hterm2 : 2 / (2 : ℝ) ^ sBinSearch ≤ betaSearch / 4 := by
        unfold sBinSearch
        linarith [show (2 : ℝ) / (2 : ℝ) ^ (54 : ℕ) ≤ 1 / (2 ^ 51 : ℝ) / 4 by norm_num]
      have hterm3 : (2 : ℝ) ≤ (betaSearch / 4) * (n : ℝ) := by
        have hnR : (2 ^ 54 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hsmall.le
        have h1 : (2 : ℝ) ≤ (1 / (2 ^ 51 : ℝ) / 4) * (2 ^ 54 : ℝ) := by norm_num
        nlinarith [show (0 : ℝ) ≤ (n : ℝ) by positivity]
      dsimp only [c']
      push_cast
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have hkn0 : (0 : ℝ) ≤ (k : ℝ) * (n : ℝ) := by positivity
      calc
        ((sBinSearch : ℝ) + 1) * (c : ℝ) +
            2 * (k : ℝ) * (((n + 2 ^ sBinSearch - 1) / 2 ^ sBinSearch : ℕ) : ℝ)
          ≤ (betaSearch / 2) * (k : ℝ) * (n : ℝ) +
              2 * (k : ℝ) * ((n : ℝ) / (2 : ℝ) ^ sBinSearch + 1) := by
            have h1' : ((sBinSearch : ℝ) + 1) * (c : ℝ) ≤
                (betaSearch / 2) * (k : ℝ) * (n : ℝ) := by exact_mod_cast hterm1
            nlinarith
        _ = (betaSearch / 2) * (k : ℝ) * (n : ℝ) +
              (2 / (2 : ℝ) ^ sBinSearch) * ((k : ℝ) * (n : ℝ)) + (k : ℝ) * 2 := by ring
        _ ≤ (betaSearch / 2) * (k : ℝ) * (n : ℝ) +
              (betaSearch / 4) * ((k : ℝ) * (n : ℝ)) + (k : ℝ) * ((betaSearch / 4) * (n : ℝ)) := by
            nlinarith
        _ = betaSearch * (k : ℝ) * (n : ℝ) := by ring
    have ht' : (t' : ℝ) ≤ (2 : ℝ) ^ (epsSearch * (k : ℝ)) := by
      dsimp only [t']
      rw [Nat.cast_pow]
      calc
        (t : ℝ) ^ (sBinSearch + 1)
          ≤ ((2 : ℝ) ^ (epsAM * (k : ℝ))) ^ (sBinSearch + 1) :=
            pow_le_pow_left₀ (Nat.cast_nonneg t) ht _
        _ = (2 : ℝ) ^ (epsAM * (k : ℝ) * ((sBinSearch + 1 : ℕ) : ℝ)) := by
            rw [← Real.rpow_natCast ((2 : ℝ) ^ _), ← Real.rpow_mul zero_le_two]
        _ = (2 : ℝ) ^ (epsSearch * (k : ℝ)) := by
            congr 1; unfold epsAM; field_simp
    have hbound := am_searchK_bound hn hc' ht' hcomm' hamb' hsolves'
    -- Take `(sBinSearch + 1)`-th root.
    have hpow_eq : ((2 : ℝ) ^ (-alphaNDisj * (k : ℝ))) ^ (sBinSearch + 1) =
        (2 : ℝ) ^ (-alphaSearch * (k : ℝ)) := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ _), ← Real.rpow_mul zero_le_two]
      congr 1
      unfold alphaNDisj
      have hs0 : ((sBinSearch + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
      field_simp
    rw [← hpow_eq] at hbound
    by_contra hgt
    push Not at hgt
    have : ((2 : ℝ) ^ (-alphaNDisj * (k : ℝ))) ^ (sBinSearch + 1) < σ ^ (sBinSearch + 1) :=
      pow_lt_pow_left₀ hgt (by positivity) (Nat.succ_ne_zero sBinSearch)
    linarith

/-- Strong direct product theorem for AM protocols with ambiguity `2 ^ (ε k)` on `NDISJ_n^(k)`:
There are constants `0 < ε, α, β ≤ 1` such that every AM-protocol with ambiguity at most
`2 ^ (ε k)` and communication at most `β k n` computing `NDISJ_n^(k)` (`n ≥ 1`) has worst-case
success probability at most `2 ^ (-α k)`. -/
theorem sdpt_am_ndisjK :
    ∃ ε α β : ℝ, (0 < ε ∧ ε ≤ 1) ∧ (0 < α ∧ α ≤ 1) ∧ (0 < β ∧ β ≤ 1) ∧
      ∀ (n k c t : ℕ), 1 ≤ n → (c : ℝ) ≤ β * (k : ℝ) * (n : ℝ) →
        (t : ℝ) ≤ (2 : ℝ) ^ (ε * (k : ℝ)) →
        ∀ (μ : AMProtocol (Fin k → BitString n) (Fin k → BitString n) (BitString k)),
          μ.HasComm c → μ.HasAmbiguity t →
          ∀ σ : ℝ, μ.SolvesWithSuccess σ (fun x y o => ndisjK n k x y = o) →
            σ ≤ (2 : ℝ) ^ (-α * (k : ℝ)) :=
  ⟨epsAM, alphaNDisj, betaNDisj,
    ⟨epsAM_pos, by unfold epsAM sBinSearch; rw [epsSearch_val]; norm_num⟩,
    alphaNDisj_mem, betaNDisj_mem,
    fun _ _ _ _ hn hc ht _ hcomm hamb _ hsolves =>
      am_ndisjK_bound hn hc ht hcomm hamb hsolves⟩

/-- Explicit-constant strong direct product bound for public-coin protocols on `NDISJ_n^(k)`. -/
theorem sdpt_ndisj_bound {n k c : ℕ} (hn : 1 ≤ n) (hc : (c : ℝ) ≤ betaNDisj * (k : ℝ) * (n : ℝ))
    {μ : PublicCoin (Fin k → BitString n) (Fin k → BitString n) (BitString k)}
    (hdepth : μ.depth ≤ c) {σ : ℝ}
    (hsolves : SolvesWithSuccess μ σ (fun x y o => ndisjK n k x y = o)) :
    σ ≤ (2 : ℝ) ^ (-alphaNDisj * (k : ℝ)) := by
  have h1 : ((1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (epsAM * (k : ℝ)) := by
    simpa using Real.one_le_rpow one_le_two (mul_nonneg epsAM_pos.le (Nat.cast_nonneg k))
  exact am_ndisjK_bound hn hc h1 (publicCoinToAM_hasComm hdepth) (publicCoinToAM_hasAmbiguity μ)
    (fun x y => by rw [publicCoinToAM_successProb]; exact hsolves x y)

/-- Strong direct product theorem for public-coin protocols computing `NDISJ_n^(k)`:
There are constants `0 < α'', β'' ≤ 1` such that for all `n ≥ 1` and `k`, every randomized
public-coin protocol for `NDISJ_n^(k)` with communication `c ≤ β'' k n` has worst-case success
probability `σ ≤ 2 ^ (-α'' k)`. -/
theorem sdpt_ndisjK :
    ∃ α'' β'' : ℝ, (0 < α'' ∧ α'' ≤ 1) ∧ (0 < β'' ∧ β'' ≤ 1) ∧
      ∀ (n k c : ℕ), 1 ≤ n → (c : ℝ) ≤ β'' * (k : ℝ) * (n : ℝ) →
        ∀ (μ : PublicCoin (Fin k → BitString n) (Fin k → BitString n) (BitString k)),
          μ.depth ≤ c → ∀ σ : ℝ, SolvesWithSuccess μ σ (fun x y o => ndisjK n k x y = o) →
            σ ≤ (2 : ℝ) ^ (-α'' * (k : ℝ)) :=
  ⟨alphaNDisj, betaNDisj, alphaNDisj_mem, betaNDisj_mem,
    fun _ _ _ hn hc _ hdepth _ hsolves => sdpt_ndisj_bound hn hc hdepth hsolves⟩

/-- Strong direct product theorem for public-coin protocols computing `DISJ_n^(k)`:
By coordinatewise output negation, the identical SDPT holds for `k`-fold Disjointness `DISJ_n^(k)`.
-/
theorem sdpt_disjK :
    ∃ α'' β'' : ℝ, (0 < α'' ∧ α'' ≤ 1) ∧ (0 < β'' ∧ β'' ≤ 1) ∧
      ∀ (n k c : ℕ), 1 ≤ n → (c : ℝ) ≤ β'' * (k : ℝ) * (n : ℝ) →
        ∀ (μ : PublicCoin (Fin k → BitString n) (Fin k → BitString n) (BitString k)),
          μ.depth ≤ c → ∀ σ : ℝ, SolvesWithSuccess μ σ (fun x y o => disjK n k x y = o) →
            σ ≤ (2 : ℝ) ^ (-α'' * (k : ℝ)) := by
  refine ⟨alphaNDisj, betaNDisj, alphaNDisj_mem, betaNDisj_mem,
    fun n k c hn hc μ hdepth σ hsolves => ?_⟩
  let negOut (v : BitString k) : BitString k := fun i => !v i
  let μ' : PublicCoin (Fin k → BitString n) (Fin k → BitString n) (BitString k) :=
    μ.map (Protocol.map negOut)
  have hdepth' : μ'.depth ≤ c := by
    rw [PublicCoin.depth_le_iff]
    intro p hp
    rw [PMF.support_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    rw [Protocol.depth_map]
    exact (PublicCoin.depth_le_depth hq).trans hdepth
  have hsolves' : SolvesWithSuccess μ' σ (fun x y o => ndisjK n k x y = o) := by
    intro x y
    rw [successProb_eq_toOuterMeasure, PMF.toOuterMeasure_map_apply]
    have hset : Protocol.map negOut ⁻¹' {p | ndisjK n k x y = p.run x y} =
        {q | disjK n k x y = q.run x y} := by
      ext q
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Protocol.run_map, negOut]
      constructor
      · intro h; funext i; rw [disjK_eq_not_ndisjK, h]; simp
      · intro h; funext i; have hi := congrFun h i; rw [disjK_eq_not_ndisjK] at hi
        simpa using congrArg Bool.not hi
    rw [hset]
    exact (successProb_eq_toOuterMeasure μ (fun x y o => disjK n k x y = o) x y).symm ▸
      hsolves x y
  exact sdpt_ndisj_bound hn hc hdepth' hsolves'

/-- Linear `Ω(n)` communication lower bound for unambiguous AM protocols on `NDISJ_n`:
There are constants `0 < ε₀, β₀` such that every unambiguous (`t = 1`) AM protocol computing
single-instance `NDISJ_n` (`n ≥ 1`) with error at most `ε₀` (success probability `≥ 1 - ε₀`)
requires communication `c > β₀ * n`. -/
theorem unambiguous_am_ndisj_lower_bound :
    ∃ ε₀ β₀ : ℝ, 0 < ε₀ ∧ 0 < β₀ ∧
      ∀ (n c : ℕ), 1 ≤ n →
        ∀ (μ : AMProtocol (BitString n) (BitString n) Bool),
          μ.HasComm c → μ.HasAmbiguity 1 →
          μ.SolvesWithSuccess (1 - ε₀) (fun x y b => ndisj x y = b) →
          β₀ * (n : ℝ) < (c : ℝ) := by
  let ε₀ : ℝ := (1 - (2 : ℝ) ^ (-alphaNDisj)) / 2
  have hpow_lt1 : (2 : ℝ) ^ (-alphaNDisj) < 1 := by
    calc (2 : ℝ) ^ (-alphaNDisj) < (2 : ℝ) ^ (0 : ℝ) :=
          Real.rpow_lt_rpow_of_exponent_lt one_lt_two (by linarith [alphaNDisj_mem.1])
      _ = 1 := by norm_num
  have hε0 : 0 < ε₀ := by dsimp only [ε₀]; linarith
  refine ⟨ε₀, betaNDisj, hε0, betaNDisj_mem.1, fun n c hn μ hcomm hamb hsolves => ?_⟩
  by_contra hle
  push Not at hle
  -- Lift single-instance `μ` to `k = 1` instance of `ndisjK n 1`.
  let liftP (P : NondetProtocol (BitString n) (BitString n) Bool) :
      NondetProtocol (Fin 1 → BitString n) (Fin 1 → BitString n) (BitString 1) :=
    (P.comap (fun x => x 0) (fun y => y 0)).map (fun b _ => b)
  let μ1 : AMProtocol (Fin 1 → BitString n) (Fin 1 → BitString n) (BitString 1) := μ.map liftP
  have hcomm1 : μ1.HasComm c := by
    intro Q hQ; rw [PMF.support_map] at hQ; obtain ⟨P, hP, rfl⟩ := hQ; exact hcomm P hP
  have hamb1 : μ1.HasAmbiguity 1 := by
    intro Q hQ; rw [PMF.support_map] at hQ; obtain ⟨P, hP, rfl⟩ := hQ
    exact NondetProtocol.map_hasAmbiguity (NondetProtocol.comap_hasAmbiguity (hamb P hP))
  have hsolves1 : μ1.SolvesWithSuccess (1 - ε₀) (fun x y o => ndisjK n 1 x y = o) := by
    intro x y
    rw [AMProtocol.successProb_eq_toOuterMeasure, PMF.toOuterMeasure_map_apply]
    refine (hsolves (x 0) (y 0)).trans (Cslib.Probability.PMF.toOuterMeasure_toReal_mono μ ?_)
    intro P ⟨r, hx, hy, hR⟩
    refine ⟨r, hx, hy, ?_⟩
    funext i; rw [Subsingleton.elim i 0]; exact hR
  have hc1 : (c : ℝ) ≤ betaNDisj * ((1 : ℕ) : ℝ) * (n : ℝ) := by simpa using hle
  have ht1 : ((1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (epsAM * ((1 : ℕ) : ℝ)) := by
    simpa using Real.one_le_rpow one_le_two epsAM_pos.le
  have hbd := am_ndisjK_bound hn hc1 ht1 hcomm1 hamb1 hsolves1
  simp only [Nat.cast_one, mul_one] at hbd
  dsimp only [ε₀] at hbd
  linarith

end CslibFrontier.Computability.Communication
