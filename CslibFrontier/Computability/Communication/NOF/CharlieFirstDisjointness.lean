module

public import CslibFrontier.Computability.Communication.DirectProduct.Disjointness
public import CslibFrontier.Computability.Communication.NOF.Protocol
public import CslibFrontier.Computability.Communication.NOF.Randomized

import Cslib.Probability.PMF
import CslibFrontier.Probability.IID
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Three-Party Charlie-First NOF Disjointness Lower Bound

Lower bound for three-party Number-on-Forehead (NOF) Disjointness in the Charlie-first model
(where the third player sends a single message before an arbitrary two-party interaction between
the first two players):

* `nofNDisj3` and `nofDisj3`: three-party NOF Nondisjointness and Disjointness on `n`-bit strings.
* `IsAliceBobOnly`, `IsCharlieFirst`, and `IsCharlieFirstPublicCoin`: Charlie-first restriction on
  `Cslib.Communication.NOF.Protocol` and `Cslib.Communication.NOF.PublicCoin`.
* Majority error amplification preserving the Charlie-first structure, self-contained Hamming-ball
  volume bound, and reduction to the strong direct product theorem for two-party `NDISJ_k^(k)`.
* `nof_charlieFirst_disj_lower_bound` and `nof_charlieFirst_ndisj_lower_bound`: `Ω(√n)` randomized
  bounded-error communication lower bound.
-/

open Cslib Cslib.Communication Cslib.Probability Finset

namespace CslibFrontier.Computability.Communication

public section

/-! ### 3-Party NOF Disjointness and Charlie-First Protocols -/

/-- 3-party Number-on-Forehead Nondisjointness on `n`-bit inputs `(x 0, x 1, x 2)`: outputs `true`
iff there is a coordinate `j : Fin n` where all three players have bit `1`. -/
@[expose] def nofNDisj3 (n : ℕ) (x : ∀ _ : Fin 3, BitString n) : Bool :=
  decide (∃ j : Fin n, x 0 j = true ∧ x 1 j = true ∧ x 2 j = true)

/-- Characterization of `nofNDisj3 n x = true`. -/
theorem nofNDisj3_eq_true_iff (n : ℕ) (x : ∀ _ : Fin 3, BitString n) :
    nofNDisj3 n x = true ↔ ∃ j : Fin n, x 0 j = true ∧ x 1 j = true ∧ x 2 j = true :=
  decide_eq_true_iff

/-- 3-party Number-on-Forehead Disjointness: negation of `nofNDisj3`. -/
@[expose] def nofDisj3 (n : ℕ) (x : ∀ _ : Fin 3, BitString n) : Bool :=
  !nofNDisj3 n x

/-- A 3-party NOF protocol in which only Alice (`0 : Fin 3`) and Bob (`1 : Fin 3`) ever speak
(Charlie `2 : Fin 3` never speaks). -/
@[expose] def IsAliceBobOnly {X : Fin 3 → Type*} {Z : Type*} : NOF.Protocol X Z → Prop
  | .output _ => True
  | .speak i _ p₀ p₁ => i ≠ 2 ∧ IsAliceBobOnly p₀ ∧ IsAliceBobOnly p₁

/-- A 3-party NOF protocol in the Charlie-first model: Charlie (`2 : Fin 3`) sends a single
message (a prefix of bits spoken only by player `2`), followed by an arbitrary interaction between
Alice (`0`) and Bob (`1`) with no further messages from Charlie. -/
@[expose] def IsCharlieFirst {X : Fin 3 → Type*} {Z : Type*} : NOF.Protocol X Z → Prop
  | .output _ => True
  | .speak i _ p₀ p₁ =>
    if i = 2 then IsCharlieFirst p₀ ∧ IsCharlieFirst p₁
    else IsAliceBobOnly p₀ ∧ IsAliceBobOnly p₁

/-- A public-coin 3-party NOF protocol is Charlie-first if every deterministic protocol in its
support is Charlie-first. -/
@[expose] def IsCharlieFirstPublicCoin {X : Fin 3 →
  Type*} {Z : Type*} (μ : NOF.PublicCoin X Z) : Prop :=
  ∀ p ∈ μ.support, IsCharlieFirst p

private theorem isCharlieFirst_of_isAliceBobOnly {X : Fin 3 → Type*} {Z : Type*}
    {p : NOF.Protocol X Z} (hp : IsAliceBobOnly p) : IsCharlieFirst p := by
  cases p with
  | output _ => trivial
  | speak i send p₀ p₁ =>
    obtain ⟨hi, h0, h1⟩ := hp
    simp only [IsCharlieFirst, ite_eq_right hi]
    exact ⟨h0, h1⟩

/-! ### Splitting Charlie's Prefix from the Alice–Bob Continuation -/

/-- Build Charlie's NOF view (`view 2`) directly from `(x₀, x₁)`, visibly independent of `x₂`. -/
private def charlieView {X : Fin 3 → Type*} (x₀ : X 0) (x₁ : X 1) : NOF.View X 2 :=
  fun ⟨j, hj⟩ =>
    match j with
    | ⟨0, _⟩ => x₀
    | ⟨1, _⟩ => x₁
    | ⟨2, _⟩ => absurd rfl hj

private theorem charlieView_eq_view {X : Fin 3 → Type*} (x : ∀ i : Fin 3, X i) :
    charlieView (x 0) (x 1) = NOF.view 2 x := by
  funext ⟨j, hj⟩
  fin_cases j
  · rfl
  · rfl
  · exact absurd rfl hj

/-- Extract Charlie's message of length `d` (padded with `false` after Charlie finishes speaking)
as a function of `(x₀, x₁)` alone. -/
private def charlieMsg {X : Fin 3 → Type*} {Z : Type*} (x₀ : X 0) (x₁ : X 1) :
    (d : ℕ) → NOF.Protocol X Z → BitString d
  | 0, _ => Fin.elim0
  | _ + 1, .output _ => fun _ => false
  | d + 1, .speak i send p₀ p₁ =>
    if hi : i = 2 then
      let b := send (hi ▸ charlieView x₀ x₁)
      Fin.cons b (charlieMsg x₀ x₁ d (if b then p₁ else p₀))
    else fun _ => false

/-- Follow bitstring `m : BitString d` through Charlie's prefix of `p` to obtain the residual
Alice–Bob continuation subtree. -/
private def followCharlie {X : Fin 3 → Type*} {Z : Type*} :
    (d : ℕ) → BitString d → NOF.Protocol X Z → NOF.Protocol X Z
  | _, _, .output z => .output z
  | 0, _, p => p
  | d + 1, m, .speak i send p₀ p₁ =>
    if i = 2 then
      if m 0 then followCharlie d (Fin.tail m) p₁ else followCharlie d (Fin.tail m) p₀
    else .speak i send p₀ p₁

private theorem isAliceBobOnly_followCharlie {X : Fin 3 → Type*} {Z : Type*}
    {p : NOF.Protocol X Z} (hp : IsCharlieFirst p) {d : ℕ} (hd : p.depth ≤ d) (m : BitString d) :
    IsAliceBobOnly (followCharlie d m p) := by
  induction p generalizing d with
  | output _ => simp [followCharlie, IsAliceBobOnly]
  | speak i send p₀ p₁ ih₀ ih₁ =>
    simp only [NOF.Protocol.depth_speak] at hd
    cases d with
    | zero => omega
    | succ d =>
      simp only [followCharlie]
      by_cases hi : i = 2
      · rw [ite_eq_left hi]
        simp only [IsCharlieFirst, ite_eq_left hi] at hp
        cases m 0
        · exact ih₀ hp.1 (by omega) (Fin.tail m)
        · exact ih₁ hp.2 (by omega) (Fin.tail m)
      · rw [ite_eq_right hi]
        simp only [IsCharlieFirst, ite_eq_right hi] at hp
        exact ⟨hi, hp.1, hp.2⟩

private theorem depth_followCharlie_le {X : Fin 3 → Type*} {Z : Type*}
    (p : NOF.Protocol X Z) (d : ℕ) (m : BitString d) :
    (followCharlie d m p).depth ≤ p.depth := by
  induction p generalizing d with
  | output _ => simp [followCharlie]
  | speak i send p₀ p₁ ih₀ ih₁ =>
    cases d with
    | zero => exact le_rfl
    | succ d =>
      simp only [followCharlie]
      by_cases hi : i = 2
      · rw [ite_eq_left hi]
        cases m 0
        · exact (ih₀ d (Fin.tail m)).trans (by simp only [NOF.Protocol.depth_speak]; omega)
        · exact (ih₁ d (Fin.tail m)).trans (by simp only [NOF.Protocol.depth_speak]; omega)
      · rw [ite_eq_right hi]

private theorem run_followCharlie_charlieMsg {X : Fin 3 → Type*} {Z : Type*}
    (p : NOF.Protocol X Z) (x : ∀ i : Fin 3, X i) {d : ℕ} (hd : p.depth ≤ d) :
    (followCharlie d (charlieMsg (x 0) (x 1) d p) p).run x = p.run x := by
  induction p generalizing d with
  | output _ => simp [followCharlie]
  | speak i send p₀ p₁ ih₀ ih₁ =>
    simp only [NOF.Protocol.depth_speak] at hd
    cases d with
    | zero => omega
    | succ d =>
      simp only [charlieMsg, followCharlie]
      by_cases hi : i = 2
      · subst hi
        simp only [↓reduceDIte, ↓reduceIte, Fin.cons_zero, Fin.tail_cons, NOF.Protocol.run_speak]
        rw [charlieView_eq_view x]
        cases hb : send (NOF.view 2 x)
        · simpa [hb] using ih₀ (by omega)
        · simpa [hb] using ih₁ (by omega)
      · rw [dite_eq_right hi, ite_eq_right hi]

/-- Player 0's (Alice's) NOF view constructed from `(x₁, z)`. -/
private def aliceView {X : Fin 3 → Type*} (x₁ : X 1) (z : X 2) : NOF.View X 0 :=
  fun ⟨j, hj⟩ => match j with
    | ⟨0, _⟩ => absurd rfl hj
    | ⟨1, _⟩ => x₁
    | ⟨2, _⟩ => z

/-- Player 1's (Bob's) NOF view constructed from `(x₀, z)`. -/
private def bobView {X : Fin 3 → Type*} (x₀ : X 0) (z : X 2) : NOF.View X 1 :=
  fun ⟨j, hj⟩ => match j with
    | ⟨0, _⟩ => x₀
    | ⟨1, _⟩ => absurd rfl hj
    | ⟨2, _⟩ => z

/-- Convert an `IsAliceBobOnly` 3-party NOF protocol with fixed Charlie input `z : X 2` into a
2-party protocol between Alice (holding `x₀ : X 0`) and Bob (holding `x₁ : X 1`). In the NOF
model, NOF-player `0` sees `(x₁, z)` (so 2-party Bob simulates NOF-player `0`) and NOF-player `1`
sees `(x₀, z)` (so 2-party Alice simulates NOF-player `1`). -/
private def toTwoParty {X : Fin 3 → Type*} {Z : Type*} (z : X 2) :
    NOF.Protocol X Z → Protocol (X 0) (X 1) Z
  | .output out => .output out
  | .speak i send p₀ p₁ =>
    match i with
    | ⟨0, _⟩ => .bob (fun x₁ => send (aliceView x₁ z)) (toTwoParty z p₀) (toTwoParty z p₁)
    | ⟨1, _⟩ => .alice (fun x₀ => send (bobView x₀ z)) (toTwoParty z p₀) (toTwoParty z p₁)
    | ⟨2, _⟩ => toTwoParty z p₀

private theorem depth_toTwoParty_le {X : Fin 3 → Type*} {Z : Type*} (z : X 2)
    (q : NOF.Protocol X Z) : (toTwoParty z q).depth ≤ q.depth := by
  induction q with
  | output _ => simp [toTwoParty]
  | speak i send p₀ p₁ ih₀ ih₁ =>
    fin_cases i
    · simp only [toTwoParty, Protocol.depth_bob, NOF.Protocol.depth_speak]; omega
    · simp only [toTwoParty, Protocol.depth_alice, NOF.Protocol.depth_speak]; omega
    · simp only [toTwoParty, NOF.Protocol.depth_speak]; omega

/-- Construct a 3-party input profile from `(x₀, x₁, z)`. -/
private def mkInput3 {n : ℕ} (x₀ x₁ z : BitString n) : ∀ _ : Fin 3, BitString n
  | ⟨0, _⟩ => x₀
  | ⟨1, _⟩ => x₁
  | ⟨2, _⟩ => z

private theorem run_toTwoParty {n : ℕ} {Z : Type*} (x₀ x₁ z : BitString n)
    {q : NOF.Protocol (fun _ : Fin 3 => BitString n) Z} (hq : IsAliceBobOnly q) :
    (toTwoParty z q).run x₀ x₁ = q.run (mkInput3 x₀ x₁ z) := by
  induction q with
  | output _ => rfl
  | speak i send p₀ p₁ ih₀ ih₁ =>
    obtain ⟨hi, h0, h1⟩ := hq
    fin_cases i
    · simp only [toTwoParty, Protocol.run_bob, NOF.Protocol.run_speak]
      have hv : aliceView (X := fun _ : Fin 3 => BitString n) x₁ z =
          NOF.view ⟨0, by decide⟩ (mkInput3 x₀ x₁ z) := by
        funext ⟨j, hj⟩
        fin_cases j
        · exact absurd rfl hj
        · rfl
        · rfl
      rw [hv]
      cases send (NOF.view ⟨0, by decide⟩ (mkInput3 x₀ x₁ z))
      · exact ih₀ h0
      · exact ih₁ h1
    · simp only [toTwoParty, Protocol.run_alice, NOF.Protocol.run_speak]
      have hv : bobView (X := fun _ : Fin 3 => BitString n) x₀ z =
          NOF.view ⟨1, by decide⟩ (mkInput3 x₀ x₁ z) := by
        funext ⟨j, hj⟩
        fin_cases j
        · rfl
        · exact absurd rfl hj
        · rfl
      rw [hv]
      cases send (NOF.view ⟨1, by decide⟩ (mkInput3 x₀ x₁ z))
      · exact ih₀ h0
      · exact ih₁ h1
    · exact absurd rfl hi

/-! ### Charlie-First Majority Error Amplification -/

private theorem isAliceBobOnly_bind {X : Fin 3 → Type*} {Z Z' : Type*}
    {p : NOF.Protocol X Z} {q : Z → NOF.Protocol X Z'}
    (hp : IsAliceBobOnly p) (hq : ∀ z, IsAliceBobOnly (q z)) :
    IsAliceBobOnly (p.bind q) := by
  induction p with
  | output z => exact hq z
  | speak i send p₀ p₁ ih₀ ih₁ =>
    obtain ⟨hi, h0, h1⟩ := hp
    exact ⟨hi, ih₀ h0, ih₁ h1⟩

private theorem isAliceBobOnly_runAll {X : Fin 3 → Type*} {Z Z' : Type*} {k : ℕ}
    {ps : Fin k → NOF.Protocol X Z} (hps : ∀ t, IsAliceBobOnly (ps t)) (g : (Fin k → Z) → Z') :
    IsAliceBobOnly (NOF.Protocol.runAll ps g) := by
  induction k generalizing Z' with
  | zero => trivial
  | succ k ih =>
    exact isAliceBobOnly_bind (hps 0) fun _ => ih (fun t => hps t.succ) _

private theorem isCharlieFirst_sendBits_two {X : Fin 3 → Type*} {Z : Type*}
    {m : ℕ} {msg : NOF.View X 2 → BitString m} {cont : BitString m → NOF.Protocol X Z}
    (hcont : ∀ v, IsCharlieFirst (cont v)) :
    IsCharlieFirst (NOF.Protocol.sendBits 2 m msg cont) := by
  induction m with
  | zero => exact hcont Fin.elim0
  | succ m ih =>
    simp only [NOF.Protocol.sendBits, IsCharlieFirst, ↓reduceIte]
    exact ⟨ih (fun v => hcont (Fin.cons false v)), ih (fun v => hcont (Fin.cons true v))⟩

/-- Strict majority of `2 * r` booleans: `true` iff strictly more than `r` entries are `true`. -/
private def strictMaj {r : ℕ} (v : BitString (2 * r)) : Bool :=
  decide (r < (Finset.univ.filter fun t : Fin (2 * r) => v t = true).card)

/-- Given `2 * r` Charlie-first protocols of depth `≤ d`, produce a single Charlie-first protocol
of depth `≤ 4 * r * d` that outputs the strict majority of their `2 * r` outputs: Charlie first
sends all `2 * r` of her `d`-bit prefixes concatenated, and Alice and Bob then run the `2 * r`
Alice–Bob continuations sequentially. -/
private def amplifyCFDet {X : Fin 3 → Type*} (d r : ℕ)
    (ps : Fin (2 * r) → NOF.Protocol X Bool) : NOF.Protocol X Bool :=
  let pack (v : NOF.View X 2) : BitString (2 * r * d) := fun idx =>
    if hd : d = 0 then false
    else
      let t : Fin (2 * r) :=
        ⟨idx.val / d, (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero hd)).mpr idx.isLt⟩
      let j : Fin d := ⟨idx.val % d, Nat.mod_lt _ (Nat.pos_of_ne_zero hd)⟩
      charlieMsg (v ⟨0, by decide⟩) (v ⟨1, by decide⟩) d (ps t) j
  let unpack (M : BitString (2 * r * d)) (t : Fin (2 * r)) : BitString d := fun j =>
    M ⟨t.val * d + j.val, by
      have h1 : (t.val + 1) * d ≤ 2 * r * d := Nat.mul_le_mul_right d t.isLt
      have : t.val * d + d ≤ 2 * r * d := by linarith
      omega⟩
  NOF.Protocol.sendBits 2 (2 * r * d) pack fun M =>
    NOF.Protocol.runAll (fun t => followCharlie d (unpack M t) (ps t)) strictMaj

private theorem isCharlieFirst_amplifyCFDet {X : Fin 3 → Type*} {d r : ℕ}
    {ps : Fin (2 * r) → NOF.Protocol X Bool}
    (hcf : ∀ t, IsCharlieFirst (ps t)) (hd : ∀ t, (ps t).depth ≤ d) :
    IsCharlieFirst (amplifyCFDet d r ps) := by
  refine isCharlieFirst_sendBits_two fun M => isCharlieFirst_of_isAliceBobOnly ?_
  exact isAliceBobOnly_runAll (fun t => isAliceBobOnly_followCharlie (hcf t) (hd t) _) _

private theorem depth_amplifyCFDet_le {X : Fin 3 → Type*} {d r : ℕ}
    {ps : Fin (2 * r) → NOF.Protocol X Bool} (hd : ∀ t, (ps t).depth ≤ d) :
    (amplifyCFDet d r ps).depth ≤ 4 * r * d := by
  have hsum : 2 * r * d + 2 * r * d = 4 * r * d := by ring
  refine (NOF.Protocol.depth_sendBits_le (d := 2 * r * d) fun M => ?_).trans hsum.le
  exact NOF.Protocol.depth_runAll_le fun t => (depth_followCharlie_le (ps t) d _).trans (hd t)

private theorem run_amplifyCFDet {X : Fin 3 → Type*} {d r : ℕ}
    {ps : Fin (2 * r) → NOF.Protocol X Bool} (hd : ∀ t, (ps t).depth ≤ d) (x : ∀ i : Fin 3, X i) :
    (amplifyCFDet d r ps).run x = strictMaj (fun t => (ps t).run x) := by
  unfold amplifyCFDet
  rw [NOF.Protocol.run_sendBits, NOF.Protocol.run_runAll]
  congr 1; funext t
  dsimp only
  have hunpack : (fun j : Fin d =>
      (if hd0 : d = 0 then false
       else
         let t' : Fin (2 * r) :=
           ⟨(t.val * d + j.val) / d,
             (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero hd0)).mpr (by
               have h1 : (t.val + 1) * d ≤ 2 * r * d := Nat.mul_le_mul_right d t.isLt
               have : t.val * d + d ≤ 2 * r * d := by linarith
               omega)⟩
         let j' : Fin d := ⟨(t.val * d + j.val) % d, Nat.mod_lt _ (Nat.pos_of_ne_zero hd0)⟩
         charlieMsg (NOF.view 2 x ⟨0, by decide⟩) (NOF.view 2 x ⟨1, by decide⟩) d (ps t') j')) =
      charlieMsg (x 0) (x 1) d (ps t) := by
    funext j
    have hd0 : d ≠ 0 := by have := j.isLt; omega
    rw [dite_eq_right hd0]
    have hdiv : (t.val * d + j.val) / d = t.val := by
      rw [mul_comm t.val d, Nat.mul_add_div (Nat.pos_of_ne_zero hd0), Nat.div_eq_of_lt j.isLt,
        add_zero]
    have hmod : (t.val * d + j.val) % d = j.val := by
      rw [mul_comm t.val d, Nat.mul_add_mod, Nat.mod_eq_of_lt j.isLt]
    have hlt_prod : t.val * d + j.val < 2 * r * d := by
      have h1 : (t.val + 1) * d ≤ 2 * r * d := Nat.mul_le_mul_right d t.isLt
      have : t.val * d + d ≤ 2 * r * d := by linarith
      omega
    have ht_eq : (⟨(t.val * d + j.val) / d,
        (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero hd0)).mpr hlt_prod⟩ : Fin (2 * r)) = t :=
      Fin.ext hdiv
    have hj_eq : (⟨(t.val * d + j.val) % d, Nat.mod_lt _ (Nat.pos_of_ne_zero hd0)⟩ : Fin d) = j :=
      Fin.ext hmod
    rw [ht_eq, hj_eq]
    rfl
  rw [hunpack, run_followCharlie_charlieMsg (ps t) x (hd t)]

/-- Public-coin Charlie-first majority amplification (`(8 / 9) ^ r` error in depth `≤ 4 * r * d`).
-/
private noncomputable def amplifyCF {X : Fin 3 → Type*} (μ : NOF.PublicCoin X Bool) (d r : ℕ) :
    NOF.PublicCoin X Bool :=
  (Cslib.Probability.PMF.iid μ (2 * r)).map (amplifyCFDet d r)

private theorem amplifyCF_spec {X : Fin 3 → Type*} {μ : NOF.PublicCoin X Bool} {d r : ℕ}
    {f : (∀ i : Fin 3, X i) → Bool}
    (hcf : IsCharlieFirstPublicCoin μ) (hdepth : μ.depth ≤ d)
    (hsolves : μ.Solves (1 / 3) (fun x b => f x = b) Set.univ) :
    IsCharlieFirstPublicCoin (amplifyCF μ d r) ∧
    (amplifyCF μ d r).depth ≤ 4 * r * d ∧
    (amplifyCF μ d r).Solves ((8 / 9 : ℝ) ^ r) (fun x b => f x = b) Set.univ := by
  classical
  have hsupp : ∀ ps ∈ (Cslib.Probability.PMF.iid μ (2 * r)).support,
      (∀ t, IsCharlieFirst (ps t)) ∧ (∀ t, (ps t).depth ≤ d) := by
    intro ps hps
    rw [Cslib.Probability.PMF.mem_support_iid_iff] at hps
    refine ⟨fun t => hcf (ps t) (hps t), fun t => ?_⟩
    exact_mod_cast (NOF.PublicCoin.depth_le_depth (hps t)).trans hdepth
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    rw [amplifyCF, PMF.support_map] at hq
    obtain ⟨ps, hps, rfl⟩ := hq
    exact isCharlieFirst_amplifyCFDet (hsupp ps hps).1 (hsupp ps hps).2
  · rw [NOF.PublicCoin.depth_le_iff]
    intro q hq
    rw [amplifyCF, PMF.support_map] at hq
    obtain ⟨ps, hps, rfl⟩ := hq
    exact_mod_cast depth_amplifyCFDet_le (hsupp ps hps).2
  · intro x _
    -- Express `errorProb` directly via `iid_card_ge_le`.
    let errInd (p : NOF.Protocol X Bool) : Bool := decide (p.run x ≠ f x)
    let q : PMF Bool := μ.map errInd
    have hq_true : (q true).toReal ≤ 1 / 3 := by
      have h1 : (q true).toReal = μ.errorProb (fun x' b => f x' = b) x := by
        dsimp only [q]
        rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
        unfold NOF.PublicCoin.errorProb
        congr 2
        ext p
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, errInd,
          decide_eq_true_eq]
        exact ne_comm
      rw [h1]
      exact hsolves x (Set.mem_univ x)
    have hiid := Cslib.Probability.PMF.iid_card_ge_le hq_true (by norm_num : (1 / 3 : ℝ) ≤ 1 / 2) r
    have h4eq : (4 * (1 / 3 : ℝ) * (1 - 1 / 3)) ^ r = (8 / 9 : ℝ) ^ r := by norm_num
    rw [h4eq] at hiid
    refine le_trans ?_ hiid
    -- Compare `{q | ¬ f x = q.run x}` under `amplifyCF` with `{v | r ≤ card {t | v t = true}}`.
    change ((amplifyCF μ d r).toOuterMeasure {p | ¬ f x = p.run x}).toReal ≤
      ((Cslib.Probability.PMF.iid q (2 * r)).toOuterMeasure
        {v | r ≤ (Finset.univ.filter fun t => v t = true).card}).toReal
    rw [amplifyCF, PMF.toOuterMeasure_map_apply,
      show Cslib.Probability.PMF.iid q (2 * r) =
        (Cslib.Probability.PMF.iid μ (2 * r)).map (fun ps t => errInd (ps t)) from
          Cslib.Probability.PMF.iid_map μ errInd (2 * r),
      PMF.toOuterMeasure_map_apply]
    -- Show support-restricted inclusion: if `ps ∈ supp` and `amplifyCFDet` errs, then `≥ r` err.
    have hle_enn :
        (Cslib.Probability.PMF.iid μ (2 * r)).toOuterMeasure
          (amplifyCFDet d r ⁻¹' {p | ¬ f x = p.run x}) ≤
        (Cslib.Probability.PMF.iid μ (2 * r)).toOuterMeasure
          ((fun ps t => errInd (ps t)) ⁻¹'
            {v | r ≤ (Finset.univ.filter fun t => v t = true).card}) := by
      simp_rw [PMF.toOuterMeasure_apply]
      refine tsum_le_tsum fun ps => ?_
      by_cases hps : ps ∈ (Cslib.Probability.PMF.iid μ (2 * r)).support
      · by_cases herr : ¬ f x = (amplifyCFDet d r ps).run x
        · have hmem : ps ∈ (fun ps t => errInd (ps t)) ⁻¹'
              {v | r ≤ (Finset.univ.filter fun t => v t = true).card} := by
            simp only [Set.mem_preimage, Set.mem_ofPred_eq]
            rw [run_amplifyCFDet (hsupp ps hps).2 x] at herr
            unfold strictMaj at herr
            let S_true := Finset.univ.filter fun t : Fin (2 * r) => (ps t).run x = true
            let S_err := Finset.univ.filter fun t : Fin (2 * r) => errInd (ps t) = true
            cases hfx : f x
            · rw [hfx] at herr
              have hgt : r < S_true.card := by
                by_contra hle; simp [S_true, hle] at herr
              have hEq : S_err = S_true := by
                ext t; simp [S_err, S_true, errInd, hfx]
              change r ≤ S_err.card
              rw [hEq]; omega
            · rw [hfx] at herr
              have hle : S_true.card ≤ r := by
                by_contra hgt; push Not at hgt; simp [S_true, hgt] at herr
              have hcomp : S_err.card + S_true.card = 2 * r := by
                have hdisj : Disjoint S_err S_true := by
                  rw [Finset.disjoint_left]
                  intro t h1 h2
                  simp only [S_err, S_true, Finset.mem_filter, Finset.mem_univ, true_and, errInd,
                    hfx, decide_eq_true_eq] at h1 h2
                  exact h1 h2
                have hunion : S_err ∪ S_true = Finset.univ := by
                  ext t; simp only [S_err, S_true, Finset.mem_union, Finset.mem_filter,
                    Finset.mem_univ, true_and, errInd, hfx, decide_eq_true_eq, iff_true]
                  exact (em ((ps t).run x = true)).symm
                rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ,
                  Fintype.card_fin]
              change r ≤ S_err.card
              omega
          rw [Set.indicator_of_mem hmem]
          exact Set.indicator_le_self _ _ _
        · rw [Set.indicator_of_notMem (by simpa using herr)]; exact zero_le
      · have hzero : Cslib.Probability.PMF.iid μ (2 * r) ps = 0 := by
          simpa [PMF.mem_support_iff] using hps
        simp [Set.indicator, hzero]
    exact ENNReal.toReal_mono (ne_of_lt (lt_of_le_of_lt
      (Cslib.Probability.PMF.toOuterMeasure_le_one _ _) ENNReal.one_lt_top)) hle_enn

/-! ### Elementary Hamming-Ball Volume Bound -/

/-- The Hamming ball of radius `D` in `BitString k`. -/
private def hammingBall (k D : ℕ) : Finset (BitString k) :=
  Finset.univ.filter fun e : BitString k =>
    (Finset.univ.filter fun i : Fin k => e i = true).card ≤ D

private theorem card_hammingBall_eq (k D : ℕ) :
    (hammingBall k D).card = ∑ j ∈ Finset.range (min D k + 1), Nat.choose k j := by
  classical
  -- Biject `e : BitString k` with `S : Finset (Fin k)` via `fun e => univ.filter (e · = true)`.
  let toSet (e : BitString k) : Finset (Fin k) := Finset.univ.filter fun i => e i = true
  have hbij : (hammingBall k D).card =
      ((Finset.univ : Finset (Finset (Fin k))).filter fun s => s.card ≤ D).card := by
    refine Finset.card_bij (fun e _ => toSet e) ?_ ?_ ?_
    · intro e he
      simp only [hammingBall, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
      exact he
    · intro e₁ _ e₂ _ h
      funext i
      have hi : e₁ i = true ↔ e₂ i = true := by
        have := Finset.ext_iff.mp h i
        simpa [toSet] using this
      cases h1 : e₁ i <;> cases h2 : e₂ i <;> simp_all
    · intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
      refine ⟨fun i => decide (i ∈ s), ?_, ?_⟩
      · simp only [hammingBall, Finset.mem_filter, Finset.mem_univ, true_and]
        have hEq : (Finset.univ.filter fun i => decide (i ∈ s) = true) = s := by
          ext i; simp
        rw [hEq]; exact hs
      · ext i; simp [toSet]
  rw [hbij]
  have hpart : ((Finset.univ : Finset (Finset (Fin k))).filter fun s => s.card ≤ D) =
      (Finset.range (min D k + 1)).biUnion fun j => Finset.powersetCard j Finset.univ := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_range, Finset.mem_powersetCard, Finset.subset_univ]
    constructor
    · intro hs
      have hsk : s.card ≤ k := by
        simpa [Fintype.card_fin] using Finset.card_le_univ s
      exact ⟨s.card, by omega, rfl⟩
    · rintro ⟨j, hj, rfl⟩; omega
  rw [hpart, Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  · intro j₁ _ j₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro s h1 h2
    simp only [Finset.mem_powersetCard] at h1 h2
    exact hne (h1.2.symm.trans h2.2)

/-- Elementary Chernoff/binomial upper bound on the Hamming ball of radius `D ≤ η * k`:
for any `0 < t ≤ 1`, `|hammingBall k D| ≤ ((1 + t) * (1 / t) ^ η) ^ k`. -/
private theorem card_hammingBall_le {k D : ℕ} {t η : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hD : (D : ℝ) ≤ η * (k : ℝ)) :
    ((hammingBall k D).card : ℝ) ≤ ((1 + t) * (1 / t) ^ η) ^ k := by
  rw [card_hammingBall_eq]
  have hinv_ge : 1 ≤ 1 / t := (one_le_div ht0).mpr ht1
  have hmul_le : t ^ D * ((∑ j ∈ Finset.range (min D k + 1), Nat.choose k j : ℕ) : ℝ) ≤
      (1 + t) ^ k := by
    rw [Nat.cast_sum, Finset.mul_sum]
    calc
      ∑ j ∈ Finset.range (min D k + 1), t ^ D * (Nat.choose k j : ℝ)
        ≤ ∑ j ∈ Finset.range (min D k + 1), t ^ j * (Nat.choose k j : ℝ) := by
          refine Finset.sum_le_sum fun j hj => ?_
          rw [Finset.mem_range] at hj
          have hjD : j ≤ D := by omega
          exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one ht0.le ht1 hjD)
            (Nat.cast_nonneg _)
      _ ≤ ∑ j ∈ Finset.range (k + 1), t ^ j * (Nat.choose k j : ℝ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
          exact Finset.range_mono (by omega)
      _ = (t + 1) ^ k := by
          rw [add_pow]
          refine Finset.sum_congr rfl fun j _ => by simp
      _ = (1 + t) ^ k := by ring
  have htd_pos : 0 < t ^ D := pow_pos ht0 D
  have h1 : ((∑ j ∈ Finset.range (min D k + 1), Nat.choose k j : ℕ) : ℝ) ≤
      (1 + t) ^ k * (1 / t) ^ D := by
    have := (le_div_iff₀ htd_pos).mpr (by linarith : ((∑ j ∈ Finset.range (min D k + 1),
      Nat.choose k j : ℕ) : ℝ) * t ^ D ≤ (1 + t) ^ k)
    simpa [div_eq_mul_inv, inv_pow, one_div] using this
  have h2 : (1 / t) ^ D ≤ ((1 / t) ^ η) ^ k := by
    rw [← Real.rpow_natCast (1 / t) D, ← Real.rpow_natCast ((1 / t) ^ η) k,
      ← Real.rpow_mul (by positivity)]
    exact Real.rpow_le_rpow_of_exponent_le hinv_ge hD
  calc
    ((∑ j ∈ Finset.range (min D k + 1), Nat.choose k j : ℕ) : ℝ)
      ≤ (1 + t) ^ k * (1 / t) ^ D := h1
    _ ≤ (1 + t) ^ k * ((1 / t) ^ η) ^ k := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = ((1 + t) * (1 / t) ^ η) ^ k := (mul_pow _ _ _).symm

/-! ### Base-Case Positivity (`d ≥ 1` for `n ≥ 1`) -/

private theorem nof_ndisj3_depth_pos {n d : ℕ} (hn : 1 ≤ n)
    {μ : NOF.PublicCoin (fun _ : Fin 3 => BitString n) Bool}
    (hdepth : μ.depth ≤ d)
    (hsolves : μ.Solves (1 / 3) (fun x b => nofNDisj3 n x = b) Set.univ) :
    1 ≤ d := by
  classical
  by_contra hd0
  have hd_eq : d = 0 := by omega
  subst hd_eq
  let x₀ : ∀ _ : Fin 3, BitString n := fun _ _ => false
  let x₁ : ∀ _ : Fin 3, BitString n := fun _ _ => true
  have hf0 : nofNDisj3 n x₀ = false := by simp [nofNDisj3, x₀]
  have hf1 : nofNDisj3 n x₁ = true := by
    simp only [nofNDisj3, x₁, decide_eq_true_eq]
    exact ⟨⟨0, by omega⟩, trivial, trivial, trivial⟩
  -- Every depth-0 protocol in `μ.support` outputs the same constant on `x₀` and `x₁`.
  have hconst : ∀ p ∈ μ.support, p.run x₀ = p.run x₁ := by
    intro p hp
    have hpd : p.depth = 0 := by
      have : (p.depth : ℕ∞) ≤ 0 := (NOF.PublicCoin.depth_le_depth hp).trans hdepth
      exact Nat.eq_zero_of_le_zero (by exact_mod_cast this)
    cases p with
    | output z => rfl
    | speak _ _ _ _ => simp [NOF.Protocol.depth_speak] at hpd
  -- Hence `errorProb x₀ + errorProb x₁ ≥ 1`, contradicting `≤ 1 / 3 + 1 / 3`.
  have hcover : {p : NOF.Protocol (fun _ : Fin 3 => BitString n) Bool | p ∈ μ.support} ⊆
      {p | ¬ nofNDisj3 n x₀ = p.run x₀} ∪ {p | ¬ nofNDisj3 n x₁ = p.run x₁} := by
    intro p hp
    by_cases h0 : nofNDisj3 n x₀ = p.run x₀
    · right
      simp only [Set.mem_ofPred_eq]
      rw [← hconst p hp, ← h0, hf0, hf1]
      decide
    · left; exact h0
  have hsum_ge : 1 ≤ μ.errorProb (fun x b => nofNDisj3 n x = b) x₀ +
      μ.errorProb (fun x b => nofNDisj3 n x = b) x₁ := by
    have hunion : μ.toOuterMeasure {p | p ∈ μ.support} ≤
        μ.toOuterMeasure {p | ¬ nofNDisj3 n x₀ = p.run x₀} +
        μ.toOuterMeasure {p | ¬ nofNDisj3 n x₁ = p.run x₁} := by
      refine (μ.toOuterMeasure.mono hcover).trans ?_
      simp_rw [PMF.toOuterMeasure_apply]
      rw [← tsum_add]
      refine tsum_le_tsum fun p => ?_
      by_cases h0 : ¬ nofNDisj3 n x₀ = p.run x₀ <;> by_cases h1 : ¬ nofNDisj3 n x₁ = p.run x₁ <;>
        simp [h0, h1]
    have hsupp1 : μ.toOuterMeasure {p | p ∈ μ.support} = 1 := by
      rw [PMF.toOuterMeasure_apply]
      calc
        ∑' p, ({p' | p' ∈ μ.support}).indicator (⇑μ) p = ∑' p, μ p := by
          congr 1; funext p
          by_cases hp : p ∈ μ.support
          · rw [Set.indicator_of_mem (show p ∈ {p' | p' ∈ μ.support} from hp)]
          · rw [Set.indicator_of_notMem (show p ∉ {p' | p' ∈ μ.support} from hp)]
            symm; simpa [PMF.mem_support_iff] using hp
        _ = 1 := μ.tsum_coe
    rw [hsupp1] at hunion
    have hfin : ∀ S, μ.toOuterMeasure S ≠ ⊤ := fun S =>
      ne_of_lt (lt_of_le_of_lt (Cslib.Probability.PMF.toOuterMeasure_le_one μ S) ENNReal.one_lt_top)
    have htoReal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin _, hfin _⟩) hunion
    rw [ENNReal.toReal_one, ENNReal.toReal_add (hfin _) (hfin _)] at htoReal
    exact htoReal
  linarith [hsolves x₀ (Set.mem_univ _), hsolves x₁ (Set.mem_univ _)]

/-! ### Charlie-First Three-Party NOF Disjointness Lower Bound -/

/-- Randomized lower bound for three-party Charlie-first NOF Nondisjointness:
In the 3-party NOF model where Charlie sends one message followed by an arbitrary interaction
between Alice and Bob, 3-party Nondisjointness `nofNDisj3 n` has randomized bounded-error
complexity `Ω(√n)`. -/
theorem nof_charlieFirst_ndisj_lower_bound :
    ∃ c : ℝ, 0 < c ∧
      ∀ (n d : ℕ) (μ : NOF.PublicCoin (fun _ : Fin 3 => BitString n) Bool),
        IsCharlieFirstPublicCoin μ →
        μ.depth ≤ d →
        μ.Solves (1 / 3) (fun x b => nofNDisj3 n x = b) Set.univ →
        c * Real.sqrt (n : ℝ) ≤ (d : ℝ) := by
  classical
  have hα0 := alphaNDisj_mem.1
  have hα1 := alphaNDisj_mem.2
  have hβ0 := betaNDisj_mem.1
  -- Step 1: Choose `t = alphaNDisj / 16 ∈ (0, 1]` and amplification parameter `r ≥ 1` so that
  -- `((1 + t) * (1 / t) ^ η) ≤ 2 ^ (alphaNDisj / 4)` where `η = 2 * (8 / 9) ^ r`.
  let t : ℝ := alphaNDisj / 16
  have ht0 : 0 < t := by dsimp only [t]; linarith
  have ht1 : t ≤ 1 := by dsimp only [t]; linarith
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog2_gt : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have h1pt : 1 + t ≤ (2 : ℝ) ^ (alphaNDisj / 8) := by
    calc
      1 + t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
      _ ≤ Real.exp ((alphaNDisj / 8) * Real.log 2) := by
          apply Real.exp_le_exp.mpr
          dsimp only [t]; nlinarith
      _ = (2 : ℝ) ^ (alphaNDisj / 8) := by
          rw [Real.rpow_def_of_pos two_pos, mul_comm]
  have hinv_ge1 : 1 ≤ 1 / t := (one_le_div ht0).mpr ht1
  have hlog_inv_pos : 0 < Real.log (1 / t) := by
    apply Real.log_pos
    rw [one_lt_div ht0]; dsimp only [t]; linarith
  -- Choose `r ≥ 1` such that `2 * (8 / 9) ^ r * log (1 / t) ≤ (alphaNDisj / 8) * log 2`.
  have hex_r : ∃ r : ℕ, 1 ≤ r ∧
      2 * (8 / 9 : ℝ) ^ r * Real.log (1 / t) ≤ (alphaNDisj / 8) * Real.log 2 := by
    let target : ℝ := (alphaNDisj / 8) * Real.log 2 / (2 * Real.log (1 / t))
    have htarget : 0 < target := by positivity
    obtain ⟨r₀, hr₀⟩ := exists_pow_lt_of_lt_one htarget (by norm_num : (8 / 9 : ℝ) < 1)
    refine ⟨max 1 r₀, le_max_left _ _, ?_⟩
    have hpow_le : (8 / 9 : ℝ) ^ (max 1 r₀) ≤ (8 / 9 : ℝ) ^ r₀ :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_max_right 1 r₀)
    have hlt : (8 / 9 : ℝ) ^ (max 1 r₀) < target := lt_of_le_of_lt hpow_le hr₀
    have hden_pos : 0 < 2 * Real.log (1 / t) := by positivity
    have := (lt_div_iff₀ hden_pos).mp hlt
    linarith
  obtain ⟨r, hr1, hr_bound⟩ := hex_r
  let δ : ℝ := (8 / 9 : ℝ) ^ r
  let η : ℝ := 2 * δ
  have hδ0 : 0 < δ := by dsimp only [δ]; positivity
  have hη0 : 0 < η := by dsimp only [η]; positivity
  have hball_base : (1 + t) * (1 / t) ^ η ≤ (2 : ℝ) ^ (alphaNDisj / 4) := by
    have h2 : (1 / t) ^ η ≤ (2 : ℝ) ^ (alphaNDisj / 8) := by
      rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos two_pos]
      apply Real.exp_le_exp.mpr
      rw [mul_comm (Real.log (1 / t)), mul_comm (Real.log 2)]
      exact hr_bound
    calc
      (1 + t) * (1 / t) ^ η
        ≤ (2 : ℝ) ^ (alphaNDisj / 8) * (2 : ℝ) ^ (alphaNDisj / 8) :=
          mul_le_mul h1pt h2 (by positivity) (by positivity)
      _ = (2 : ℝ) ^ (alphaNDisj / 8 + alphaNDisj / 8) := (Real.rpow_add two_pos _ _).symm
      _ = (2 : ℝ) ^ (alphaNDisj / 4) := by congr 1; ring
  -- Step 2: Set threshold `k₀` and explicit positive constant `c`.
  let k₀ : ℕ := max 1 (Nat.ceil (4 / alphaNDisj))
  have hk₀_pos : 1 ≤ k₀ := le_max_left _ _
  let c : ℝ := min (1 / (k₀ : ℝ)) (min (betaNDisj / (8 * (r : ℝ))) (alphaNDisj / (32 * (r : ℝ))))
  have hc_pos : 0 < c := by
    dsimp only [c]
    have hrR : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr (by omega)
    have hk₀R : (0 : ℝ) < (k₀ : ℝ) := Nat.cast_pos.mpr (by omega)
    exact lt_min (by positivity) (lt_min (by positivity) (by positivity))
  refine ⟨c, hc_pos, fun n d μ hcf hdepth hsolves => ?_⟩
  by_cases hn0 : n = 0
  · subst hn0; simp
  have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn0
  have hd1 : 1 ≤ d := nof_ndisj3_depth_pos hn1 hdepth hsolves
  let k : ℕ := Nat.sqrt n
  have hsqrt_lt : Real.sqrt (n : ℝ) < (k : ℝ) + 1 := by
    have hlt_nat : n < (k + 1) ^ 2 := Nat.lt_succ_sqrt' n
    have hlt_R : (n : ℝ) < ((k : ℝ) + 1) ^ 2 := by
      have : (n : ℝ) < (((k + 1) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hlt_nat
      push_cast at this; linarith
    calc
      Real.sqrt (n : ℝ) < Real.sqrt (((k : ℝ) + 1) ^ 2) :=
        Real.sqrt_lt_sqrt (Nat.cast_nonneg n) hlt_R
      _ = (k : ℝ) + 1 := Real.sqrt_sq (by positivity)
  by_cases hk_small : k < k₀
  · -- Small `n`: `Real.sqrt n < k + 1 ≤ k₀`, so `c * Real.sqrt n ≤ (1 / k₀) * k₀ = 1 ≤ d`.
    have hle_k0 : Real.sqrt (n : ℝ) ≤ (k₀ : ℝ) := by
      have : (k : ℝ) + 1 ≤ (k₀ : ℝ) := by exact_mod_cast hk_small
      linarith
    have hc1 : c ≤ 1 / (k₀ : ℝ) := min_le_left _ _
    have hk₀R : (0 : ℝ) < (k₀ : ℝ) := Nat.cast_pos.mpr (by omega)
    calc
      c * Real.sqrt (n : ℝ) ≤ (1 / (k₀ : ℝ)) * (k₀ : ℝ) :=
        mul_le_mul hc1 hle_k0 (Real.sqrt_nonneg _) (by positivity)
      _ = 1 := by field_simp
      _ ≤ (d : ℝ) := by exact_mod_cast hd1
  · -- Large `n`: `k ≥ k₀ ≥ 1`; assume `d < c * Real.sqrt n` and contradict `sdpt_ndisj_bound`.
    push Not at hk_small
    have hk1 : 1 ≤ k := le_trans hk₀_pos hk_small
    have hkk_le : k * k ≤ n := Nat.sqrt_le n
    by_contra hlt_d
    push Not at hlt_d
    -- Amplify `μ` to Charlie-first `μ_r` of depth `≤ d_r = 4 * r * d` and error `≤ δ`.
    let d_r : ℕ := 4 * r * d
    let μ_r := amplifyCF μ d r
    obtain ⟨hcf_r, hdepth_r, hsolves_r⟩ := amplifyCF_spec hcf hdepth hsolves
    -- Bound `d_r` in terms of `k`.
    have hsqrt_le_2k : Real.sqrt (n : ℝ) ≤ 2 * (k : ℝ) := by
      have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
      linarith
    have hcb : c ≤ betaNDisj / (8 * (r : ℝ)) := (min_le_right _ _).trans (min_le_left _ _)
    have hca : c ≤ alphaNDisj / (32 * (r : ℝ)) := (min_le_right _ _).trans (min_le_right _ _)
    have hrR : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr (by omega)
    have hdr_le_beta : (d_r : ℝ) ≤ betaNDisj * (k : ℝ) := by
      dsimp only [d_r]; push_cast
      have h1 : (d : ℝ) ≤ (betaNDisj / (8 * (r : ℝ))) * (2 * (k : ℝ)) :=
        le_trans hlt_d.le (mul_le_mul hcb hsqrt_le_2k (Real.sqrt_nonneg _) (by positivity))
      have h2 : 4 * (r : ℝ) * ((betaNDisj / (8 * (r : ℝ))) * (2 * (k : ℝ))) =
          betaNDisj * (k : ℝ) := by field_simp; ring
      nlinarith
    have hdr_le_alpha : (d_r : ℝ) ≤ (alphaNDisj / 4) * (k : ℝ) := by
      dsimp only [d_r]; push_cast
      have h1 : (d : ℝ) ≤ (alphaNDisj / (32 * (r : ℝ))) * (2 * (k : ℝ)) :=
        le_trans hlt_d.le (mul_le_mul hca hsqrt_le_2k (Real.sqrt_nonneg _) (by positivity))
      have h2 : 4 * (r : ℝ) * ((alphaNDisj / (32 * (r : ℝ))) * (2 * (k : ℝ))) =
          (alphaNDisj / 4) * (k : ℝ) := by field_simp; ring
      nlinarith
    -- Block embedding of `(Fin k → BitString k)` into `BitString n` and block masks `Z_i`.
    let embVec (v : Fin k → BitString k) : BitString n := fun idx =>
      if h : idx.val < k * k then
        v ⟨idx.val / k, (Nat.div_lt_iff_lt_mul (by omega)).mpr (by simpa [mul_comm] using h)⟩
          ⟨idx.val % k, Nat.mod_lt _ (by omega)⟩
      else false
    let blockMask (i : Fin k) : BitString n := fun idx =>
      decide (i.val * k ≤ idx.val ∧ idx.val < (i.val + 1) * k)
    have hemb_correct : ∀ (x y : Fin k → BitString k) (i : Fin k),
        nofNDisj3 n (mkInput3 (embVec x) (embVec y) (blockMask i)) = ndisjK k k x y i := by
      intro x y i
      rw [Bool.eq_iff_iff, nofNDisj3_eq_true_iff, ndisjK_apply, ndisj_eq_true_iff_exists]
      simp only [mkInput3]
      constructor
      · rintro ⟨idx, hx, hy, hz⟩
        simp only [blockMask, decide_eq_true_eq] at hz
        have hlt_kk : idx.val < k * k := by
          have : (i.val + 1) * k ≤ k * k := Nat.mul_le_mul_right k i.isLt
          omega
        simp only [embVec, hlt_kk, ↓reduceDIte] at hx hy
        have hdiv : idx.val / k = i.val := by
          have h1 : i.val ≤ idx.val / k := (Nat.le_div_iff_mul_le hk1).mpr hz.1
          have h2 : idx.val / k < i.val + 1 := (Nat.div_lt_iff_lt_mul hk1).mpr hz.2
          omega
        have hi_eq : (⟨idx.val / k, (Nat.div_lt_iff_lt_mul hk1).mpr
            (by simpa [mul_comm] using hlt_kk)⟩ : Fin k) = i := Fin.ext hdiv
        rw [hi_eq] at hx hy
        exact ⟨⟨idx.val % k, Nat.mod_lt _ hk1⟩, hx, hy⟩
      · rintro ⟨j, hx, hy⟩
        have hlt_i : i.val * k + j.val < (i.val + 1) * k := by
          have : (i.val + 1) * k = i.val * k + k := by ring
          omega
        have hlt_kk : i.val * k + j.val < k * k :=
          lt_of_lt_of_le hlt_i (Nat.mul_le_mul_right k i.isLt)
        let idx : Fin n := ⟨i.val * k + j.val, lt_of_lt_of_le hlt_kk hkk_le⟩
        have hidx_lt : idx.val < k * k := hlt_kk
        have hdiv : idx.val / k = i.val := by
          change (i.val * k + j.val) / k = i.val
          rw [mul_comm i.val k, Nat.mul_add_div hk1, Nat.div_eq_of_lt j.isLt, add_zero]
        have hmod : idx.val % k = j.val := by
          change (i.val * k + j.val) % k = j.val
          rw [mul_comm i.val k, Nat.mul_add_mod, Nat.mod_eq_of_lt j.isLt]
        have hi_eq : (⟨idx.val / k, (Nat.div_lt_iff_lt_mul hk1).mpr
            (by simpa [mul_comm] using hidx_lt)⟩ : Fin k) = i := Fin.ext hdiv
        have hj_eq : (⟨idx.val % k, Nat.mod_lt _ hk1⟩ : Fin k) = j := Fin.ext hmod
        refine ⟨idx, ?_, ?_, ?_⟩
        · simp only [embVec, hidx_lt, ↓reduceDIte]
          rw [hi_eq, hj_eq]; exact hx
        · simp only [embVec, hidx_lt, ↓reduceDIte]
          rw [hi_eq, hj_eq]; exact hy
        · simp only [blockMask, decide_eq_true_eq]
          exact ⟨Nat.le_add_right _ _, hlt_i⟩
    -- Build the 2-party `PublicCoin` protocol `ν` for `NDISJ_k^(k)` by sampling:
    -- `p ~ μ_r`, uniform Charlie message `m : BitString d_r`, and uniform error mask `e ∈ B_η`.
    let D : ℕ := Nat.floor (η * (k : ℝ))
    let B_η := hammingBall k D
    have hB_nonempty : B_η.Nonempty := ⟨fun _ => false, by simp [B_η, hammingBall]⟩
    let unifM : PMF (BitString d_r) := Cslib.Probability.PMF.uniformOfFintype (BitString d_r)
    let unifE : PMF (BitString k) := Cslib.Probability.PMF.uniformOfFinset B_η hB_nonempty
    let buildP (p : NOF.Protocol (fun _ : Fin 3 => BitString n) Bool)
        (m : BitString d_r) (e : BitString k) :
        Protocol (Fin k → BitString k) (Fin k → BitString k) (BitString k) :=
      (Protocol.runAll (fun i : Fin k => toTwoParty (blockMask i) (followCharlie d_r m p))
        (fun out i => xor (out i) (e i))).comap embVec embVec
    let ν : PublicCoin (Fin k → BitString k) (Fin k → BitString k) (BitString k) :=
      μ_r.bind fun p => unifM.bind fun m => unifE.map fun e => buildP p m e
    -- Depth of `ν` is at most `k * d_r`.
    have hν_depth : ν.depth ≤ k * d_r := by
      rw [PublicCoin.depth_le_iff]
      intro q hq
      rw [PMF.mem_support_bind_iff] at hq
      obtain ⟨p, hp, hq⟩ := hq
      rw [PMF.mem_support_bind_iff] at hq
      obtain ⟨m, _, hq⟩ := hq
      rw [PMF.support_map] at hq
      obtain ⟨e, _, rfl⟩ := hq
      have hp_d : p.depth ≤ d_r := by
        exact_mod_cast (NOF.PublicCoin.depth_le_depth hp).trans hdepth_r
      have hbd : (buildP p m e).depth ≤ k * d_r := by
        dsimp only [buildP]
        rw [Protocol.depth_comap]
        exact Protocol.depth_runAll_le fun i =>
          (depth_toTwoParty_le _ _).trans ((depth_followCharlie_le p d_r m).trans hp_d)
      exact_mod_cast hbd
    -- Lower bound the success probability of `ν` on every `(x, y)` via Markov + uniform guessing.
    have hB_card_le : (B_η.card : ℝ) ≤ (2 : ℝ) ^ ((alphaNDisj / 4) * (k : ℝ)) := by
      have hD_le : (D : ℝ) ≤ η * (k : ℝ) := Nat.floor_le (by positivity)
      calc
        (B_η.card : ℝ) ≤ ((1 + t) * (1 / t) ^ η) ^ k := card_hammingBall_le ht0 ht1 hD_le
        _ ≤ ((2 : ℝ) ^ (alphaNDisj / 4)) ^ k :=
            pow_le_pow_left₀ (by positivity) hball_base k
        _ = (2 : ℝ) ^ ((alphaNDisj / 4) * (k : ℝ)) := by
            rw [← Real.rpow_natCast ((2 : ℝ) ^ _), ← Real.rpow_mul zero_le_two]
    let σ : ℝ := (1 / 2 : ℝ) * (2 : ℝ) ^ (-(d_r : ℝ)) *
      (2 : ℝ) ^ (-((alphaNDisj / 4) * (k : ℝ)))
    have hν_solves : SolvesWithSuccess ν σ (fun x y v => ndisjK k k x y = v) := by
      intro x y
      -- Markov's inequality on `p ~ μ_r`: `Pr[numErrs(p) ≤ D] ≥ 1 / 2`.
      let numErrs (p : NOF.Protocol (fun _ : Fin 3 => BitString n) Bool) : ℕ :=
        (Finset.univ.filter fun i : Fin k =>
          p.run (mkInput3 (embVec x) (embVec y) (blockMask i)) ≠ ndisjK k k x y i).card
      let GoodP : Set (NOF.Protocol (fun _ : Fin 3 => BitString n) Bool) :=
        {p | p ∈ μ_r.support ∧ numErrs p ≤ D}
      have hGoodP_ge : (1 / 2 : ℝ) ≤ (μ_r.toOuterMeasure GoodP).toReal := by
        let BadP : Set (NOF.Protocol (fun _ : Fin 3 => BitString n) Bool) :=
          {p | D < numErrs p}
        -- Upper bound `Pr[BadP] ≤ 1 / 2` via `∑_{i} errorProb_i ≤ δ * k`.
        have hBad_le : (μ_r.toOuterMeasure BadP).toReal ≤ 1 / 2 := by
          have hsum_err : ∑ i : Fin k,
              (μ_r.toOuterMeasure {p | p.run (mkInput3 (embVec x) (embVec y) (blockMask i)) ≠
                ndisjK k k x y i}).toReal ≤ δ * (k : ℝ) := by
            calc
              ∑ i : Fin k,
                  (μ_r.toOuterMeasure {p | p.run (mkInput3 (embVec x) (embVec y) (blockMask i)) ≠
                    ndisjK k k x y i}).toReal
                ≤ ∑ _i : Fin k, δ := by
                  refine Finset.sum_le_sum fun i _ => ?_
                  have hi := hsolves_r (mkInput3 (embVec x) (embVec y) (blockMask i))
                    (Set.mem_univ _)
                  have hset : {p : NOF.Protocol (fun _ : Fin 3 => BitString n) Bool |
                      p.run (mkInput3 (embVec x) (embVec y) (blockMask i)) ≠ ndisjK k k x y i} =
                      {p | ¬ nofNDisj3 n (mkInput3 (embVec x) (embVec y) (blockMask i)) =
                        p.run (mkInput3 (embVec x) (embVec y) (blockMask i))} := by
                    ext p; rw [hemb_correct x y i]; simp [eq_comm]
                  rw [hset]; exact hi
              _ = δ * (k : ℝ) := by
                  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]
          -- In `ENNReal`: `(D + 1) * μ_r(BadP) ≤ ∑ i, μ_r(Err_i)`.
          have hmarkov_enn : ((D + 1 : ℕ) : ENNReal) * μ_r.toOuterMeasure BadP ≤
              ∑ i : Fin k, μ_r.toOuterMeasure
                {p | p.run (mkInput3 (embVec x) (embVec y) (blockMask i)) ≠ ndisjK k k x y i} := by
            simp_rw [PMF.toOuterMeasure_apply]
            rw [← ENNReal.tsum_mul_left,
              ← Summable.tsum_finsetSum (fun _ _ => CompleteLattice.summable)]
            refine tsum_le_tsum fun p => ?_
            have hrhs : ∑ i : Fin k,
                ({p' | p'.run (mkInput3 (embVec x) (embVec y) (blockMask i)) ≠
                  ndisjK k k x y i}).indicator (⇑μ_r) p =
                ((numErrs p : ℕ) : ENNReal) * μ_r p := by
              dsimp only [numErrs]
              rw [Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum, Finset.sum_mul]
              refine Finset.sum_congr rfl fun i _ => ?_
              by_cases h : p.run (mkInput3 (embVec x) (embVec y) (blockMask i)) ≠ ndisjK k k x y i
              · simp [Set.indicator, h]
              · simp [Set.indicator, h]
            rw [hrhs]
            by_cases hbad : p ∈ BadP
            · rw [Set.indicator_of_mem hbad]
              have hle : D + 1 ≤ numErrs p := hbad
              gcongr
            · rw [Set.indicator_of_notMem hbad, mul_zero]; exact zero_le
          have hfin_rhs : (∑ i : Fin k, μ_r.toOuterMeasure
              {p | p.run (mkInput3 (embVec x) (embVec y) (blockMask i)) ≠
                ndisjK k k x y i}) ≠ ⊤ :=
            ENNReal.sum_ne_top.mpr fun i _ => ne_of_lt (lt_of_le_of_lt
              (Cslib.Probability.PMF.toOuterMeasure_le_one μ_r _) ENNReal.one_lt_top)
          have hmarkov_R := ENNReal.toReal_mono hfin_rhs hmarkov_enn
          rw [ENNReal.toReal_mul, ENNReal.toReal_natCast,
            ENNReal.toReal_sum (fun i _ => ne_of_lt (lt_of_le_of_lt
              (Cslib.Probability.PMF.toOuterMeasure_le_one μ_r _) ENNReal.one_lt_top))] at hmarkov_R
          have hD1_gt : η * (k : ℝ) < ((D + 1 : ℕ) : ℝ) := by
            push_cast; exact Nat.lt_floor_add_one (η * (k : ℝ))
          have hηk_pos : 0 < η * (k : ℝ) := by
            have hkR : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
            positivity
          have h2 : η * (k : ℝ) * (μ_r.toOuterMeasure BadP).toReal ≤ δ * (k : ℝ) := by
            have hnonneg : 0 ≤ (μ_r.toOuterMeasure BadP).toReal := ENNReal.toReal_nonneg
            calc
              η * (k : ℝ) * (μ_r.toOuterMeasure BadP).toReal
                ≤ ((D + 1 : ℕ) : ℝ) * (μ_r.toOuterMeasure BadP).toReal :=
                  mul_le_mul_of_nonneg_right hD1_gt.le hnonneg
              _ ≤ δ * (k : ℝ) := hmarkov_R.trans hsum_err
          have hkR_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
          dsimp only [η] at h2
          nlinarith
        -- `μ_r(GoodP) = μ_r(BadPᶜ) = 1 - μ_r(BadP) ≥ 1 / 2`.
        have hGood_eq : μ_r.toOuterMeasure GoodP = μ_r.toOuterMeasure BadPᶜ := by
          simp_rw [PMF.toOuterMeasure_apply]
          congr 1; funext p
          by_cases hp : p ∈ μ_r.support
          · by_cases hle : numErrs p ≤ D
            · rw [Set.indicator_of_mem (show p ∈ GoodP from ⟨hp, hle⟩),
                Set.indicator_of_mem (show p ∈ BadPᶜ by simp [BadP]; omega)]
            · rw [Set.indicator_of_notMem (by simp [GoodP, hle]),
                Set.indicator_of_notMem (by simp [BadP]; omega)]
          · have hz : μ_r p = 0 := by simpa [PMF.mem_support_iff] using hp
            simp [Set.indicator, hz]
        rw [hGood_eq]
        linarith [Cslib.Probability.PMF.toOuterMeasure_toReal_add_compl μ_r BadP]
      -- For every `p ∈ GoodP`, the single `(m₀, e₀)` pair succeeds with prob `≥ 2^(-d_r) *
      -- |B_η|⁻¹`.
      rw [successProb_eq_toOuterMeasure]
      let E : Set (Protocol (Fin k → BitString k) (Fin k → BitString k) (BitString k)) :=
        {q | ndisjK k k x y = q.run x y}
      have hENN : ENNReal.ofReal ((2 : ℝ) ^ (-(d_r : ℝ)) *
          (2 : ℝ) ^ (-((alphaNDisj / 4) * (k : ℝ)))) * μ_r.toOuterMeasure GoodP ≤
          ν.toOuterMeasure E := by
        rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_left]
        refine tsum_le_tsum fun p => ?_
        by_cases hp : p ∈ GoodP
        · rw [Set.indicator_of_mem hp, mul_comm]
          gcongr
          obtain ⟨hp_supp, hp_err⟩ := hp
          have hp_cf : IsCharlieFirst p := hcf_r p hp_supp
          have hp_d : p.depth ≤ d_r := by
            exact_mod_cast (NOF.PublicCoin.depth_le_depth hp_supp).trans hdepth_r
          let m₀ : BitString d_r := charlieMsg (embVec x) (embVec y) d_r p
          let e₀ : BitString k := fun i =>
            decide (p.run (mkInput3 (embVec x) (embVec y) (blockMask i)) ≠ ndisjK k k x y i)
          have he₀_mem : e₀ ∈ B_η := by
            simp only [B_η, hammingBall, Finset.mem_filter, Finset.mem_univ, true_and, e₀,
              decide_eq_true_eq]
            exact hp_err
          have hrun_eq : (buildP p m₀ e₀).run x y = ndisjK k k x y := by
            funext i
            dsimp only [buildP]
            rw [Protocol.run_comap, Protocol.run_runAll]
            dsimp only
            have hab : IsAliceBobOnly (followCharlie d_r m₀ p) :=
              isAliceBobOnly_followCharlie hp_cf hp_d m₀
            rw [run_toTwoParty (embVec x) (embVec y) (blockMask i) hab,
              show m₀ = charlieMsg ((mkInput3 (embVec x) (embVec y) (blockMask i)) 0)
                ((mkInput3 (embVec x) (embVec y) (blockMask i)) 1) d_r p from rfl,
              run_followCharlie_charlieMsg p _ hp_d]
            dsimp only [e₀]
            cases p.run (mkInput3 (embVec x) (embVec y) (blockMask i)) <;>
              cases ndisjK k k x y i <;> rfl
          rw [PMF.toOuterMeasure_bind_apply]
          -- Lower bound the `tsum` over `m` by the single term `m = m₀`.
          have hm_step : unifM m₀ * (unifE.map (buildP p m₀)).toOuterMeasure E ≤
              ∑' m, unifM m * (unifE.map (buildP p m)).toOuterMeasure E :=
            le_tsum (fun m => unifM m * (unifE.map (buildP p m)).toOuterMeasure E) m₀
          refine le_trans ?_ hm_step
          have he_step : unifE e₀ ≤ (unifE.map (buildP p m₀)).toOuterMeasure E := by
            rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply]
            have hmem : e₀ ∈ buildP p m₀ ⁻¹' E := by
              change ndisjK k k x y = (buildP p m₀ e₀).run x y
              exact hrun_eq.symm
            exact le_trans (le_of_eq (Set.indicator_of_mem hmem (⇑unifE)).symm)
              (le_tsum (fun e => (buildP p m₀ ⁻¹' E).indicator (⇑unifE) e) e₀)
          have hme : unifM m₀ * unifE e₀ ≤ unifM m₀ * (unifE.map (buildP p m₀)).toOuterMeasure E :=
            by gcongr
          refine le_trans ?_ hme
          rw [ENNReal.ofReal_mul (by positivity)]
          refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
          · -- `2^(-d_r) ≤ unifM m₀`.
            rw [← ENNReal.ofReal_toReal (PMF.apply_ne_top unifM m₀)]
            apply ENNReal.ofReal_le_ofReal
            rw [Cslib.Probability.PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
              ENNReal.toReal_natCast, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
              Nat.cast_pow, Nat.cast_ofNat, Real.rpow_neg zero_le_two, Real.rpow_natCast]
          · -- `2^(-(alphaNDisj/4)*k) ≤ unifE e₀`.
            rw [← ENNReal.ofReal_toReal (PMF.apply_ne_top unifE e₀)]
            apply ENNReal.ofReal_le_ofReal
            rw [Cslib.Probability.PMF.uniformOfFinset_apply, ite_eq_left he₀_mem,
              ENNReal.toReal_inv, ENNReal.toReal_natCast, Real.rpow_neg zero_le_two]
            exact inv_anti₀ (Nat.cast_pos.mpr hB_nonempty.card_pos) hB_card_le
        · rw [Set.indicator_of_notMem hp, mul_zero]; exact zero_le
      have htoReal := ENNReal.toReal_mono (ne_of_lt (lt_of_le_of_lt
        (Cslib.Probability.PMF.toOuterMeasure_le_one ν _) ENNReal.one_lt_top)) hENN
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at htoReal
      refine le_trans ?_ htoReal
      dsimp only [σ]
      calc
        (1 / 2 : ℝ) * (2 : ℝ) ^ (-(d_r : ℝ)) * (2 : ℝ) ^ (-((alphaNDisj / 4) * (k : ℝ)))
          = (2 : ℝ) ^ (-(d_r : ℝ)) * (2 : ℝ) ^ (-((alphaNDisj / 4) * (k : ℝ))) * (1 / 2 : ℝ) := by
            ring
        _ ≤ (2 : ℝ) ^ (-(d_r : ℝ)) * (2 : ℝ) ^ (-((alphaNDisj / 4) * (k : ℝ))) *
              (μ_r.toOuterMeasure GoodP).toReal :=
            mul_le_mul_of_nonneg_left hGoodP_ge (by positivity)
    -- Apply `sdpt_ndisj_bound` to `ν` and derive a contradiction.
    have hcomm_bd : ((k * d_r : ℕ) : ℝ) ≤ betaNDisj * (k : ℝ) * (k : ℝ) := by
      push_cast
      have := mul_le_mul_of_nonneg_left hdr_le_beta (Nat.cast_nonneg (α := ℝ) k)
      linarith
    have hsdpt := sdpt_ndisj_bound hk1 hcomm_bd hν_depth hν_solves
    -- Compare exponents: `σ ≥ 2 ^ (-(3/4) * alphaNDisj * k) > 2 ^ (-alphaNDisj * k)`.
    have hk_ge_ceil : 4 / alphaNDisj ≤ (k : ℝ) := by
      have h1 : 4 / alphaNDisj ≤ (Nat.ceil (4 / alphaNDisj) : ℝ) := Nat.le_ceil _
      have h2 : (Nat.ceil (4 / alphaNDisj) : ℝ) ≤ (k₀ : ℝ) := by
        exact_mod_cast le_max_right 1 (Nat.ceil (4 / alphaNDisj))
      have h3 : (k₀ : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_small
      linarith
    have h1le : (1 : ℝ) ≤ (alphaNDisj / 4) * (k : ℝ) := by
      have := (div_le_iff₀ hα0).mp hk_ge_ceil
      linarith
    have hσ_eq : σ = (2 : ℝ) ^ (-1 - (d_r : ℝ) - (alphaNDisj / 4) * (k : ℝ)) := by
      dsimp only [σ]
      have hhalf : (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) := by norm_num
      rw [hhalf, ← Real.rpow_add two_pos, ← Real.rpow_add two_pos]
      congr 1
    rw [hσ_eq] at hsdpt
    have hexp := (Real.rpow_le_rpow_left_iff one_lt_two).mp hsdpt
    have hkR : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
    nlinarith

/-- Randomized lower bound for three-party Charlie-first NOF Disjointness:
In the 3-party NOF model where Charlie sends one message followed by an arbitrary interaction
between Alice and Bob, 3-party Disjointness `nofDisj3 n` has randomized bounded-error
complexity `Ω(√n)`. -/
theorem nof_charlieFirst_disj_lower_bound :
    ∃ c : ℝ, 0 < c ∧
      ∀ (n d : ℕ) (μ : NOF.PublicCoin (fun _ : Fin 3 => BitString n) Bool),
        IsCharlieFirstPublicCoin μ →
        μ.depth ≤ d →
        μ.Solves (1 / 3) (fun x b => nofDisj3 n x = b) Set.univ →
        c * Real.sqrt (n : ℝ) ≤ (d : ℝ) := by
  obtain ⟨c, hc, hndisj⟩ := nof_charlieFirst_ndisj_lower_bound
  refine ⟨c, hc, fun n d μ hcf hdepth hsolves => ?_⟩
  let negP (p : NOF.Protocol (fun _ : Fin 3 => BitString n) Bool) :
      NOF.Protocol (fun _ : Fin 3 => BitString n) Bool :=
    p.bind fun b => .output (!b)
  let μ' : NOF.PublicCoin (fun _ : Fin 3 => BitString n) Bool := μ.map negP
  have hneg_ab : ∀ p : NOF.Protocol (fun _ : Fin 3 => BitString n) Bool,
      IsAliceBobOnly p → IsAliceBobOnly (negP p) :=
    fun p hp => isAliceBobOnly_bind hp (fun _ => trivial)
  have hneg_cf : ∀ p : NOF.Protocol (fun _ : Fin 3 => BitString n) Bool,
      IsCharlieFirst p → IsCharlieFirst (negP p) := by
    intro p
    induction p with
    | output _ => intro _; trivial
    | speak i send p₀ p₁ ih₀ ih₁ =>
      intro hp
      dsimp only [negP, NOF.Protocol.bind]
      by_cases hi : i = 2
      · simp only [IsCharlieFirst, ite_eq_left hi] at hp ⊢
        exact ⟨ih₀ hp.1, ih₁ hp.2⟩
      · simp only [IsCharlieFirst, ite_eq_right hi] at hp ⊢
        exact ⟨hneg_ab p₀ hp.1, hneg_ab p₁ hp.2⟩
  have hcf' : IsCharlieFirstPublicCoin μ' := by
    intro q hq
    rw [PMF.support_map] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    exact hneg_cf p (hcf p hp)
  have hdepth' : μ'.depth ≤ d := by
    rw [NOF.PublicCoin.depth_le_iff]
    intro q hq
    rw [PMF.support_map] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    have hle : (negP p).depth ≤ p.depth := by
      simpa using NOF.Protocol.depth_bind_le (p := p) (q := fun b => NOF.Protocol.output (!b))
        (d := 0) (fun _ => le_rfl)
    exact le_trans (by exact_mod_cast hle) ((NOF.PublicCoin.depth_le_depth hp).trans hdepth)
  have hsolves' : μ'.Solves (1 / 3) (fun x b => nofNDisj3 n x = b) Set.univ := by
    intro x _
    change ((μ.map negP).toOuterMeasure {p | ¬ nofNDisj3 n x = p.run x}).toReal ≤ 1 / 3
    rw [PMF.toOuterMeasure_map_apply]
    have hset : negP ⁻¹' {p | ¬ nofNDisj3 n x = p.run x} = {p | ¬ nofDisj3 n x = p.run x} := by
      ext p
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, negP, NOF.Protocol.run_bind,
        NOF.Protocol.run_output, nofDisj3]
      cases nofNDisj3 n x <;> cases p.run x <;> simp
    rw [hset]
    exact hsolves x (Set.mem_univ x)
  exact hndisj n d μ' hcf' hdepth' hsolves'

end

end CslibFrontier.Computability.Communication
