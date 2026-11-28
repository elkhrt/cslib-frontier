module

public import CslibFrontier.Computability.Communication.Discrepancy
public import CslibFrontier.Computability.Communication.Functions
public import CslibFrontier.Computability.Communication.Randomized
public import CslibFrontier.Foundations.Data.BitString.Basic
public import CslibFrontier.Probability.PMF
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Logb
import CslibFrontier.Foundations.Data.BitString.Sign
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Discrepancy Upper Bound for the Greater-Than Function

This module constructs a hard product-of-bitstrings distribution `greaterThanDist` for the
`n`-bit Greater-Than Boolean function `greaterThanBits n` and proves an `O(1 / √n)` upper bound
on its discrepancy, yielding an `Ω(log n)` public-coin randomized communication complexity
lower bound:

* **Hard distribution** (`greaterThanDist`, `greaterThanDistSucc`, `greaterThanDistExplicit`):
  defined both recursively on the most significant bit and via an explicit three-step sampling
  procedure (draw a split coordinate `k` uniformly from `0, …, n - 1`, sample a shared prefix
  above `k`, set opposing bits at `k`, and sample remaining suffix bits uniformly), proved equal
  in `greaterThanDistExplicit_eq_greaterThanDistSucc`.
* **Rectangle discrepancy bound** (`discrepancy_greaterThanSucc_rect_lt`,
  `discrepancy_greaterThanSucc_rect_le`): for every combinatorial rectangle `S × T` in
  `BitString n × BitString n` with uniform densities `s = |S| / 2^n` and `t = |T| / 2^n`, the
  rectangle discrepancy is at most `20 * √(s * t) / √n` (strictly `<` when `S` and `T` are
  nonempty).
* **Global discrepancy upper bound** (`discrepancy_greaterThan_lt`,
  `exists_dist_discrepancy_greaterThan_lt`):
  `discrepancy (greaterThanDist n hn) (greaterThanBits n) < 20 / √n` for every `n ≥ 1`.
* **Communication complexity lower bound** (`ecomplexity_greaterThan_lower_bound`):
  every `1/3`-error public-coin randomized protocol for `greaterThanBits n` requires at least
  `log₂(n) / 2 - 7` bits of communication.
-/

public section

namespace CslibFrontier.Computability.Communication.Discrepancy

open Finset Cslib Cslib.BitString Cslib.Communication Cslib.Probability
open scoped BigOperators ENNReal NNReal

/-! ### The Greater-Than Boolean function on `n`-bit strings -/

/-- The Greater-Than Boolean function `GT_n` on `n`-bit strings, interpreting bit strings as
binary numerals via `Cslib.BitString.equivFin` (with `Fin.last` as the most significant bit)
and reusing `Cslib.Communication.greaterThan`. -/
def greaterThanBits (n : ℕ) (x y : BitString n) : Bool :=
  Cslib.Communication.greaterThan (BitString.equivFin n x) (BitString.equivFin n y)

/-- Splitting `greaterThanBits (n + 1)` on the most significant bit (`Fin.last n`). -/
theorem greaterThanBits_snoc {n : ℕ} (x y : BitString n) (a b : Bool) :
    greaterThanBits (n + 1) (Fin.snoc x a) (Fin.snoc y b) =
      match a, b with
      | true, false => true
      | false, true => false
      | _, _ => greaterThanBits n x y := by
  have hx_lt := (BitString.equivFin n x).isLt
  have hy_lt := (BitString.equivFin n y).isLt
  have hval (z : BitString n) (c : Bool) :
      (BitString.equivFin (n + 1) (Fin.snoc z c) : ℕ) =
        (BitString.equivFin n z : ℕ) + c.toNat * 2 ^ n := by
    rw [BitString.val_equivFin_succ, Fin.init_snoc, Fin.snoc_last]
  simp only [greaterThanBits, Cslib.Communication.greaterThan, Fin.lt_def, hval]
  cases a <;> cases b
  · simp only [Bool.toNat_false, zero_mul, add_zero]
  · simp only [Bool.toNat_false, Bool.toNat_true, zero_mul, one_mul, add_zero]
    exact decide_eq_false (by omega)
  · simp only [Bool.toNat_false, Bool.toNat_true, zero_mul, one_mul, add_zero]
    exact decide_eq_true (by omega)
  · simp only [Bool.toNat_true, one_mul, add_lt_add_iff_right]

/-! ### The hard distribution `μ_n` for Greater-Than -/

/-- A Bernoulli PMF on `Bool` returning `true` with probability `p ≤ 1` and `false` with `1 - p`. -/
private noncomputable def bernoulliPMF (p : ℝ≥0) (hp : p ≤ 1) : PMF Bool :=
  PMF.ofFintype (fun b => if b then (p : ℝ≥0∞) else ((1 - p : ℝ≥0) : ℝ≥0∞)) (by
    rw [Fintype.sum_bool]
    simp only [↓reduceIte, Bool.false_eq_true, ← ENNReal.coe_add, add_tsub_cancel_of_le hp,
      ENNReal.coe_one])

private theorem bernoulliPMF_apply (p : ℝ≥0) (hp : p ≤ 1) (b : Bool) :
    bernoulliPMF p hp b = if b then (p : ℝ≥0∞) else ((1 - p : ℝ≥0) : ℝ≥0∞) :=
  PMF.ofFintype_apply _ b

/-- The distribution on `BitString (m + 1) × BitString (m + 1)` where the most significant bits
are opposite uniform bits `(w, !w)` and the lower `m` bits are independent uniform strings. -/
noncomputable def gtDiffMSB (m : ℕ) : PMF (BitString (m + 1) × BitString (m + 1)) :=
  (PMF.uniformOfFintype (Bool × BitString m × BitString m)).map fun ⟨w, x', y'⟩ =>
    (Fin.snoc (α := fun _ => Bool) x' w, Fin.snoc (α := fun _ => Bool) y' !w)

/-- Recursive construction of the hard distribution `μ_{m+1}` on
`BitString (m + 1) × BitString (m + 1)`. -/
noncomputable def greaterThanDistSucc : (m : ℕ) → PMF (BitString (m + 1) × BitString (m + 1))
  | 0 => gtDiffMSB 0
  | m + 1 =>
    let p : ℝ≥0 := ((m + 2 : ℕ) : ℝ≥0)⁻¹
    let hp : p ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast (by omega : 1 ≤ m + 2))
    (bernoulliPMF p hp).bind fun isTop =>
      if isTop then gtDiffMSB (m + 1)
      else (PMF.uniformOfFintype Bool).bind fun z =>
        (greaterThanDistSucc m).map fun ⟨x', y'⟩ =>
          (Fin.snoc (α := fun _ => Bool) x' z, Fin.snoc (α := fun _ => Bool) y' z)

/-- The hard distribution `μ_n` for `GT_n` on `BitString n × BitString n`, defined for `n ≥ 1`. -/
noncomputable def greaterThanDist (n : ℕ) (hn : 0 < n) : PMF (BitString n × BitString n) :=
  (greaterThanDistSucc (n - 1)).map (Equiv.prodCongr
    (Equiv.arrowCongr (finCongr (Nat.sub_add_cancel hn)) (Equiv.refl Bool))
    (Equiv.arrowCongr (finCongr (Nat.sub_add_cancel hn)) (Equiv.refl Bool)))

/-- Explicit three-step sampling definition of `μ_{m+1}`:
sample `k : Fin (m + 1)` uniformly, sample a shared prefix `z` above `k`, opposite bits `(w, !w)`
at `k`, and independent suffixes `(x', y')` below `k` (here `Fin.last` is the most significant
bit, matching `BitString.equivFin`). -/
noncomputable def greaterThanDistExplicit (m : ℕ) :
    PMF (BitString (m + 1) × BitString (m + 1)) :=
  (PMF.uniformOfFintype (Fin (m + 1))).bind fun k =>
    (PMF.uniformOfFintype (BitString (m + 1) × BitString (m + 1))).map fun ⟨a, b⟩ =>
      (fun i : Fin (m + 1) => if k.val < i.val then a i else if i = k then a k else a i,
       fun i : Fin (m + 1) => if k.val < i.val then a i else if i = k then !a k else b i)

/-- Injectivity of `(w, x', y') ↦ (Fin.snoc x' w, Fin.snoc y' !w)`. -/
private theorem snoc_diff_injective (m : ℕ) :
    Function.Injective (fun t : Bool × BitString m × BitString m =>
      (Fin.snoc (α := fun _ => Bool) t.2.1 t.1, Fin.snoc (α := fun _ => Bool) t.2.2 !t.1)) := by
  rintro ⟨w₁, x₁, y₁⟩ ⟨w₂, x₂, y₂⟩ h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  have hw : w₁ = w₂ := by
    have := congrFun h1 (Fin.last m)
    simpa [Fin.snoc_last] using this
  have hx : x₁ = x₂ := by
    have := congrArg Fin.init h1
    simpa [Fin.init_snoc] using this
  have hy : y₁ = y₂ := by
    have := congrArg Fin.init h2
    simpa [Fin.init_snoc] using this
  subst hw hx hy
  rfl

/-- Mass of `gtDiffMSB m` at `(Fin.snoc x' a, Fin.snoc y' b)`. -/
private theorem gtDiffMSB_apply_snoc (m : ℕ) (x' y' : BitString m) (a b : Bool) :
    gtDiffMSB m (Fin.snoc (α := fun _ => Bool) x' a, Fin.snoc (α := fun _ => Bool) y' b) =
      if a = !b then ((2 * 2 ^ m * 2 ^ m : ℕ) : ℝ≥0∞)⁻¹ else 0 := by
  classical
  rw [gtDiffMSB, PMF.map_apply]
  by_cases hab : a = !b
  · subst hab
    simp only [↓reduceIte]
    rw [tsum_eq_single (!b, x', y')]
    · simp only [Bool.not_not, ↓reduceIte, PMF.uniformOfFintype_apply, Fintype.card_prod,
        Fintype.card_bool, BitString.card, mul_assoc]
    · rintro ⟨w, u, v⟩ hne
      simp only [ite_eq_right_iff]
      intro heq
      exfalso
      apply hne
      have h' : (Fin.snoc (α := fun _ => Bool) u w, Fin.snoc (α := fun _ => Bool) v !w) =
          (Fin.snoc (α := fun _ => Bool) x' !b, Fin.snoc (α := fun _ => Bool) y' !(!b)) := by
        simpa [Bool.not_not] using heq.symm
      exact snoc_diff_injective m h'
  · simp only [hab, ↓reduceIte]
    refine tsum_eq_zero_iff.mpr fun ⟨w, u, v⟩ => ?_
    simp only [ite_eq_right_iff]
    intro heq
    exfalso
    have h1 := congrFun (congrArg Prod.fst heq) (Fin.last m)
    have h2 := congrFun (congrArg Prod.snd heq) (Fin.last m)
    simp only [Fin.snoc_last] at h1 h2
    exact hab (by rw [h1, h2, Bool.not_not])

/-- Mass of `greaterThanDistSucc (m + 1)` at `(Fin.snoc x' a, Fin.snoc y' b)`. -/
private theorem greaterThanDistSucc_succ_apply_snoc (m : ℕ) (x' y' : BitString (m + 1))
    (a b : Bool) :
    greaterThanDistSucc (m + 1)
        (Fin.snoc (α := fun _ => Bool) x' a, Fin.snoc (α := fun _ => Bool) y' b) =
      if a = b then
        ((m + 1 : ℕ) : ℝ≥0∞) / ((2 * (m + 2) : ℕ) : ℝ≥0∞) * greaterThanDistSucc m (x', y')
      else
        ((2 * (m + 2) * 2 ^ (m + 1) * 2 ^ (m + 1) : ℕ) : ℝ≥0∞)⁻¹ := by
  classical
  rw [greaterThanDistSucc, PMF.bind_apply, tsum_fintype, Fintype.sum_bool]
  simp only [↓reduceIte, Bool.false_eq_true, bernoulliPMF_apply]
  have hp_lt : ((m + 2 : ℕ) : ℝ≥0)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by exact_mod_cast (by omega : 1 ≤ m + 2))
  have h1sub : (1 - ((m + 2 : ℕ) : ℝ≥0)⁻¹ : ℝ≥0) = ((m + 1 : ℕ) : ℝ≥0) / ((m + 2 : ℕ) : ℝ≥0) := by
    have hm : ((m + 2 : ℕ) : ℝ≥0) ≠ 0 := by positivity
    rw [tsub_eq_iff_eq_add_of_le hp_lt, eq_comm]
    calc
      ((m + 1 : ℕ) : ℝ≥0) / ((m + 2 : ℕ) : ℝ≥0) + ((m + 2 : ℕ) : ℝ≥0)⁻¹
        = (((m + 1 : ℕ) : ℝ≥0) + 1) / ((m + 2 : ℕ) : ℝ≥0) := by
            rw [inv_eq_one_div, add_div]
      _ = ((m + 2 : ℕ) : ℝ≥0) / ((m + 2 : ℕ) : ℝ≥0) := by push_cast; ring_nf
      _ = 1 := div_self hm
  have hsame :
      ((PMF.uniformOfFintype Bool).bind fun z =>
          (greaterThanDistSucc m).map fun q =>
            (Fin.snoc (α := fun _ => Bool) q.1 z, Fin.snoc (α := fun _ => Bool) q.2 z))
        (Fin.snoc (α := fun _ => Bool) x' a, Fin.snoc (α := fun _ => Bool) y' b) =
      if a = b then (2 : ℝ≥0∞)⁻¹ * greaterThanDistSucc m (x', y') else 0 := by
    rw [PMF.bind_apply, tsum_fintype, Fintype.sum_bool]
    have hmap (z : Bool) :
        ((greaterThanDistSucc m).map fun q =>
            (Fin.snoc (α := fun _ => Bool) q.1 z, Fin.snoc (α := fun _ => Bool) q.2 z))
          (Fin.snoc (α := fun _ => Bool) x' a, Fin.snoc (α := fun _ => Bool) y' b) =
        if a = z ∧ b = z then greaterThanDistSucc m (x', y') else 0 := by
      rw [PMF.map_apply]
      by_cases hz : a = z ∧ b = z
      · rcases hz with ⟨rfl, rfl⟩
        simp only [and_self, ↓reduceIte]
        rw [tsum_eq_single (x', y')]
        · simp
        · rintro ⟨u, v⟩ hne
          simp only [ite_eq_right_iff]
          intro heq
          exfalso
          apply hne
          have h1 := congrArg Fin.init (congrArg Prod.fst heq)
          have h2 := congrArg Fin.init (congrArg Prod.snd heq)
          simp only [Fin.init_snoc] at h1 h2
          exact Prod.ext h1.symm h2.symm
      · simp only [hz, ↓reduceIte]
        refine tsum_eq_zero_iff.mpr fun ⟨u, v⟩ => ?_
        simp only [ite_eq_right_iff]
        intro heq
        exfalso
        have h1 := congrFun (congrArg Prod.fst heq) (Fin.last (m + 1))
        have h2 := congrFun (congrArg Prod.snd heq) (Fin.last (m + 1))
        simp only [Fin.snoc_last] at h1 h2
        exact hz ⟨h1, h2⟩
    simp only [hmap, PMF.uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat]
    cases a <;> cases b <;> simp
  rw [gtDiffMSB_apply_snoc, hsame, h1sub]
  have hcoe_inv : ((((m + 2 : ℕ) : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) = ((m + 2 : ℕ) : ℝ≥0∞)⁻¹ := by
    rw [ENNReal.coe_inv (by positivity), ENNReal.coe_natCast]
  have hcoe_div : ((((m + 1 : ℕ) : ℝ≥0) / ((m + 2 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ≥0∞) =
      ((m + 1 : ℕ) : ℝ≥0∞) / ((m + 2 : ℕ) : ℝ≥0∞) := by
    rw [ENNReal.coe_div (by positivity), ENNReal.coe_natCast, ENNReal.coe_natCast]
  rw [hcoe_inv, hcoe_div]
  cases a <;> cases b <;> simp only [↓reduceIte, Bool.false_eq_true, Bool.not_false, Bool.not_true,
    mul_zero, zero_add, add_zero]
  · rw [div_eq_mul_inv, div_eq_mul_inv, Nat.cast_mul, Nat.cast_ofNat,
      ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top)]
    ring
  · rw [← ENNReal.mul_inv (Or.inl (by positivity)) (Or.inr (by simp))]
    push_cast; ring_nf
  · rw [← ENNReal.mul_inv (Or.inl (by positivity)) (Or.inr (by simp))]
    push_cast; ring_nf
  · simp only [show (true = false) ↔ False by decide, ↓reduceIte, mul_zero, zero_add]
    rw [div_eq_mul_inv, div_eq_mul_inv, Nat.cast_mul, Nat.cast_ofNat,
      ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top)]
    ring

/-- Helper: splitting a uniform distribution on `Fin (m + 2)` into `Fin.last (m + 1)` vs
`Fin.castSucc`. -/
private theorem uniform_fin_succ_eq_bernoulli (m : ℕ) :
    PMF.uniformOfFintype (Fin (m + 2)) =
      (bernoulliPMF (((m + 2 : ℕ) : ℝ≥0)⁻¹)
          (inv_le_one_of_one_le₀ (by exact_mod_cast (by omega : 1 ≤ m + 2)))).bind fun isTop =>
        if isTop then PMF.pure (Fin.last (m + 1))
        else (PMF.uniformOfFintype (Fin (m + 1))).map Fin.castSucc := by
  classical
  ext i
  rw [PMF.uniformOfFintype_apply, Fintype.card_fin, PMF.bind_apply, tsum_fintype,
    Fintype.sum_bool]
  simp only [↓reduceIte, Bool.false_eq_true, bernoulliPMF_apply, PMF.pure_apply]
  have h1sub : (1 - ((m + 2 : ℕ) : ℝ≥0)⁻¹ : ℝ≥0) = ((m + 1 : ℕ) : ℝ≥0) / ((m + 2 : ℕ) : ℝ≥0) := by
    have hm : ((m + 2 : ℕ) : ℝ≥0) ≠ 0 := by positivity
    rw [tsub_eq_iff_eq_add_of_le
      (inv_le_one_of_one_le₀ (by exact_mod_cast (by omega : 1 ≤ m + 2))), eq_comm]
    calc
      ((m + 1 : ℕ) : ℝ≥0) / ((m + 2 : ℕ) : ℝ≥0) + ((m + 2 : ℕ) : ℝ≥0)⁻¹
        = (((m + 1 : ℕ) : ℝ≥0) + 1) / ((m + 2 : ℕ) : ℝ≥0) := by rw [inv_eq_one_div, add_div]
      _ = ((m + 2 : ℕ) : ℝ≥0) / ((m + 2 : ℕ) : ℝ≥0) := by push_cast; ring_nf
      _ = 1 := div_self hm
  rw [h1sub, ENNReal.coe_inv (by positivity), ENNReal.coe_div (by positivity),
    ENNReal.coe_natCast, ENNReal.coe_natCast]
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have hcast :
        ((PMF.uniformOfFintype (Fin (m + 1))).map Fin.castSucc) (Fin.last (m + 1)) = 0 := by
      rw [PMF.map_apply]
      refine tsum_eq_zero_iff.mpr fun j => ?_
      simp [(Fin.castSucc_ne_last j).symm]
    simp [hcast]
  · have hne : Fin.castSucc j ≠ Fin.last (m + 1) := Fin.castSucc_ne_last j
    have hcast : ((PMF.uniformOfFintype (Fin (m + 1))).map Fin.castSucc) (Fin.castSucc j) =
        ((m + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
      rw [PMF.map_apply, tsum_eq_single j]
      · simp [PMF.uniformOfFintype_apply]
      · intro j' hj'
        have hne' : Fin.castSucc j ≠ Fin.castSucc j' :=
          fun h => hj' (Fin.castSucc_injective _ h.symm)
        simp [hne']
    simp only [hne, ↓reduceIte, hcast, mul_zero, zero_add]
    rw [div_eq_mul_inv, mul_right_comm, ENNReal.mul_inv_cancel (by positivity) (by simp), one_mul]

/-- The explicit three-step sampling distribution agrees identically with the recursive
definition `greaterThanDistSucc`. -/
theorem greaterThanDistExplicit_eq_greaterThanDistSucc (m : ℕ) :
    greaterThanDistExplicit m = greaterThanDistSucc m := by
  induction m with
  | zero =>
    ext ⟨x, y⟩
    have hx : x = Fin.snoc (α := fun _ => Bool) (Fin.init x) (x (Fin.last 0)) :=
      (Fin.snoc_init_self x).symm
    have hy : y = Fin.snoc (α := fun _ => Bool) (Fin.init y) (y (Fin.last 0)) :=
      (Fin.snoc_init_self y).symm
    rw [hx, hy, greaterThanDistSucc, gtDiffMSB_apply_snoc]
    rw [greaterThanDistExplicit, PMF.bind_apply, tsum_fintype, Fin.sum_univ_one]
    simp only [PMF.uniformOfFintype_apply, Fintype.card_fin, PMF.map_apply, tsum_fintype]
    have hcard : Fintype.card (BitString 1 × BitString 1) = 4 := by
      simp [Fintype.card_prod]
    simp only [hcard, Nat.cast_ofNat]
    have hsum :
        (∑ q : BitString 1 × BitString 1,
          if (Fin.snoc (α := fun _ => Bool) (Fin.init x) (x (Fin.last 0)),
              Fin.snoc (α := fun _ => Bool) (Fin.init y) (y (Fin.last 0))) =
              (fun i : Fin 1 => if (0 : Fin 1).val < i.val then q.1 i
                else if i = 0 then q.1 0 else q.1 i,
               fun i : Fin 1 => if (0 : Fin 1).val < i.val then q.1 i
                else if i = 0 then !q.1 0 else q.2 i)
          then (4 : ℝ≥0∞)⁻¹ else 0) =
        if x (Fin.last 0) = !y (Fin.last 0) then (2 : ℝ≥0∞)⁻¹ else 0 := by
      have hcond (q : BitString 1 × BitString 1) :
          ((Fin.snoc (α := fun _ => Bool) (Fin.init x) (x (Fin.last 0)),
            Fin.snoc (α := fun _ => Bool) (Fin.init y) (y (Fin.last 0))) =
            (fun i : Fin 1 => if (0 : Fin 1).val < i.val then q.1 i
              else if i = 0 then q.1 0 else q.1 i,
             fun i : Fin 1 => if (0 : Fin 1).val < i.val then q.1 i
              else if i = 0 then !q.1 0 else q.2 i)) ↔
            q.1 0 = x 0 ∧ (!q.1 0) = y 0 := by
        rw [← hx, ← hy, Prod.mk.injEq, funext_iff, funext_iff]
        constructor
        · rintro ⟨h1, h2⟩
          have h10 := h1 0
          have h20 := h2 0
          simp only [Fin.val_zero, lt_self_iff_false, ↓reduceIte] at h10 h20
          exact ⟨h10.symm, h20.symm⟩
        · rintro ⟨h1, h2⟩
          refine ⟨fun i => ?_, fun i => ?_⟩
          · have hi : i = 0 := Fin.eq_zero i
            subst hi
            simp only [Fin.val_zero, lt_self_iff_false, ↓reduceIte, h1]
          · have hi : i = 0 := Fin.eq_zero i
            subst hi
            simp only [Fin.val_zero, lt_self_iff_false, ↓reduceIte, h2]
      simp_rw [hcond]
      by_cases hxy : x (Fin.last 0) = !y (Fin.last 0)
      · simp only [hxy, ↓reduceIte]
        have hx0 : x 0 = !y 0 := hxy
        have hcount :
            (Finset.univ.filter fun q : BitString 1 × BitString 1 =>
              q.1 0 = x 0 ∧ (!q.1 0) = y 0).card = 2 := by
          have : (Finset.univ.filter fun q : BitString 1 × BitString 1 =>
              q.1 0 = x 0 ∧ (!q.1 0) = y 0) =
            Finset.univ.image (fun b : Bool => ((fun _ : Fin 1 => x 0), (fun _ : Fin 1 => b))) := by
            ext ⟨a, b⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
              Prod.mk.injEq, funext_iff, Fin.forall_fin_one]
            constructor
            · rintro ⟨ha, _⟩; exact ⟨b 0, ha.symm, rfl⟩
            · rintro ⟨c, ha, _⟩
              refine ⟨ha.symm, ?_⟩
              simp [← ha, hx0]
          rw [this, Finset.card_image_of_injective]
          · simp
          · intro b₁ b₂ h
            have := congrFun (congrArg Prod.snd h) 0
            simpa using this
        rw [← Finset.sum_filter, Finset.sum_const, hcount, nsmul_eq_mul, Nat.cast_ofNat]
        rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num, ENNReal.mul_inv (Or.inl two_ne_zero)
          (Or.inl ENNReal.ofNat_ne_top), ← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero
          ENNReal.ofNat_ne_top, one_mul]
      · simp only [hxy, ↓reduceIte]
        refine Finset.sum_eq_zero fun q _ => ?_
        simp only [ite_eq_right_iff]
        rintro ⟨h1, h2⟩
        exfalso
        apply hxy
        change x 0 = !y 0
        rw [← h1, ← h2, Bool.not_not]
    rw [hsum]
    norm_num
  | succ m ih =>
    rw [greaterThanDistExplicit, uniform_fin_succ_eq_bernoulli m, PMF.bind_bind,
      greaterThanDistSucc]
    refine congrArg (PMF.bind _) (funext fun isTop => ?_)
    cases isTop
    · -- `isTop = false`: `k = Fin.castSucc j`, MSB agrees
      simp only [Bool.false_eq_true, ↓reduceIte, PMF.bind_map, ← ih, greaterThanDistExplicit]
      have hrhs :
          ((PMF.uniformOfFintype Bool).bind fun z =>
            ((PMF.uniformOfFintype (Fin (m + 1))).bind fun k =>
              (PMF.uniformOfFintype (BitString (m + 1) × BitString (m + 1))).map fun q =>
                (fun i : Fin (m + 1) => if k.val < i.val then q.1 i
                  else if i = k then q.1 k else q.1 i,
                 fun i : Fin (m + 1) => if k.val < i.val then q.1 i
                  else if i = k then !q.1 k else q.2 i)).map
              fun q => (Fin.snoc (α := fun _ => Bool) q.1 z,
                        Fin.snoc (α := fun _ => Bool) q.2 z)) =
          (PMF.uniformOfFintype (Fin (m + 1))).bind fun j =>
            (PMF.uniformOfFintype Bool).bind fun z =>
              ((PMF.uniformOfFintype (BitString (m + 1) × BitString (m + 1))).map fun q =>
                (fun i : Fin (m + 1) => if j.val < i.val then q.1 i
                  else if i = j then q.1 j else q.1 i,
                 fun i : Fin (m + 1) => if j.val < i.val then q.1 i
                  else if i = j then !q.1 j else q.2 i)).map
                fun q => (Fin.snoc (α := fun _ => Bool) q.1 z,
                          Fin.snoc (α := fun _ => Bool) q.2 z) := by
        simp_rw [PMF.map_bind]
        exact PMF.bind_comm _ _ _
      rw [hrhs]
      have hsplit : PMF.uniformOfFintype (BitString (m + 2) × BitString (m + 2)) =
          (PMF.uniformOfFintype ((Bool × Bool) × (BitString (m + 1) × BitString (m + 1)))).map
            fun ⟨⟨a, b⟩, ⟨u, v⟩⟩ =>
              (Fin.snoc (α := fun _ => Bool) u a, Fin.snoc (α := fun _ => Bool) v b) := by
        let e : (Bool × Bool) × (BitString (m + 1) × BitString (m + 1)) ≃
            BitString (m + 2) × BitString (m + 2) :=
          { toFun := fun ⟨⟨a, b⟩, ⟨u, v⟩⟩ =>
              (Fin.snoc (α := fun _ => Bool) u a, Fin.snoc (α := fun _ => Bool) v b)
            invFun := fun ⟨x, y⟩ => ((x (Fin.last _), y (Fin.last _)), (Fin.init x, Fin.init y))
            left_inv := fun ⟨⟨a, b⟩, ⟨u, v⟩⟩ => by
              simp [Fin.snoc_last, Fin.init_snoc]
            right_inv := fun ⟨x, y⟩ => by
              simp [Fin.snoc_init_self] }
        exact (Cslib.Probability.PMF.uniformOfFintype_map_equiv e).symm
      refine congrArg (PMF.bind _) (funext fun j => ?_)
      dsimp only [Function.comp_apply]
      rw [hsplit, PMF.map_comp]
      have hprod :
          PMF.uniformOfFintype ((Bool × Bool) × (BitString (m + 1) × BitString (m + 1))) =
            (PMF.uniformOfFintype Bool).bind fun z =>
              (PMF.uniformOfFintype Bool).bind fun w =>
                (PMF.uniformOfFintype (BitString (m + 1) × BitString (m + 1))).map
                  fun q => ((z, w), q) := by
        ext ⟨⟨z, w⟩, q⟩
        simp only [PMF.uniformOfFintype_apply, PMF.bind_apply, PMF.map_apply, tsum_fintype,
          Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat]
        rw [Finset.sum_eq_single z _ (fun h => absurd (Finset.mem_univ _) h)]
        · rw [Finset.sum_eq_single w _ (fun h => absurd (Finset.mem_univ _) h)]
          · rw [Finset.sum_eq_single q _ (fun h => absurd (Finset.mem_univ _) h)]
            · simp only [↓reduceIte, mul_assoc]
              rw [← ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top),
                ← ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top)]
            · intro q' _ hq'; simp [hq'.symm]
          · intro w' _ hw'
            refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun q' _ => ?_)
            simp [hw'.symm]
        · intro z' _ hz'
          refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun w' _ => ?_)
          refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun q' _ => ?_)
          simp [hz'.symm]
      rw [hprod, PMF.map_bind]
      refine congrArg (PMF.bind _) (funext fun z => ?_)
      rw [PMF.map_bind]
      have hconst :
          (fun w : Bool =>
            ((PMF.uniformOfFintype (BitString (m + 1) × BitString (m + 1))).map
              fun q => ((z, w), q)).map
              ((fun q : BitString (m + 2) × BitString (m + 2) =>
                (fun i : Fin (m + 2) => if j.castSucc.val < i.val then q.1 i
                  else if i = j.castSucc then q.1 j.castSucc else q.1 i,
                 fun i : Fin (m + 2) => if j.castSucc.val < i.val then q.1 i
                  else if i = j.castSucc then !q.1 j.castSucc else q.2 i)) ∘
                fun t : (Bool × Bool) × (BitString (m + 1) × BitString (m + 1)) =>
                  (Fin.snoc (α := fun _ => Bool) t.2.1 t.1.1,
                   Fin.snoc (α := fun _ => Bool) t.2.2 t.1.2))) =
          fun _ : Bool =>
            ((PMF.uniformOfFintype (BitString (m + 1) × BitString (m + 1))).map fun q =>
              (fun i : Fin (m + 1) => if j.val < i.val then q.1 i
                else if i = j then q.1 j else q.1 i,
               fun i : Fin (m + 1) => if j.val < i.val then q.1 i
                else if i = j then !q.1 j else q.2 i)).map
              fun q => (Fin.snoc (α := fun _ => Bool) q.1 z,
                        Fin.snoc (α := fun _ => Bool) q.2 z) := by
        funext w
        rw [PMF.map_comp, PMF.map_comp]
        refine congrArg (fun f => PMF.map f _) (funext fun ⟨u, v⟩ => ?_)
        simp only [Function.comp_apply, Prod.mk.injEq]
        constructor <;> funext i <;> refine Fin.lastCases ?_ (fun i' => ?_) i
        · simp [Fin.snoc_last, j.isLt]
        · simp [Fin.snoc_castSucc, Fin.castSucc_inj]
        · simp [Fin.snoc_last, j.isLt]
        · simp [Fin.snoc_castSucc, Fin.castSucc_inj]
      rw [hconst, PMF.bind_const]
    · -- `isTop = true`: `k = Fin.last (m + 1)`, MSB differs
      simp only [↓reduceIte, PMF.pure_bind, gtDiffMSB]
      let e : (Bool × Bool) × (BitString (m + 1) × BitString (m + 1)) ≃
          BitString (m + 2) × BitString (m + 2) :=
        { toFun := fun ⟨⟨a, b⟩, ⟨u, v⟩⟩ =>
            (Fin.snoc (α := fun _ => Bool) u a, Fin.snoc (α := fun _ => Bool) v b)
          invFun := fun ⟨x, y⟩ => ((x (Fin.last _), y (Fin.last _)), (Fin.init x, Fin.init y))
          left_inv := fun ⟨⟨a, b⟩, ⟨u, v⟩⟩ => by simp [Fin.snoc_last, Fin.init_snoc]
          right_inv := fun ⟨x, y⟩ => by simp [Fin.snoc_init_self] }
      rw [← Cslib.Probability.PMF.uniformOfFintype_map_equiv e, PMF.map_comp]
      have hfactor :
          PMF.uniformOfFintype ((Bool × Bool) × (BitString (m + 1) × BitString (m + 1))) =
            (PMF.uniformOfFintype (Bool × BitString (m + 1) × BitString (m + 1))).bind
              fun ⟨w, u, v⟩ => (PMF.uniformOfFintype Bool).map fun w' => ((w, w'), (u, v)) := by
        ext ⟨⟨w, w'⟩, ⟨u, v⟩⟩
        simp only [PMF.uniformOfFintype_apply, PMF.bind_apply, PMF.map_apply, tsum_fintype,
          Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat]
        rw [Finset.sum_eq_single (w, u, v) _ (fun h => absurd (Finset.mem_univ _) h)]
        · rw [Finset.sum_eq_single w' _ (fun h => absurd (Finset.mem_univ _) h)]
          · simp only [↓reduceIte]
            rw [mul_comm _ (2 : ℝ≥0∞)⁻¹,
              ← ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top)]
            congr 1
            ring
          · intro b _ hb; simp [hb.symm]
        · rintro ⟨a, u', v'⟩ _ hne
          refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun b _ => ?_)
          have : ¬(((w, w'), (u, v)) = ((a, b), (u', v'))) := by
            intro h
            apply hne
            rcases Prod.mk.inj h with ⟨h1, h2⟩
            rcases Prod.mk.inj h1 with ⟨ha, _⟩
            rcases Prod.mk.inj h2 with ⟨hu, hv⟩
            simp [ha, hu, hv]
          simp [this]
      rw [hfactor, PMF.map_bind]
      change ((PMF.uniformOfFintype (Bool × BitString (m + 1) × BitString (m + 1))).bind _) =
        (PMF.uniformOfFintype (Bool × BitString (m + 1) × BitString (m + 1))).bind
          (fun t : Bool × BitString (m + 1) × BitString (m + 1) =>
            PMF.pure (Fin.snoc (α := fun _ => Bool) t.2.1 t.1,
              Fin.snoc (α := fun _ => Bool) t.2.2 !t.1))
      refine congrArg (PMF.bind _) (funext fun ⟨w, u, v⟩ => ?_)
      rw [PMF.map_comp]
      have hconst :
          ((fun q : BitString (m + 2) × BitString (m + 2) =>
              (fun i : Fin (m + 2) => if (Fin.last (m + 1)).val < i.val then q.1 i
                else if i = Fin.last (m + 1) then q.1 (Fin.last (m + 1)) else q.1 i,
               fun i : Fin (m + 2) => if (Fin.last (m + 1)).val < i.val then q.1 i
                else if i = Fin.last (m + 1) then !q.1 (Fin.last (m + 1)) else q.2 i)) ∘
            e) ∘ (fun w' : Bool => ((w, w'), (u, v))) =
          Function.const Bool
            (Fin.snoc (α := fun _ => Bool) u w, Fin.snoc (α := fun _ => Bool) v !w) := by
        funext w'
        simp only [Function.comp_apply, Function.const_apply, e, Equiv.coe_fn_mk, Prod.mk.injEq]
        constructor <;> funext i <;> refine Fin.lastCases ?_ (fun i' => ?_) i
        · simp [Fin.snoc_last]
        · have hlt : ¬(m + 1 < i'.val) := by omega
          have hne : i'.castSucc ≠ Fin.last (m + 1) := Fin.castSucc_ne_last i'
          simp [Fin.snoc_castSucc, hlt, hne]
        · simp [Fin.snoc_last]
        · have hlt : ¬(m + 1 < i'.val) := by omega
          have hne : i'.castSucc ≠ Fin.last (m + 1) := Fin.castSucc_ne_last i'
          simp [Fin.snoc_castSucc, hlt, hne]
      rw [hconst, PMF.map_const]

/-! ### Elementary algebraic inequalities for the Greater-Than induction -/

/-- `√(pq) + √((1 - p)(1 - q)) ≤ 1 - (p - q)^2 / 4` for `p, q ∈ [0, 1]`. -/
private theorem sqrt_mul_add_sqrt_one_sub_le {p q : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Real.sqrt (p * q) + Real.sqrt ((1 - p) * (1 - q)) ≤ 1 - (p - q) ^ 2 / 4 := by
  have h1 : Real.sqrt (p * q) = Real.sqrt p * Real.sqrt q := Real.sqrt_mul hp0 q
  have h2 : Real.sqrt ((1 - p) * (1 - q)) = Real.sqrt (1 - p) * Real.sqrt (1 - q) :=
    Real.sqrt_mul (by linarith) (1 - q)
  have hsp : 0 ≤ Real.sqrt p := Real.sqrt_nonneg p
  have hsq : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
  have hsp1 : Real.sqrt p ≤ 1 := Real.sqrt_le_one.mpr hp1
  have hsq1 : Real.sqrt q ≤ 1 := Real.sqrt_le_one.mpr hq1
  have hs1p : 0 ≤ Real.sqrt (1 - p) := Real.sqrt_nonneg _
  have hs1q : 0 ≤ Real.sqrt (1 - q) := Real.sqrt_nonneg _
  have hs1p1 : Real.sqrt (1 - p) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  have hs1q1 : Real.sqrt (1 - q) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  have hsp_sq : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp0
  have hsq_sq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq0
  have hs1p_sq : Real.sqrt (1 - p) ^ 2 = 1 - p := Real.sq_sqrt (by linarith)
  have hs1q_sq : Real.sqrt (1 - q) ^ 2 = 1 - q := Real.sq_sqrt (by linarith)
  have hdiff1 : (p - q) ^ 2 ≤ 4 * (Real.sqrt p - Real.sqrt q) ^ 2 := by
    have hfac : p - q = (Real.sqrt p - Real.sqrt q) * (Real.sqrt p + Real.sqrt q) := by
      nlinarith
    rw [hfac, mul_pow]
    nlinarith [sq_nonneg (Real.sqrt p - Real.sqrt q)]
  have hdiff2 : (p - q) ^ 2 ≤ 4 * (Real.sqrt (1 - p) - Real.sqrt (1 - q)) ^ 2 := by
    have hfac : q - p = (Real.sqrt (1 - p) - Real.sqrt (1 - q)) *
        (Real.sqrt (1 - p) + Real.sqrt (1 - q)) := by
      nlinarith
    have hsq_eq : (p - q) ^ 2 = (q - p) ^ 2 := by ring
    rw [hsq_eq, hfac, mul_pow]
    nlinarith [sq_nonneg (Real.sqrt (1 - p) - Real.sqrt (1 - q))]
  rw [h1, h2]
  nlinarith

/-- For `n ≥ 2`, `√((n - 1) / n) < 1 - 1 / (2 * n)`. -/
private theorem sqrt_pred_div_lt {n : ℕ} (hn : 2 ≤ n) :
    Real.sqrt (((n - 1 : ℕ) : ℝ) / (n : ℝ)) < 1 - 1 / (2 * (n : ℝ)) := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by exact_mod_cast Nat.cast_sub (by omega : 1 ≤ n)
  rw [hcast]
  have hrhs : 0 < 1 - 1 / (2 * (n : ℝ)) := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have : 1 / (2 * (n : ℝ)) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
    linarith
  rw [Real.sqrt_lt' hrhs]
  have hsq : (1 - 1 / (2 * (n : ℝ))) ^ 2 =
      ((n : ℝ) - 1) / (n : ℝ) + 1 / (4 * (n : ℝ) ^ 2) := by
    field_simp [hn_pos.ne']
    ring
  rw [hsq]
  linarith [show (0 : ℝ) < 1 / (4 * (n : ℝ) ^ 2) by positivity]

/-- Core algebraic step of the rectangle discrepancy induction, proved simultaneously
for both signs via `|p - q|`, with strict inequality whenever `0 < s` and `0 < t`. -/
private theorem gt_induction_step_lt {n : ℕ} (hn : 2 ≤ n) {s t p q : ℝ}
    (hs0 : 0 < s) (hs1 : s ≤ 1) (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ((n - 1 : ℕ) : ℝ) / (2 * (n : ℝ)) *
        (20 * Real.sqrt (2 * p * s * (2 * q * t)) / Real.sqrt ((n - 1 : ℕ) : ℝ)) +
      ((n - 1 : ℕ) : ℝ) / (2 * (n : ℝ)) *
        (20 * Real.sqrt (2 * (1 - p) * s * (2 * (1 - q) * t)) / Real.sqrt ((n - 1 : ℕ) : ℝ)) +
      (2 / (n : ℝ)) * |p - q| * s * t <
    20 * Real.sqrt (s * t) / Real.sqrt (n : ℝ) := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hm_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - 1)
  have hst_pos : 0 < s * t := mul_pos hs0 ht0
  have hst_le : s * t ≤ 1 := by nlinarith
  have hsqrt_st_pos : 0 < Real.sqrt (s * t) := Real.sqrt_pos.mpr hst_pos
  have hsqrt_n_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
  have hsqrt_m_pos : 0 < Real.sqrt ((n - 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr hm_pos
  have hterm1 :
      ((n - 1 : ℕ) : ℝ) / (2 * (n : ℝ)) *
        (20 * Real.sqrt (2 * p * s * (2 * q * t)) / Real.sqrt ((n - 1 : ℕ) : ℝ)) =
      20 * Real.sqrt (s * t) / Real.sqrt (n : ℝ) *
        (Real.sqrt (((n - 1 : ℕ) : ℝ) / (n : ℝ)) * Real.sqrt (p * q)) := by
    have h1 : 2 * p * s * (2 * q * t) = 4 * (p * q) * (s * t) := by ring
    rw [h1, Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num),
      show Real.sqrt 4 = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)],
      Real.sqrt_div hm_pos.le]
    have hmsq : Real.sqrt ((n - 1 : ℕ) : ℝ) ^ 2 = ((n - 1 : ℕ) : ℝ) := Real.sq_sqrt hm_pos.le
    have hnsq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hn_pos.le
    field_simp [hn_pos.ne', hsqrt_m_pos.ne', hsqrt_n_pos.ne']
    rw [hmsq, hnsq]
    ring
  have hterm2 :
      ((n - 1 : ℕ) : ℝ) / (2 * (n : ℝ)) *
        (20 * Real.sqrt (2 * (1 - p) * s * (2 * (1 - q) * t)) / Real.sqrt ((n - 1 : ℕ) : ℝ)) =
      20 * Real.sqrt (s * t) / Real.sqrt (n : ℝ) *
        (Real.sqrt (((n - 1 : ℕ) : ℝ) / (n : ℝ)) * Real.sqrt ((1 - p) * (1 - q))) := by
    have h1 : 2 * (1 - p) * s * (2 * (1 - q) * t) = 4 * ((1 - p) * (1 - q)) * (s * t) := by ring
    have h1pq : 0 ≤ (1 - p) * (1 - q) := mul_nonneg (by linarith) (by linarith)
    rw [h1, Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num),
      show Real.sqrt 4 = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)],
      Real.sqrt_div hm_pos.le]
    have hmsq : Real.sqrt ((n - 1 : ℕ) : ℝ) ^ 2 = ((n - 1 : ℕ) : ℝ) := Real.sq_sqrt hm_pos.le
    have hnsq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hn_pos.le
    field_simp [hn_pos.ne', hsqrt_m_pos.ne', hsqrt_n_pos.ne']
    rw [hmsq, hnsq]
    ring
  have hst_le_sqrt : s * t ≤ Real.sqrt (s * t) := by
    have hsq : (s * t) ^ 2 ≤ s * t := by nlinarith
    exact Real.le_sqrt_of_sq_le hsq
  have hterm3 :
      (2 / (n : ℝ)) * |p - q| * s * t ≤
        20 * Real.sqrt (s * t) / Real.sqrt (n : ℝ) * (|p - q| / (10 * Real.sqrt (n : ℝ))) := by
    have hrew : (2 / (n : ℝ)) * |p - q| * s * t = (2 / (n : ℝ)) * |p - q| * (s * t) := by ring
    rw [hrew]
    have hle := mul_le_mul_of_nonneg_left hst_le_sqrt
      (mul_nonneg (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hn_pos.le) (abs_nonneg (p - q)))
    refine hle.trans_eq ?_
    have hnsq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hn_pos.le
    field_simp [hn_pos.ne', hsqrt_n_pos.ne']
    rw [hnsq]
    ring
  rw [hterm1, hterm2]
  set C := 20 * Real.sqrt (s * t) / Real.sqrt (n : ℝ)
  have hC_pos : 0 < C := by positivity
  set S := Real.sqrt (p * q) + Real.sqrt ((1 - p) * (1 - q))
  have hS_nonneg : 0 ≤ S := add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hS_le : S ≤ 1 - (p - q) ^ 2 / 4 := sqrt_mul_add_sqrt_one_sub_le hp0 hp1 hq0 hq1
  have hroot_lt : Real.sqrt (((n - 1 : ℕ) : ℝ) / (n : ℝ)) < 1 - 1 / (2 * (n : ℝ)) :=
    sqrt_pred_div_lt hn
  -- Compare the bracket `√((n-1)/n) * S + |p - q| / (10 √n)` strictly against `1`.
  have hbracket_lt :
      Real.sqrt (((n - 1 : ℕ) : ℝ) / (n : ℝ)) * S + |p - q| / (10 * Real.sqrt (n : ℝ)) < 1 := by
    set d := |p - q|
    have hd0 : 0 ≤ d := abs_nonneg _
    have hd1 : d ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hd_sq : d ^ 2 = (p - q) ^ 2 := sq_abs (p - q)
    have hn2_real : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hA_le : 1 / (2 * (n : ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have hB_le : d ^ 2 / 4 ≤ 1 := by nlinarith
    have hprod_le : (1 - 1 / (2 * (n : ℝ))) * (1 - d ^ 2 / 4) ≤
        1 - 1 / (4 * (n : ℝ)) - d ^ 2 / 8 := by
      have hab : (1 / (2 * (n : ℝ))) * (d ^ 2 / 4) ≤
          (1 / (2 * (n : ℝ)) + d ^ 2 / 4) / 2 := by
        have h1 : (1 / (2 * (n : ℝ))) * (d ^ 2 / 4) ≤ 1 / (2 * (n : ℝ)) :=
          mul_le_of_le_one_right (by positivity) hB_le
        have h2 : (1 / (2 * (n : ℝ))) * (d ^ 2 / 4) ≤ d ^ 2 / 4 :=
          mul_le_of_le_one_left (by positivity) hA_le
        linarith
      have hexp : (1 - 1 / (2 * (n : ℝ))) * (1 - d ^ 2 / 4) =
          1 - 1 / (2 * (n : ℝ)) - d ^ 2 / 4 + (1 / (2 * (n : ℝ))) * (d ^ 2 / 4) := by ring
      have hhalf : (1 / (2 * (n : ℝ))) / 2 = 1 / (4 * (n : ℝ)) := by ring
      linarith
    have hamgm : d / (Real.sqrt 8 * Real.sqrt (n : ℝ)) ≤ 1 / (4 * (n : ℝ)) + d ^ 2 / 8 := by
      have hsq : 0 ≤ (1 / (2 * Real.sqrt (n : ℝ)) - d / Real.sqrt 8) ^ 2 := sq_nonneg _
      have h8sq : Real.sqrt 8 ^ 2 = 8 := Real.sq_sqrt (by norm_num)
      have hnsq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hn_pos.le
      have h8pos : 0 < Real.sqrt 8 := Real.sqrt_pos.mpr (by norm_num)
      have hexp :
          (1 / (2 * Real.sqrt (n : ℝ)) - d / Real.sqrt 8) ^ 2 =
            1 / (4 * (n : ℝ)) + d ^ 2 / 8 - d / (Real.sqrt 8 * Real.sqrt (n : ℝ)) := by
        rw [sub_sq, div_pow, div_pow, one_pow, mul_pow, hnsq, h8sq]
        have hmid :
            2 * (1 / (2 * Real.sqrt (n : ℝ))) * (d / Real.sqrt 8) =
              d / (Real.sqrt 8 * Real.sqrt (n : ℝ)) := by
          field_simp [hsqrt_n_pos.ne', h8pos.ne']
        linarith
      linarith
    have h8_lt_10 : Real.sqrt 8 < 10 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    have hcoeff : d / (10 * Real.sqrt (n : ℝ)) ≤ d / (Real.sqrt 8 * Real.sqrt (n : ℝ)) := by
      refine div_le_div_of_nonneg_left hd0 (by positivity) ?_
      exact mul_le_mul_of_nonneg_right h8_lt_10.le hsqrt_n_pos.le
    rcases eq_or_lt_of_le hS_nonneg with hS0 | hS_pos
    · rw [← hS0, mul_zero, zero_add]
      have h10 : (1 : ℝ) < 10 * Real.sqrt (n : ℝ) := by
        have : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
          rw [Real.le_sqrt (by norm_num) hn_pos.le]; norm_cast; omega
        linarith
      exact (div_lt_one (by positivity)).mpr (lt_of_le_of_lt hd1 h10)
    · have h1 : Real.sqrt (((n - 1 : ℕ) : ℝ) / (n : ℝ)) * S < (1 - 1 / (2 * (n : ℝ))) * S :=
        mul_lt_mul_of_pos_right hroot_lt hS_pos
      have h2 : (1 - 1 / (2 * (n : ℝ))) * S ≤ (1 - 1 / (2 * (n : ℝ))) * (1 - d ^ 2 / 4) := by
        rw [hd_sq]
        exact mul_le_mul_of_nonneg_left hS_le (by linarith)
      linarith
  have hcombine :
      C * (Real.sqrt (((n - 1 : ℕ) : ℝ) / (n : ℝ)) * Real.sqrt (p * q)) +
        C * (Real.sqrt (((n - 1 : ℕ) : ℝ) / (n : ℝ)) * Real.sqrt ((1 - p) * (1 - q))) +
        (2 / (n : ℝ)) * |p - q| * s * t ≤
      C * (Real.sqrt (((n - 1 : ℕ) : ℝ) / (n : ℝ)) * S + |p - q| / (10 * Real.sqrt (n : ℝ))) := by
    have : C * (Real.sqrt (((n - 1 : ℕ) : ℝ) / (n : ℝ)) * Real.sqrt (p * q)) +
        C * (Real.sqrt (((n - 1 : ℕ) : ℝ) / (n : ℝ)) * Real.sqrt ((1 - p) * (1 - q))) =
        C * (Real.sqrt (((n - 1 : ℕ) : ℝ) / (n : ℝ)) * S) := by
      simp only [S]; ring
    linarith [hterm3]
  have hstrict :
      C * (Real.sqrt (((n - 1 : ℕ) : ℝ) / (n : ℝ)) * S + |p - q| / (10 * Real.sqrt (n : ℝ))) <
        C * 1 :=
    mul_lt_mul_of_pos_left hbracket_lt hC_pos
  linarith

/-! ### Rectangle discrepancy induction for `GT_n` -/

/-- Injectivity of `Fin.snoc · b` on any subset of `BitString m`. -/
private theorem snoc_injOn (m : ℕ) (b : Bool) (S : Finset (BitString (m + 1))) :
    Set.InjOn (fun u : BitString m => Fin.snoc (α := fun _ => Bool) u b)
      ((fun u : BitString m => Fin.snoc (α := fun _ => Bool) u b) ⁻¹'
        (S : Set (BitString (m + 1)))) := by
  intro u₁ _ u₂ _ h
  simpa [Fin.init_snoc] using congrArg Fin.init h

/-- Helper: splitting a sum over a `Finset (BitString (m + 1))` by the most significant bit
`Fin.last m`. -/
private theorem sum_bitString_succ_split {m : ℕ} (S : Finset (BitString (m + 1)))
    (g : BitString (m + 1) → ℝ) :
    ∑ x ∈ S, g x =
      (∑ x' ∈ S.preimage (fun u => Fin.snoc (α := fun _ => Bool) u false)
          (snoc_injOn m false S), g (Fin.snoc (α := fun _ => Bool) x' false)) +
      (∑ x' ∈ S.preimage (fun u => Fin.snoc (α := fun _ => Bool) u true)
          (snoc_injOn m true S), g (Fin.snoc (α := fun _ => Bool) x' true)) := by
  classical
  have hdisj : Disjoint (S.filter fun x => x (Fin.last m) = false)
      (S.filter fun x => x (Fin.last m) = true) := by
    rw [Finset.disjoint_left]
    intro x h0 h1
    simp only [Finset.mem_filter] at h0 h1
    exact Bool.false_ne_true (h0.2.symm.trans h1.2)
  have hunion : S = (S.filter fun x => x (Fin.last m) = false) ∪
      (S.filter fun x => x (Fin.last m) = true) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter]
    cases hx : x (Fin.last m) <;> simp
  conv_lhs => rw [hunion, Finset.sum_union hdisj]
  congr 1
  · refine Finset.sum_bij (fun x _ => Fin.init x) (fun x hx => ?_) ?_ ?_ ?_
    · simp only [Finset.mem_filter] at hx
      rw [Finset.mem_preimage]
      rw [← hx.2, Fin.snoc_init_self]
      exact hx.1
    · intro x₁ hx₁ x₂ hx₂ hinit
      simp only [Finset.mem_filter] at hx₁ hx₂
      rw [← Fin.snoc_init_self x₁, ← Fin.snoc_init_self x₂, hinit, hx₁.2, hx₂.2]
    · intro u hu
      rw [Finset.mem_preimage] at hu
      refine ⟨Fin.snoc (α := fun _ => Bool) u false,
        Finset.mem_filter.mpr ⟨hu, Fin.snoc_last _ _⟩, Fin.init_snoc _ _⟩
    · intro x hx
      simp only [Finset.mem_filter] at hx
      rw [← hx.2, Fin.snoc_init_self]
  · refine Finset.sum_bij (fun x _ => Fin.init x) (fun x hx => ?_) ?_ ?_ ?_
    · simp only [Finset.mem_filter] at hx
      rw [Finset.mem_preimage]
      rw [← hx.2, Fin.snoc_init_self]
      exact hx.1
    · intro x₁ hx₁ x₂ hx₂ hinit
      simp only [Finset.mem_filter] at hx₁ hx₂
      rw [← Fin.snoc_init_self x₁, ← Fin.snoc_init_self x₂, hinit, hx₁.2, hx₂.2]
    · intro u hu
      rw [Finset.mem_preimage] at hu
      refine ⟨Fin.snoc (α := fun _ => Bool) u true,
        Finset.mem_filter.mpr ⟨hu, Fin.snoc_last _ _⟩, Fin.init_snoc _ _⟩
    · intro x hx
      simp only [Finset.mem_filter] at hx
      rw [← hx.2, Fin.snoc_init_self]

/-- Nonempty strict rectangle discrepancy bound: for every `m : ℕ` and
nonempty rectangle `S × T` in `BitString (m + 1) × BitString (m + 1)`, the rectangle
discrepancy of `GT_{m+1}` under `μ_{m+1}` is strictly less than
`20 * √((|S|/2^(m+1)) * (|T|/2^(m+1))) / √(m + 1)`. -/
theorem discrepancy_greaterThanSucc_rect_lt (m : ℕ) (S T : Finset (BitString (m + 1)))
    (hS : S.Nonempty) (hT : T.Nonempty) :
    |∑ x ∈ S, ∑ y ∈ T, (greaterThanDistSucc m (x, y)).toReal *
        signVal (greaterThanBits (m + 1) x y)| <
      20 * Real.sqrt ((S.card / (2 ^ (m + 1) : ℝ)) * (T.card / (2 ^ (m + 1) : ℝ))) /
        Real.sqrt ((m + 1 : ℕ) : ℝ) := by
  induction m with
  | zero =>
    have hS1 : (1 : ℝ) ≤ S.card := by exact_mod_cast hS.card_pos
    have hT1 : (1 : ℝ) ≤ T.card := by exact_mod_cast hT.card_pos
    have hprod_ge : (1 / 4 : ℝ) ≤ (S.card / (2 ^ 1 : ℝ)) * (T.card / (2 ^ 1 : ℝ)) := by
      nlinarith
    have hsqrt_ge : (1 / 2 : ℝ) ≤
        Real.sqrt ((S.card / (2 ^ 1 : ℝ)) * (T.card / (2 ^ 1 : ℝ))) := by
      rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
        rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hprod_ge
    have hsum_le :
        |∑ x ∈ S, ∑ y ∈ T, (greaterThanDistSucc 0 (x, y)).toReal *
            signVal (greaterThanBits 1 x y)| ≤ 1 := by
      calc
        |∑ x ∈ S, ∑ y ∈ T, (greaterThanDistSucc 0 (x, y)).toReal *
            signVal (greaterThanBits 1 x y)|
          ≤ ∑ x ∈ S, |∑ y ∈ T, (greaterThanDistSucc 0 (x, y)).toReal *
              signVal (greaterThanBits 1 x y)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ x ∈ S, ∑ y ∈ T, |(greaterThanDistSucc 0 (x, y)).toReal *
              signVal (greaterThanBits 1 x y)| :=
            Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _
        _ = ∑ x ∈ S, ∑ y ∈ T, (greaterThanDistSucc 0 (x, y)).toReal := by
            refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
            rw [abs_mul, abs_signVal, mul_one, abs_of_nonneg ENNReal.toReal_nonneg]
        _ ≤ ∑ x : BitString 1, ∑ y : BitString 1, (greaterThanDistSucc 0 (x, y)).toReal := by
            refine (Finset.sum_le_sum fun x _ =>
              Finset.sum_le_univ_sum_of_nonneg fun _ => ENNReal.toReal_nonneg).trans ?_
            exact Finset.sum_le_univ_sum_of_nonneg fun _ =>
              Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
        _ = 1 := by
            rw [← Fintype.sum_prod_type', Cslib.Probability.PMF.sum_toReal]
    simp only [zero_add, Nat.cast_one, Real.sqrt_one, div_one]
    linarith
  | succ m ih =>
    let S₀ : Finset (BitString (m + 1)) :=
      S.preimage (fun u => Fin.snoc (α := fun _ => Bool) u false) (snoc_injOn (m + 1) false S)
    let S₁ : Finset (BitString (m + 1)) :=
      S.preimage (fun u => Fin.snoc (α := fun _ => Bool) u true) (snoc_injOn (m + 1) true S)
    let T₀ : Finset (BitString (m + 1)) :=
      T.preimage (fun u => Fin.snoc (α := fun _ => Bool) u false) (snoc_injOn (m + 1) false T)
    let T₁ : Finset (BitString (m + 1)) :=
      T.preimage (fun u => Fin.snoc (α := fun _ => Bool) u true) (snoc_injOn (m + 1) true T)
    have hScard : S₀.card + S₁.card = S.card := by
      have := sum_bitString_succ_split S (fun _ => (1 : ℝ))
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at this
      exact_mod_cast this.symm
    have hTcard : T₀.card + T₁.card = T.card := by
      have := sum_bitString_succ_split T (fun _ => (1 : ℝ))
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at this
      exact_mod_cast this.symm
    let n : ℕ := m + 2
    have hn2 : 2 ≤ n := by omega
    have hSpos : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
    have hTpos : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
    set s : ℝ := S.card / (2 ^ n : ℝ)
    set t : ℝ := T.card / (2 ^ n : ℝ)
    set p : ℝ := S₀.card / (S.card : ℝ)
    set q : ℝ := T₀.card / (T.card : ℝ)
    have hs0 : 0 < s := by positivity
    have ht0 : 0 < t := by positivity
    have hs1 : s ≤ 1 := by
      rw [div_le_one (by positivity)]
      have := Finset.card_le_univ S
      rw [BitString.card] at this
      exact_mod_cast this
    have ht1 : t ≤ 1 := by
      rw [div_le_one (by positivity)]
      have := Finset.card_le_univ T
      rw [BitString.card] at this
      exact_mod_cast this
    have hp0 : 0 ≤ p := by positivity
    have hp1 : p ≤ 1 := (div_le_one hSpos).mpr (by exact_mod_cast (by omega : S₀.card ≤ S.card))
    have hq0 : 0 ≤ q := by positivity
    have hq1 : q ≤ 1 := (div_le_one hTpos).mpr (by exact_mod_cast (by omega : T₀.card ≤ T.card))
    have hs₀_eq : (S₀.card : ℝ) / (2 ^ (m + 1) : ℝ) = 2 * p * s := by
      simp only [p, s, n, pow_succ]
      field_simp [hSpos.ne']
    have hs₁_eq : (S₁.card : ℝ) / (2 ^ (m + 1) : ℝ) = 2 * (1 - p) * s := by
      have h1 : (S₁.card : ℝ) = (S.card : ℝ) - (S₀.card : ℝ) := by
        have : (S₀.card : ℝ) + (S₁.card : ℝ) = (S.card : ℝ) := by exact_mod_cast hScard
        linarith
      rw [h1]
      simp only [p, s, n, pow_succ]
      field_simp [hSpos.ne']
    have ht₀_eq : (T₀.card : ℝ) / (2 ^ (m + 1) : ℝ) = 2 * q * t := by
      simp only [q, t, n, pow_succ]
      field_simp [hTpos.ne']
    have ht₁_eq : (T₁.card : ℝ) / (2 ^ (m + 1) : ℝ) = 2 * (1 - q) * t := by
      have h1 : (T₁.card : ℝ) = (T.card : ℝ) - (T₀.card : ℝ) := by
        have : (T₀.card : ℝ) + (T₁.card : ℝ) = (T.card : ℝ) := by exact_mod_cast hTcard
        linarith
      rw [h1]
      simp only [q, t, n, pow_succ]
      field_simp [hTpos.ne']
    -- Split the rectangle sum into the 4 quadrant rectangles `S₀×T₀`, `S₁×T₁`, `S₀×T₁`, `S₁×T₀`.
    have hsplit :
        (∑ x ∈ S, ∑ y ∈ T, (greaterThanDistSucc (m + 1) (x, y)).toReal *
            signVal (greaterThanBits (m + 2) x y)) =
          ((m + 1 : ℕ) : ℝ) / (2 * (n : ℝ)) *
            (∑ x' ∈ S₀, ∑ y' ∈ T₀, (greaterThanDistSucc m (x', y')).toReal *
              signVal (greaterThanBits (m + 1) x' y')) +
          ((m + 1 : ℕ) : ℝ) / (2 * (n : ℝ)) *
            (∑ x' ∈ S₁, ∑ y' ∈ T₁, (greaterThanDistSucc m (x', y')).toReal *
              signVal (greaterThanBits (m + 1) x' y')) +
          (2 / (n : ℝ)) * (p - q) * s * t := by
      rw [sum_bitString_succ_split S]
      simp_rw [sum_bitString_succ_split T, Finset.sum_add_distrib]
      have h00 :
          (∑ x' ∈ S₀, ∑ y' ∈ T₀,
            (greaterThanDistSucc (m + 1) (Fin.snoc x' false, Fin.snoc y' false)).toReal *
              signVal (greaterThanBits (m + 2) (Fin.snoc x' false) (Fin.snoc y' false))) =
          ((m + 1 : ℕ) : ℝ) / (2 * (n : ℝ)) *
            (∑ x' ∈ S₀, ∑ y' ∈ T₀, (greaterThanDistSucc m (x', y')).toReal *
              signVal (greaterThanBits (m + 1) x' y')) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x' _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y' _ => ?_
        rw [greaterThanDistSucc_succ_apply_snoc, greaterThanBits_snoc]
        simp only [↓reduceIte, ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_natCast]
        push_cast [n]
        ring
      have h11 :
          (∑ x' ∈ S₁, ∑ y' ∈ T₁,
            (greaterThanDistSucc (m + 1)
                (Fin.snoc (α := fun _ => Bool) x' true,
                 Fin.snoc (α := fun _ => Bool) y' true)).toReal *
              signVal (greaterThanBits (m + 2)
                (Fin.snoc (α := fun _ => Bool) x' true)
                (Fin.snoc (α := fun _ => Bool) y' true))) =
          ((m + 1 : ℕ) : ℝ) / (2 * (n : ℝ)) *
            (∑ x' ∈ S₁, ∑ y' ∈ T₁, (greaterThanDistSucc m (x', y')).toReal *
              signVal (greaterThanBits (m + 1) x' y')) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x' _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y' _ => ?_
        rw [greaterThanDistSucc_succ_apply_snoc, greaterThanBits_snoc]
        simp only [↓reduceIte, ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_natCast]
        push_cast [n]
        ring
      have h01 :
          (∑ x' ∈ S₀, ∑ y' ∈ T₁,
            (greaterThanDistSucc (m + 1)
                (Fin.snoc (α := fun _ => Bool) x' false,
                 Fin.snoc (α := fun _ => Bool) y' true)).toReal *
              signVal (greaterThanBits (m + 2)
                (Fin.snoc (α := fun _ => Bool) x' false)
                (Fin.snoc (α := fun _ => Bool) y' true))) =
          (2 / (n : ℝ)) * p * (1 - q) * s * t := by
        have hconst : ∀ x' ∈ S₀, ∀ y' ∈ T₁,
            (greaterThanDistSucc (m + 1)
                (Fin.snoc (α := fun _ => Bool) x' false,
                 Fin.snoc (α := fun _ => Bool) y' true)).toReal *
              signVal (greaterThanBits (m + 2)
                (Fin.snoc (α := fun _ => Bool) x' false)
                (Fin.snoc (α := fun _ => Bool) y' true)) =
            (2 * (n : ℝ) * (2 ^ (m + 1) : ℝ) * (2 ^ (m + 1) : ℝ))⁻¹ := by
          intro x' _ y' _
          rw [greaterThanDistSucc_succ_apply_snoc, greaterThanBits_snoc]
          simp only [Bool.false_eq_true, ↓reduceIte, signVal_false, mul_one, ENNReal.toReal_inv,
            ENNReal.toReal_natCast]
          push_cast [n]
          rfl
        rw [Finset.sum_congr rfl fun x' hx' =>
              Finset.sum_congr rfl fun y' hy' => hconst x' hx' y' hy']
        simp only [Finset.sum_const, nsmul_eq_mul]
        have h1 : (S₀.card : ℝ) = 2 * p * s * (2 ^ (m + 1) : ℝ) := by
          rw [← hs₀_eq, div_mul_cancel₀ _ (by positivity)]
        have h2 : (T₁.card : ℝ) = 2 * (1 - q) * t * (2 ^ (m + 1) : ℝ) := by
          rw [← ht₁_eq, div_mul_cancel₀ _ (by positivity)]
        rw [h1, h2]
        have hn_ne : (n : ℝ) ≠ 0 := by positivity
        field_simp [hn_ne]
      have h10 :
          (∑ x' ∈ S₁, ∑ y' ∈ T₀,
            (greaterThanDistSucc (m + 1)
                (Fin.snoc (α := fun _ => Bool) x' true,
                 Fin.snoc (α := fun _ => Bool) y' false)).toReal *
              signVal (greaterThanBits (m + 2)
                (Fin.snoc (α := fun _ => Bool) x' true)
                (Fin.snoc (α := fun _ => Bool) y' false))) =
          -((2 / (n : ℝ)) * (1 - p) * q * s * t) := by
        have hconst : ∀ x' ∈ S₁, ∀ y' ∈ T₀,
            (greaterThanDistSucc (m + 1)
                (Fin.snoc (α := fun _ => Bool) x' true,
                 Fin.snoc (α := fun _ => Bool) y' false)).toReal *
              signVal (greaterThanBits (m + 2)
                (Fin.snoc (α := fun _ => Bool) x' true)
                (Fin.snoc (α := fun _ => Bool) y' false)) =
            -((2 * (n : ℝ) * (2 ^ (m + 1) : ℝ) * (2 ^ (m + 1) : ℝ))⁻¹) := by
          intro x' _ y' _
          rw [greaterThanDistSucc_succ_apply_snoc, greaterThanBits_snoc]
          simp only [show (true = false) ↔ False by decide, ↓reduceIte, signVal_true, mul_neg_one,
            ENNReal.toReal_inv, ENNReal.toReal_natCast]
          push_cast [n]
          rfl
        rw [Finset.sum_congr rfl fun x' hx' =>
              Finset.sum_congr rfl fun y' hy' => hconst x' hx' y' hy']
        simp only [Finset.sum_const, nsmul_eq_mul]
        have h1 : (S₁.card : ℝ) = 2 * (1 - p) * s * (2 ^ (m + 1) : ℝ) := by
          rw [← hs₁_eq, div_mul_cancel₀ _ (by positivity)]
        have h2 : (T₀.card : ℝ) = 2 * q * t * (2 ^ (m + 1) : ℝ) := by
          rw [← ht₀_eq, div_mul_cancel₀ _ (by positivity)]
        rw [h1, h2]
        have hn_ne : (n : ℝ) ≠ 0 := by positivity
        field_simp [hn_ne]
      rw [h00, h11, h01, h10]
      ring
    -- Apply the induction hypothesis to `(S₀, T₀)` and `(S₁, T₁)`.
    have hbound00 :
        |∑ x' ∈ S₀, ∑ y' ∈ T₀, (greaterThanDistSucc m (x', y')).toReal *
            signVal (greaterThanBits (m + 1) x' y')| ≤
          20 * Real.sqrt (2 * p * s * (2 * q * t)) / Real.sqrt ((m + 1 : ℕ) : ℝ) := by
      rw [← hs₀_eq, ← ht₀_eq]
      by_cases h0 : S₀.Nonempty ∧ T₀.Nonempty
      · exact (ih S₀ T₀ h0.1 h0.2).le
      · rw [not_and_or, Finset.not_nonempty_iff_eq_empty, Finset.not_nonempty_iff_eq_empty] at h0
        rcases h0 with h0 | h0 <;> simp [h0]
    have hbound11 :
        |∑ x' ∈ S₁, ∑ y' ∈ T₁, (greaterThanDistSucc m (x', y')).toReal *
            signVal (greaterThanBits (m + 1) x' y')| ≤
          20 * Real.sqrt (2 * (1 - p) * s * (2 * (1 - q) * t)) / Real.sqrt ((m + 1 : ℕ) : ℝ) := by
      rw [← hs₁_eq, ← ht₁_eq]
      by_cases h1 : S₁.Nonempty ∧ T₁.Nonempty
      · exact (ih S₁ T₁ h1.1 h1.2).le
      · rw [not_and_or, Finset.not_nonempty_iff_eq_empty, Finset.not_nonempty_iff_eq_empty] at h1
        rcases h1 with h1 | h1 <;> simp [h1]
    have hcoeff_nonneg : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) / (2 * (n : ℝ)) := by positivity
    have htri :
        |∑ x ∈ S, ∑ y ∈ T, (greaterThanDistSucc (m + 1) (x, y)).toReal *
            signVal (greaterThanBits (m + 2) x y)| ≤
          ((m + 1 : ℕ) : ℝ) / (2 * (n : ℝ)) *
            (20 * Real.sqrt (2 * p * s * (2 * q * t)) / Real.sqrt ((m + 1 : ℕ) : ℝ)) +
          ((m + 1 : ℕ) : ℝ) / (2 * (n : ℝ)) *
            (20 * Real.sqrt (2 * (1 - p) * s * (2 * (1 - q) * t)) / Real.sqrt ((m + 1 : ℕ) : ℝ)) +
          (2 / (n : ℝ)) * |p - q| * s * t := by
      rw [hsplit]
      have h1 := abs_add_le
        (((m + 1 : ℕ) : ℝ) / (2 * (n : ℝ)) *
            (∑ x' ∈ S₀, ∑ y' ∈ T₀, (greaterThanDistSucc m (x', y')).toReal *
              signVal (greaterThanBits (m + 1) x' y')) +
          ((m + 1 : ℕ) : ℝ) / (2 * (n : ℝ)) *
            (∑ x' ∈ S₁, ∑ y' ∈ T₁, (greaterThanDistSucc m (x', y')).toReal *
              signVal (greaterThanBits (m + 1) x' y')))
        ((2 / (n : ℝ)) * (p - q) * s * t)
      have h2 := abs_add_le
        (((m + 1 : ℕ) : ℝ) / (2 * (n : ℝ)) *
            (∑ x' ∈ S₀, ∑ y' ∈ T₀, (greaterThanDistSucc m (x', y')).toReal *
              signVal (greaterThanBits (m + 1) x' y')))
        (((m + 1 : ℕ) : ℝ) / (2 * (n : ℝ)) *
            (∑ x' ∈ S₁, ∑ y' ∈ T₁, (greaterThanDistSucc m (x', y')).toReal *
              signVal (greaterThanBits (m + 1) x' y')))
      have h3 : |(2 / (n : ℝ)) * (p - q) * s * t| = (2 / (n : ℝ)) * |p - q| * s * t := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 / (n : ℝ)),
          abs_of_pos hs0, abs_of_pos ht0]
      rw [abs_mul, abs_mul, abs_of_nonneg hcoeff_nonneg] at h2
      have hm1 := mul_le_mul_of_nonneg_left hbound00 hcoeff_nonneg
      have hm2 := mul_le_mul_of_nonneg_left hbound11 hcoeff_nonneg
      linarith
    have hstep := gt_induction_step_lt hn2 hs0 hs1 ht0 ht1 hp0 hp1 hq0 hq1
    have hsub : n - 1 = m + 1 := rfl
    rw [hsub] at hstep
    exact htri.trans_lt hstep

/-- General non-strict rectangle discrepancy bound for possibly empty rectangles. -/
theorem discrepancy_greaterThanSucc_rect_le (m : ℕ) (S T : Finset (BitString (m + 1))) :
    |∑ x ∈ S, ∑ y ∈ T, (greaterThanDistSucc m (x, y)).toReal *
        signVal (greaterThanBits (m + 1) x y)| ≤
      20 * Real.sqrt ((S.card / (2 ^ (m + 1) : ℝ)) * (T.card / (2 ^ (m + 1) : ℝ))) /
        Real.sqrt ((m + 1 : ℕ) : ℝ) := by
  by_cases h : S.Nonempty ∧ T.Nonempty
  · exact (discrepancy_greaterThanSucc_rect_lt m S T h.1 h.2).le
  · rw [not_and_or, Finset.not_nonempty_iff_eq_empty, Finset.not_nonempty_iff_eq_empty] at h
    rcases h with rfl | rfl <;> simp

/-- The discrepancy of `GT_{m+1}` with respect to `μ_{m+1}`
is strictly less than `20 / √(m + 1)`. -/
theorem discrepancy_greaterThanSucc_lt (m : ℕ) :
    Cslib.Communication.discrepancy (greaterThanDistSucc m) (greaterThanBits (m + 1)) <
      20 / Real.sqrt ((m + 1 : ℕ) : ℝ) := by
  obtain ⟨S, T, hST⟩ :=
    Cslib.Communication.exists_abs_sum_eq_discrepancy (greaterThanDistSucc m)
      (greaterThanBits (m + 1))
  rw [← hST]
  by_cases h : S.Nonempty ∧ T.Nonempty
  · refine (discrepancy_greaterThanSucc_rect_lt m S T h.1 h.2).trans_le ?_
    have hs1 : (S.card : ℝ) / (2 ^ (m + 1) : ℝ) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have := Finset.card_le_univ S
      rw [BitString.card] at this
      exact_mod_cast this
    have ht1 : (T.card : ℝ) / (2 ^ (m + 1) : ℝ) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have := Finset.card_le_univ T
      rw [BitString.card] at this
      exact_mod_cast this
    have hsqrt_le :
        Real.sqrt ((S.card / (2 ^ (m + 1) : ℝ)) * (T.card / (2 ^ (m + 1) : ℝ))) ≤ 1 := by
      refine Real.sqrt_le_one.mpr ?_
      have h0 : (0 : ℝ) ≤ S.card / (2 ^ (m + 1) : ℝ) := by positivity
      have h1 : (0 : ℝ) ≤ T.card / (2 ^ (m + 1) : ℝ) := by positivity
      nlinarith
    have hnum :
        20 * Real.sqrt ((S.card / (2 ^ (m + 1) : ℝ)) * (T.card / (2 ^ (m + 1) : ℝ))) ≤ 20 := by
      linarith
    exact div_le_div_of_nonneg_right hnum (Real.sqrt_nonneg _)
  · rw [not_and_or, Finset.not_nonempty_iff_eq_empty, Finset.not_nonempty_iff_eq_empty] at h
    rcases h with rfl | rfl
    · simp only [Finset.sum_empty, abs_zero]
      positivity
    · simp only [Finset.sum_empty, Finset.sum_const_zero, abs_zero]
      positivity

/-- Transport of `discrepancy` across a pair of equivalences on inputs. -/
private theorem discrepancy_map_prodCongr {X Y X' Y' : Type*} [Finite X] [Finite Y]
    [Finite X'] [Finite Y'] (eX : X ≃ X') (eY : Y ≃ Y')
    (ν : PMF (X × Y)) (f : X' → Y' → Bool) :
    Cslib.Communication.discrepancy (ν.map (Equiv.prodCongr eX eY)) f =
      Cslib.Communication.discrepancy ν (fun x y => f (eX x) (eY y)) := by
  classical
  refine le_antisymm ?_ ?_
  · obtain ⟨A', B', hAB'⟩ :=
      Cslib.Communication.exists_abs_sum_eq_discrepancy (ν.map (Equiv.prodCongr eX eY)) f
    rw [← hAB']
    let A : Finset X := A'.map eX.symm.toEmbedding
    let B : Finset Y := B'.map eY.symm.toEmbedding
    have hsum :
        (∑ x' ∈ A', ∑ y' ∈ B', ((ν.map (Equiv.prodCongr eX eY)) (x', y')).toReal *
            signVal (f x' y')) =
        ∑ x ∈ A, ∑ y ∈ B, (ν (x, y)).toReal * signVal (f (eX x) (eY y)) := by
      rw [Finset.sum_map]
      refine Finset.sum_congr rfl fun x' _ => ?_
      rw [Finset.sum_map]
      refine Finset.sum_congr rfl fun y' _ => ?_
      simp only [Equiv.toEmbedding_apply, Equiv.apply_symm_apply]
      congr 2
      have heq := Cslib.Probability.PMF.map_equiv_apply ν (Equiv.prodCongr eX eY) (x', y')
      exact heq
    rw [hsum]
    exact Cslib.Communication.abs_sum_le_discrepancy ν (fun x y => f (eX x) (eY y)) A B
  · obtain ⟨A, B, hAB⟩ :=
      Cslib.Communication.exists_abs_sum_eq_discrepancy ν (fun x y => f (eX x) (eY y))
    rw [← hAB]
    let A' : Finset X' := A.map eX.toEmbedding
    let B' : Finset Y' := B.map eY.toEmbedding
    have hsum :
        (∑ x ∈ A, ∑ y ∈ B, (ν (x, y)).toReal * signVal (f (eX x) (eY y))) =
        ∑ x' ∈ A', ∑ y' ∈ B',
          ((ν.map (Equiv.prodCongr eX eY)) (x', y')).toReal * signVal (f x' y') := by
      rw [Finset.sum_map]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_map]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp only [Equiv.toEmbedding_apply]
      congr 2
      have heq := Cslib.Probability.PMF.map_equiv_apply ν (Equiv.prodCongr eX eY) (eX x, eY y)
      simpa using heq.symm
    rw [hsum]
    exact Cslib.Communication.abs_sum_le_discrepancy (ν.map (Equiv.prodCongr eX eY)) f A' B'

/-- For every `n ≥ 1`, the discrepancy of `GT_n` with respect to `greaterThanDist n hn` is
strictly less than `20 / √n`. -/
theorem discrepancy_greaterThan_lt (n : ℕ) (hn : 0 < n) :
    Cslib.Communication.discrepancy (greaterThanDist n hn) (greaterThanBits n) <
      20 / Real.sqrt (n : ℝ) := by
  let e : BitString (n - 1 + 1) ≃ BitString n :=
    Equiv.arrowCongr (finCongr (Nat.sub_add_cancel hn)) (Equiv.refl Bool)
  rw [greaterThanDist, discrepancy_map_prodCongr e e]
  have hgt : (fun x y : BitString (n - 1 + 1) => greaterThanBits n (e x) (e y)) =
      greaterThanBits (n - 1 + 1) := by
    funext x y
    simp only [greaterThanBits, Cslib.Communication.greaterThan, Fin.lt_def]
    congr 1
    have hval (z : BitString (n - 1 + 1)) :
        (BitString.equivFin n (e z) : ℕ) = (BitString.equivFin (n - 1 + 1) z : ℕ) := by
      rw [BitString.val_equivFin_eq_sum, BitString.val_equivFin_eq_sum]
      refine (Equiv.sum_comp (finCongr (Nat.sub_add_cancel hn))
        (fun i : Fin n => (e z i).toNat * 2 ^ (i : ℕ))).symm.trans ?_
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [e, Equiv.arrowCongr_apply, finCongr_apply]
    simp [hval]
  rw [hgt]
  have hsub : ((n - 1 + 1 : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast Nat.sub_add_cancel hn
  simpa [hsub] using discrepancy_greaterThanSucc_lt (n - 1)

/-- Existential form: for every `n ≥ 1`,
there exists a distribution `μ_n` on `BitString n × BitString n` such that
`Disc_{μ_n}(GT_n) < 20 / √n`. -/
theorem exists_dist_discrepancy_greaterThan_lt (n : ℕ) (hn : 0 < n) :
    ∃ μ : PMF (BitString n × BitString n),
      Cslib.Communication.discrepancy μ (greaterThanBits n) < 20 / Real.sqrt (n : ℝ) :=
  ⟨greaterThanDist n hn, discrepancy_greaterThan_lt n hn⟩

/-- Public-coin randomized communication complexity lower bound for the `n`-bit Greater-Than
function: any `1/3`-error public-coin protocol requires at least `log₂(n) / 2 - 7` bits. -/
theorem ecomplexity_greaterThan_lower_bound (n : ℕ) (hn : 0 < n) :
    ENNReal.ofReal (Real.logb 2 (n : ℝ) / 2 - 7) ≤
      (Cslib.Communication.PublicCoin.ecomplexityFun (1 / 3) (greaterThanBits n) : ℝ≥0∞) := by
  cases h : Cslib.Communication.PublicCoin.ecomplexityFun (1 / 3) (greaterThanBits n)
      using ENat.recTopCoe with
  | top => simp
  | coe c =>
      have hle' : Cslib.Communication.PublicCoin.ecomplexityFun (1 / 2 - 1 / 6)
          (greaterThanBits n) ≤ c := by
        rw [show (1 / 2 - 1 / 6 : ℝ) = 1 / 3 by norm_num]
        exact h.le
      have hdisc := Cslib.Communication.PublicCoin.two_mul_le_two_pow_mul_discrepancy
        (γ := 1 / 6) (c := c) hle' (greaterThanDist n hn)
      have hlt := discrepancy_greaterThan_lt n hn
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
      have hbound : Real.sqrt (n : ℝ) ≤ 60 * (2 : ℝ) ^ c := by
        have h1 : (1 / 3 : ℝ) < (2 : ℝ) ^ c * (20 / Real.sqrt (n : ℝ)) := by
          have : (2 : ℝ) ^ c * Cslib.Communication.discrepancy (greaterThanDist n hn)
              (greaterThanBits n) < (2 : ℝ) ^ c * (20 / Real.sqrt (n : ℝ)) :=
            mul_lt_mul_of_pos_left hlt (by positivity)
          linarith
        have h2 := (lt_div_iff₀ (Real.sqrt_pos.mpr hn_pos)).mp (by
          rw [← mul_div_assoc] at h1; exact h1)
        linarith
      have hlog : Real.logb 2 (n : ℝ) / 2 - 7 ≤ (c : ℝ) := by
        have h60 : Real.sqrt (n : ℝ) ≤ (2 : ℝ) ^ (c + 6) := by
          have : (60 : ℝ) ≤ 64 := by norm_num
          have h64 : (2 : ℝ) ^ (c + 6) = 64 * (2 : ℝ) ^ c := by rw [pow_add]; ring
          nlinarith [show (0 : ℝ) < (2 : ℝ) ^ c by positivity]
        have hlog1 := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
          (Real.sqrt_pos.mpr hn_pos) h60
        rw [Real.logb_two_pow, Real.sqrt_eq_rpow,
          Real.logb_rpow_eq_mul_logb_of_pos hn_pos] at hlog1
        push_cast at hlog1
        linarith
      rw [ENat.toENNReal_coe]
      simpa [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hlog

end CslibFrontier.Computability.Communication.Discrepancy

