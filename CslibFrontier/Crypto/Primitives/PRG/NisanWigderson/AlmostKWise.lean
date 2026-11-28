module

public import Cslib.Probability.PMF
public import CslibFrontier.Crypto.Primitives.PRG.NisanWigderson
public import CslibFrontier.Foundations.Data.BitString.Threshold
import CslibFrontier.Foundations.Data.BitString.Weight
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Almost `k`-Wise Independence of Nisan–Wigderson Distributions with Majority

This module defines the Nisan–Wigderson generator with per-coordinate input negations
(`nwGeneratorWithNeg`), its joint seed-and-output distribution `nwJointDist`, and `ε`-almost
`k`-wise independence (`IsAlmostKWiseIndependent`), and proves that instantiating the generator
with `Cslib.majority ℓ` on any `(ℓ, p)`-design yields a `(4 * √2 * p * k ^ 2 / √ℓ)`-almost
`k`-wise independent joint distribution whenever `2 * √2 * p * k ^ 2 ≤ √ℓ`.

## Main definitions

* `nwGeneratorWithNeg`: Nisan–Wigderson generator with fixed per-block input negations.
* `nwJointDist`: joint distribution `(U_t, NW^f_D(U_t))` on `{0, 1}^{t + m}`.
* `IsAlmostKWiseIndependent`: `ε`-almost `k`-wise independence for distributions on `{0, 1}^r`.
* `binomTail`: shifted binomial tail probability for the majority predicate.

## Main results

* `choose_le_two_pow_div_sqrt`: elementary central binomial bound `q.choose r ≤ 2 ^ q / √(q + 1)`.
* `abs_binomTail_sub_half_le`: shifted binomial tail deviation bound `|binomTail - 1 / 2|`.
* `majority_cond_count_bounds`: conditional bias of `Cslib.majority ℓ` after fixing `s` bits.
* `nwMajority_isAlmostKWiseIndependent`: explicit almost `k`-wise independence bound for
  `(U_t, NW^{majority}_D(U_t))` on any `(ℓ, p)`-design.
-/

public section

namespace CslibFrontier.Crypto.Primitives.PRG.NisanWigderson

open Cslib Cslib.BitString Finset
open scoped BigOperators ENNReal

/-- An `(ℓ, p)`-design of `m` sets in a universe of size `t`,
aliasing `Cslib.Crypto.PRG.NisanWigderson.Design`. Argument order: universe size `t`,
block cardinality `ℓ`, maximum pairwise intersection `p`, and number of sets `m`. -/
abbrev Design (t ℓ p m : ℕ) :=
  Cslib.Crypto.PRG.NisanWigderson.Design t ℓ p m

/-- The Nisan–Wigderson generator with fixed per-coordinate input negations. Output bit `i`
applies `f` to the restriction of `x` to the
`i`-th block `D.block i` with each coordinate `j` XORed with `neg i j`. -/
@[expose] def nwGeneratorWithNeg {t ℓ p m : ℕ} (D : Design t ℓ p m)
    (f : (Fin ℓ → Bool) → Bool) (neg : Fin m → Fin ℓ → Bool)
    (x : Fin t → Bool) : Fin m → Bool :=
  fun i => f (fun j => D.restrict i x j ^^ neg i j)

@[simp]
theorem nwGeneratorWithNeg_apply {t ℓ p m : ℕ} (D : Design t ℓ p m)
    (f : (Fin ℓ → Bool) → Bool) (neg : Fin m → Fin ℓ → Bool)
    (x : Fin t → Bool) (i : Fin m) :
    nwGeneratorWithNeg D f neg x i = f (fun j => D.restrict i x j ^^ neg i j) := by
  rfl

/-- Without negations, `nwGeneratorWithNeg` agrees with
`Cslib.Crypto.PRG.NisanWigderson.generator`. -/
theorem nwGeneratorWithNeg_false_eq_generator {t ℓ p m : ℕ} (D : Design t ℓ p m)
    (f : (Fin ℓ → Bool) → Bool) (x : Fin t → Bool) :
    nwGeneratorWithNeg D f (fun _ _ => false) x =
      Cslib.Crypto.PRG.NisanWigderson.generator D f x := by
  ext i
  rw [nwGeneratorWithNeg_apply, Cslib.Crypto.PRG.NisanWigderson.generator_apply]
  congr 1
  ext j
  simp

/-- The joint Nisan–Wigderson distribution `(U_t, NW^f_D(U_t))` on `{0, 1}^{t + m}`. -/
@[expose] noncomputable def nwJointDist {t ℓ p m : ℕ} (D : Design t ℓ p m)
    (f : (Fin ℓ → Bool) → Bool) (neg : Fin m → Fin ℓ → Bool) :
    PMF (Fin (t + m) → Bool) :=
  (Cslib.Probability.PMF.uniformOfFintype (Fin t → Bool)).map fun x =>
    Fin.append x (nwGeneratorWithNeg D f neg x)

/-- Probability of an event under `nwJointDist` equals the fraction of seeds `x ∈ {0, 1}^t`
whose joint output lies in the event. -/
theorem nwJointDist_toOuterMeasure_toReal {t ℓ p m : ℕ} (D : Design t ℓ p m)
    (f : (Fin ℓ → Bool) → Bool) (neg : Fin m → Fin ℓ → Bool)
    (E : Set (Fin (t + m) → Bool)) [DecidablePred (· ∈ E)] :
    ((nwJointDist D f neg).toOuterMeasure E).toReal =
      (#{x : Fin t → Bool | Fin.append x (nwGeneratorWithNeg D f neg x) ∈ E} : ℝ) / 2 ^ t := by
  classical
  unfold nwJointDist
  rw [PMF.toOuterMeasure_map_apply,
    Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_toReal]
  have hcard : (Fintype.card (Fin t → Bool) : ℝ) = 2 ^ t := by
    simp
  rw [hcard]
  congr 1
  exact_mod_cast congrArg Finset.card (by ext x; simp)

/-! ### Almost `k`-Wise Independence -/

/-- A distribution `D` on `{0, 1}^r` is `ε`-almost `k`-wise independent if for every `k`
distinct coordinates
`idx : Fin k ↪ Fin r` and every target assignment `α : Fin k → Bool`, the marginal probability
divided by `2⁻ᵏ` lies in `[1 - ε, 1 + ε]`. -/
@[expose] def IsAlmostKWiseIndependent (ε : ℝ) (k : ℕ) {r : ℕ} (D : PMF (Fin r → Bool)) : Prop :=
  ∀ (idx : Fin k ↪ Fin r) (α : Fin k → Bool),
    let prob := (D.toOuterMeasure {x | ∀ j, x (idx j) = α j}).toReal
    1 - ε ≤ prob / (2 : ℝ)⁻¹ ^ k ∧ prob / (2 : ℝ)⁻¹ ^ k ≤ 1 + ε

/-- Equivalent absolute-difference characterization of `IsAlmostKWiseIndependent`. -/
theorem isAlmostKWiseIndependent_iff_abs {ε : ℝ} {k r : ℕ} {D : PMF (Fin r → Bool)} :
    IsAlmostKWiseIndependent ε k D ↔
      ∀ (idx : Fin k ↪ Fin r) (α : Fin k → Bool),
        |(D.toOuterMeasure {x | ∀ j, x (idx j) = α j}).toReal - (2 : ℝ)⁻¹ ^ k| ≤
          ε * (2 : ℝ)⁻¹ ^ k := by
  have hpos : (0 : ℝ) < (2 : ℝ)⁻¹ ^ k := by positivity
  constructor
  · intro h idx α
    obtain ⟨hl, hu⟩ := h idx α
    rw [le_div_iff₀ hpos] at hl
    rw [div_le_iff₀ hpos] at hu
    rw [abs_le]
    constructor <;> linarith
  · intro h idx α
    have habs := h idx α
    rw [abs_le] at habs
    constructor
    · rw [le_div_iff₀ hpos]; linarith
    · rw [div_le_iff₀ hpos]; linarith

/-- Monotonicity of almost `k`-wise independence in the error parameter `ε`. -/
theorem IsAlmostKWiseIndependent.mono {ε₁ ε₂ : ℝ} {k r : ℕ} {D : PMF (Fin r → Bool)}
    (h : IsAlmostKWiseIndependent ε₁ k D) (hε : ε₁ ≤ ε₂) :
    IsAlmostKWiseIndependent ε₂ k D := by
  intro idx α
  obtain ⟨hl, hu⟩ := h idx α
  exact ⟨by linarith, by linarith⟩

/-- The uniform distribution on `{0, 1}^r` is `0`-almost `k`-wise independent for all `k`. -/
theorem isAlmostKWiseIndependent_uniform (k r : ℕ) :
    IsAlmostKWiseIndependent 0 k (Cslib.Probability.PMF.uniformOfFintype (Fin r → Bool)) := by
  classical
  rw [isAlmostKWiseIndependent_iff_abs]
  intro idx α
  have hmap :
      ((Cslib.Probability.PMF.uniformOfFintype (Fin r → Bool)).toOuterMeasure
          {x | ∀ j, x (idx j) = α j}).toReal =
        (2 : ℝ)⁻¹ ^ k := by
    have hpre :
        {x : Fin r → Bool | ∀ j, x (idx j) = α j} =
          (fun x : Fin r → Bool => fun j => x (idx j)) ⁻¹' {α} := by
      ext x
      simp [funext_iff]
    rw [hpre, ← PMF.toOuterMeasure_map_apply,
      Cslib.Probability.PMF.uniformOfFintype_pi_map_comp_embedding,
      PMF.toOuterMeasure_apply_singleton, Cslib.Probability.PMF.uniformOfFintype_apply]
    simp [ENNReal.toReal_inv, inv_pow]
  rw [hmap, sub_self, abs_zero, zero_mul]


/-! ### Elementary Central Binomial and Shifted Tail Bounds -/

/-- Elementary Wallis-type bound `(2n choose n)^2 * (2n + 1) ≤ (4^n)^2`, proved by induction
without Stirling's formula. -/
theorem centralBinom_sq_mul_le (n : ℕ) :
    (Nat.centralBinom n) ^ 2 * (2 * n + 1) ≤ (4 ^ n) ^ 2 := by
  induction n with
  | zero =>
    simp [Nat.centralBinom]
  | succ n ih =>
    have hrec : (n + 1) * Nat.centralBinom (n + 1) = 2 * (2 * n + 1) * Nat.centralBinom n := by
      have h := Nat.succ_mul_centralBinom_succ n
      linarith
    have hmul :
        ((n + 1) * Nat.centralBinom (n + 1)) ^ 2 * (2 * (n + 1) + 1) ≤
          ((n + 1) * 4 ^ (n + 1)) ^ 2 := by
      rw [hrec]
      have h1 :
          (2 * (2 * n + 1) * Nat.centralBinom n) ^ 2 * (2 * (n + 1) + 1) =
            4 * (2 * n + 1) * (2 * n + 3) * (Nat.centralBinom n ^ 2 * (2 * n + 1)) := by
        ring
      have h2 :
          4 * (2 * n + 1) * (2 * n + 3) ≤ 4 * (2 * n + 2) ^ 2 := by
        nlinarith
      have h3 :
          4 * (2 * n + 2) ^ 2 * (4 ^ n) ^ 2 = ((n + 1) * 4 ^ (n + 1)) ^ 2 := by
        rw [pow_succ]
        ring
      calc
        (2 * (2 * n + 1) * Nat.centralBinom n) ^ 2 * (2 * (n + 1) + 1)
            = 4 * (2 * n + 1) * (2 * n + 3) * (Nat.centralBinom n ^ 2 * (2 * n + 1)) := h1
        _ ≤ 4 * (2 * n + 1) * (2 * n + 3) * (4 ^ n) ^ 2 :=
            Nat.mul_le_mul_left _ ih
        _ ≤ 4 * (2 * n + 2) ^ 2 * (4 ^ n) ^ 2 :=
            Nat.mul_le_mul_right _ h2
        _ = ((n + 1) * 4 ^ (n + 1)) ^ 2 := h3
    have hpos : 0 < (n + 1) ^ 2 := by positivity
    have hmul' :
        (n + 1) ^ 2 * (Nat.centralBinom (n + 1) ^ 2 * (2 * (n + 1) + 1)) ≤
          (n + 1) ^ 2 * (4 ^ (n + 1)) ^ 2 := by
      linarith [show ((n + 1) * Nat.centralBinom (n + 1)) ^ 2 * (2 * (n + 1) + 1) =
        (n + 1) ^ 2 * (Nat.centralBinom (n + 1) ^ 2 * (2 * (n + 1) + 1)) by ring,
        show ((n + 1) * 4 ^ (n + 1)) ^ 2 = (n + 1) ^ 2 * (4 ^ (n + 1)) ^ 2 by ring]
    exact Nat.le_of_mul_le_mul_left hmul' hpos

/-- Every binomial coefficient satisfies `q.choose r ≤ 2 ^ q / √(q + 1)`. -/
theorem choose_le_two_pow_div_sqrt (q r : ℕ) :
    (Nat.choose q r : ℝ) ≤ (2 : ℝ) ^ q / Real.sqrt (q + 1 : ℝ) := by
  have hmid : (Nat.choose q r : ℝ) ≤ (Nat.choose q (q / 2) : ℝ) := by
    exact_mod_cast Nat.choose_le_middle r q
  refine hmid.trans ?_
  have hsq_nat : (Nat.choose q (q / 2)) ^ 2 * (q + 1) ≤ (2 ^ q) ^ 2 := by
    rcases Nat.even_or_odd' q with ⟨n, rfl | rfl⟩
    · have hdiv : (2 * n) / 2 = n := by omega
      rw [hdiv]
      have hcb := centralBinom_sq_mul_le n
      rw [Nat.centralBinom_eq_two_mul_choose] at hcb
      have h4 : (4 : ℕ) ^ n = 2 ^ (2 * n) := by
        rw [pow_mul]
        norm_num
      rwa [h4] at hcb
    · have hdiv : (2 * n + 1) / 2 = n := by omega
      rw [hdiv]
      have hsymm : Nat.choose (2 * n + 1) (n + 1) = Nat.choose (2 * n + 1) n := by
        have h := Nat.choose_symm (show n ≤ 2 * n + 1 by omega)
        rwa [show 2 * n + 1 - n = n + 1 by omega] at h
      have hpascal : Nat.centralBinom (n + 1) = 2 * Nat.choose (2 * n + 1) n := by
        rw [Nat.centralBinom, show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
          Nat.choose_succ_succ, hsymm]
        ring
      have hcb := centralBinom_sq_mul_le (n + 1)
      rw [hpascal] at hcb
      have h4 : (4 : ℕ) ^ (n + 1) = 2 * 2 ^ (2 * n + 1) := by
        rw [show (4 : ℕ) ^ (n + 1) = 2 ^ (2 * (n + 1)) by rw [pow_mul]; norm_num,
          show 2 * (n + 1) = (2 * n + 1) + 1 by omega, pow_succ']
      rw [h4] at hcb
      have hstep :
          4 * (Nat.choose (2 * n + 1) n ^ 2 * (2 * n + 1 + 1)) ≤
            (2 * Nat.choose (2 * n + 1) n) ^ 2 * (2 * (n + 1) + 1) := by
        nlinarith
      have hfin : 4 * (Nat.choose (2 * n + 1) n ^ 2 * (2 * n + 1 + 1)) ≤
          4 * (2 ^ (2 * n + 1)) ^ 2 := by
        calc
          4 * (Nat.choose (2 * n + 1) n ^ 2 * (2 * n + 1 + 1))
              ≤ (2 * Nat.choose (2 * n + 1) n) ^ 2 * (2 * (n + 1) + 1) := hstep
          _ ≤ (2 * 2 ^ (2 * n + 1)) ^ 2 := hcb
          _ = 4 * (2 ^ (2 * n + 1)) ^ 2 := by ring
      exact Nat.le_of_mul_le_mul_left hfin (by decide)
  have hsqrt_pos : (0 : ℝ) < Real.sqrt (q + 1 : ℝ) := Real.sqrt_pos.mpr (by positivity)
  rw [le_div_iff₀ hsqrt_pos]
  have hsq_real :
      ((Nat.choose q (q / 2) : ℝ) * Real.sqrt (q + 1 : ℝ)) ^ 2 ≤ ((2 : ℝ) ^ q) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    exact_mod_cast hsq_nat
  have hnonneg : 0 ≤ (2 : ℝ) ^ q := by positivity
  exact le_of_sq_le_sq hsq_real hnonneg

/-- Upper tail probability `Pr[Bin(q, 1/2) ≥ t]` for an integer threshold `t`. -/
noncomputable def binomTail (q : ℕ) (t : ℤ) : ℝ :=
  (∑ r ∈ Finset.range (q + 1), if t ≤ (r : ℤ) then (Nat.choose q r : ℝ) else 0) / (2 : ℝ) ^ q

/-- Symmetry identity `Pr[Bin(q, 1/2) ≥ t] + Pr[Bin(q, 1/2) ≥ q + 1 - t] = 1`. -/
theorem binomTail_add_symm (q : ℕ) (t : ℤ) :
    binomTail q t + binomTail q ((q : ℤ) + 1 - t) = 1 := by
  unfold binomTail
  rw [← add_div]
  have hrev :
      ∑ r ∈ Finset.range (q + 1),
          (if (q : ℤ) + 1 - t ≤ (r : ℤ) then (Nat.choose q r : ℝ) else 0) =
        ∑ r ∈ Finset.range (q + 1),
          (if (r : ℤ) < t then (Nat.choose q r : ℝ) else 0) := by
    refine Finset.sum_bij (fun r _ => q - r) ?_ ?_ ?_ ?_
    · intro r hr
      rw [Finset.mem_range] at hr ⊢
      omega
    · intro r₁ hr₁ r₂ hr₂ h
      rw [Finset.mem_range] at hr₁ hr₂
      omega
    · intro r hr
      rw [Finset.mem_range] at hr
      refine ⟨q - r, Finset.mem_range.mpr (by omega), by omega⟩
    · intro r hr
      rw [Finset.mem_range] at hr
      have hle : r ≤ q := by omega
      have hsymm : Nat.choose q (q - r) = Nat.choose q r := Nat.choose_symm hle
      have hcond : ((q : ℤ) + 1 - t ≤ (r : ℤ)) ↔ ((q - r : ℕ) : ℤ) < t := by
        omega
      rw [hsymm, if_congr hcond rfl rfl]
  rw [hrev, ← Finset.sum_add_distrib]
  have hsum :
      ∑ r ∈ Finset.range (q + 1),
          ((if t ≤ (r : ℤ) then (Nat.choose q r : ℝ) else 0) +
           (if (r : ℤ) < t then (Nat.choose q r : ℝ) else 0)) =
        (2 : ℝ) ^ q := by
    have hterm : ∀ r : ℕ,
        (if t ≤ (r : ℤ) then (Nat.choose q r : ℝ) else 0) +
        (if (r : ℤ) < t then (Nat.choose q r : ℝ) else 0) = (Nat.choose q r : ℝ) := by
      intro r
      by_cases h : t ≤ (r : ℤ)
      · have h' : ¬((r : ℤ) < t) := not_lt.mpr h
        simp [h, h']
      · have h' : (r : ℤ) < t := not_le.mp h
        simp [h, h']
    simp_rw [hterm]
    exact_mod_cast Nat.sum_range_choose q
  rw [hsum, div_self (by positivity)]

/-- Deviation of `Pr[Bin(q, 1/2) ≥ t]` from `1/2` is bounded by `|2t - (q + 1)| / (2 √(q + 1))`. -/
theorem abs_binomTail_sub_half_le (q : ℕ) (t : ℤ) :
    |binomTail q t - 1 / 2| ≤ (|2 * t - ((q : ℤ) + 1)| : ℝ) / (2 * Real.sqrt (q + 1 : ℝ)) := by
  have hcore : ∀ s : ℤ, 2 * s ≤ (q : ℤ) + 1 →
      0 ≤ binomTail q s - 1 / 2 ∧
      binomTail q s - 1 / 2 ≤ (((q : ℤ) + 1 - 2 * s : ℤ) : ℝ) / (2 * Real.sqrt (q + 1 : ℝ)) := by
    intro s hs
    have hsym := binomTail_add_symm q s
    have hdiff : 2 * (binomTail q s - 1 / 2) = binomTail q s - binomTail q ((q : ℤ) + 1 - s) := by
      linarith
    have hsub :
        binomTail q s - binomTail q ((q : ℤ) + 1 - s) =
          (∑ r ∈ Finset.range (q + 1),
            if s ≤ (r : ℤ) ∧ (r : ℤ) < (q : ℤ) + 1 - s then (Nat.choose q r : ℝ) else 0) /
            (2 : ℝ) ^ q := by
      unfold binomTail
      rw [← sub_div, ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun r _ => ?_
      by_cases h1 : s ≤ (r : ℤ)
      · by_cases h2 : (q : ℤ) + 1 - s ≤ (r : ℤ)
        · have hnot : ¬((r : ℤ) < (q : ℤ) + 1 - s) := not_lt.mpr h2
          simp [h1, h2, hnot]
        · have hlt : (r : ℤ) < (q : ℤ) + 1 - s := not_le.mp h2
          simp [h1, h2, hlt]
      · have h2 : ¬((q : ℤ) + 1 - s ≤ (r : ℤ)) := by omega
        simp [h1, h2]
    have hnonneg : 0 ≤ binomTail q s - binomTail q ((q : ℤ) + 1 - s) := by
      rw [hsub]
      refine div_nonneg (Finset.sum_nonneg fun r _ => ?_) (by positivity)
      split_ifs <;> positivity
    let I : Finset ℕ :=
      (Finset.range (q + 1)).filter fun r => s ≤ (r : ℤ) ∧ (r : ℤ) < (q : ℤ) + 1 - s
    have hcard_le : (#I : ℤ) ≤ (q : ℤ) + 1 - 2 * s := by
      let m : ℕ := ((q : ℤ) + 1 - 2 * s).toNat
      have hm : (m : ℤ) = (q : ℤ) + 1 - 2 * s := Int.toNat_of_nonneg (by omega)
      have hsubI : I.image (fun r : ℕ => ((r : ℤ) - s).toNat) ⊆ Finset.range m := by
        intro k hk
        rcases Finset.mem_image.mp hk with ⟨r, hr, rfl⟩
        simp only [I, Finset.mem_filter, Finset.mem_range] at hr
        rw [Finset.mem_range]
        omega
      have hinj : Set.InjOn (fun r : ℕ => ((r : ℤ) - s).toNat) I := by
        intro r₁ hr₁ r₂ hr₂ h
        simp only [Finset.mem_coe, I, Finset.mem_filter, Finset.mem_range] at hr₁ hr₂
        have h1 : (((r₁ : ℤ) - s).toNat : ℤ) = (r₁ : ℤ) - s := Int.toNat_of_nonneg (by omega)
        have h2 : (((r₂ : ℤ) - s).toNat : ℤ) = (r₂ : ℤ) - s := Int.toNat_of_nonneg (by omega)
        have hcast : (((r₁ : ℤ) - s).toNat : ℤ) = (((r₂ : ℤ) - s).toNat : ℤ) :=
          congrArg Nat.cast h
        omega
      have hle_m : #I ≤ m := by
        calc #I = #(I.image fun r : ℕ => ((r : ℤ) - s).toNat) :=
              (Finset.card_image_of_injOn hinj).symm
          _ ≤ #(Finset.range m) := Finset.card_le_card hsubI
          _ = m := Finset.card_range m
      rw [← hm]
      exact_mod_cast hle_m
    have hupper :
        binomTail q s - binomTail q ((q : ℤ) + 1 - s) ≤
          (((q : ℤ) + 1 - 2 * s : ℤ) : ℝ) / Real.sqrt (q + 1 : ℝ) := by
      rw [hsub, ← Finset.sum_filter]
      have hsum_le :
          ∑ r ∈ I, (Nat.choose q r : ℝ) ≤ (#I : ℝ) * ((2 : ℝ) ^ q / Real.sqrt (q + 1 : ℝ)) := by
        calc ∑ r ∈ I, (Nat.choose q r : ℝ)
            ≤ ∑ _r ∈ I, ((2 : ℝ) ^ q / Real.sqrt (q + 1 : ℝ)) :=
              Finset.sum_le_sum fun r _ => choose_le_two_pow_div_sqrt q r
          _ = (#I : ℝ) * ((2 : ℝ) ^ q / Real.sqrt (q + 1 : ℝ)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
      have hcard_real : (#I : ℝ) ≤ (((q : ℤ) + 1 - 2 * s : ℤ) : ℝ) := by
        exact_mod_cast hcard_le
      calc (∑ r ∈ I, (Nat.choose q r : ℝ)) / (2 : ℝ) ^ q
          ≤ ((#I : ℝ) * ((2 : ℝ) ^ q / Real.sqrt (q + 1 : ℝ))) / (2 : ℝ) ^ q :=
            div_le_div_of_nonneg_right hsum_le (by positivity)
        _ = (#I : ℝ) / Real.sqrt (q + 1 : ℝ) := by
            have h2pos : (2 : ℝ) ^ q ≠ 0 := by positivity
            field_simp [h2pos]
        _ ≤ (((q : ℤ) + 1 - 2 * s : ℤ) : ℝ) / Real.sqrt (q + 1 : ℝ) :=
            div_le_div_of_nonneg_right hcard_real (Real.sqrt_nonneg _)
    refine ⟨by linarith, ?_⟩
    have hdiv :
        (((q : ℤ) + 1 - 2 * s : ℤ) : ℝ) / Real.sqrt (q + 1 : ℝ) / 2 =
          (((q : ℤ) + 1 - 2 * s : ℤ) : ℝ) / (2 * Real.sqrt (q + 1 : ℝ)) := by
      ring
    linarith
  by_cases ht : 2 * t ≤ (q : ℤ) + 1
  · obtain ⟨h0, h1⟩ := hcore t ht
    rw [abs_of_nonneg h0]
    have habs : (|2 * t - ((q : ℤ) + 1)| : ℝ) = (((q : ℤ) + 1 - 2 * t : ℤ) : ℝ) := by
      have hint : |2 * t - ((q : ℤ) + 1)| = (q : ℤ) + 1 - 2 * t := by
        rw [abs_of_nonpos (by omega)]
        ring
      exact_mod_cast hint
    rwa [habs]
  · let t' : ℤ := (q : ℤ) + 1 - t
    have ht' : 2 * t' ≤ (q : ℤ) + 1 := by omega
    obtain ⟨h0, h1⟩ := hcore t' ht'
    have hsym := binomTail_add_symm q t
    have heq : binomTail q t - 1 / 2 = -(binomTail q t' - 1 / 2) := by
      dsimp only [t']
      linarith
    rw [heq, abs_neg, abs_of_nonneg h0]
    have habs : (|2 * t - ((q : ℤ) + 1)| : ℝ) = (((q : ℤ) + 1 - 2 * t' : ℤ) : ℝ) := by
      have hint : |2 * t - ((q : ℤ) + 1)| = (q : ℤ) + 1 - 2 * t' := by
        rw [abs_of_nonneg (by omega)]
        dsimp only [t']
        ring
      exact_mod_cast hint
    rwa [habs]

/-! ### Conditional Majority Bias Under Fixed Coordinates -/

/-- Fixing a subset `S ⊆ Fin ℓ` of coordinates of a uniform `ℓ`-bit string (with arbitrary
negation mask `mask`), the fraction of completions on `Sᶜ` for which `Cslib.majority ℓ` equals
`β` lies within `(#S + 1) / (2 √(ℓ - #S + 1))` of `1 / 2`. -/
theorem majority_cond_count_bounds {ℓ : ℕ} (S : Finset (Fin ℓ))
    (fix mask : Fin ℓ → Bool) (β : Bool) :
    let free : Finset (Fin ℓ) := Finset.univ \ S
    let q : ℕ := #free
    let δ : ℝ := (#S + 1 : ℝ) / (2 * Real.sqrt (ℓ - #S + 1 : ℝ))
    let good : Finset (free → Bool) :=
      Finset.univ.filter fun u =>
        Cslib.majority ℓ (fun j => (if h : j ∈ free then u ⟨j, h⟩ else fix j) ^^ mask j) = β
    (1 / 2 - δ) * (2 : ℝ) ^ q ≤ (#good : ℝ) ∧ (#good : ℝ) ≤ (1 / 2 + δ) * (2 : ℝ) ^ q := by
  intro free q δ good
  have hq : q = ℓ - #S := by
    dsimp only [q, free]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ, Fintype.card_fin]
  have hdisj : Disjoint free S := Finset.sdiff_disjoint
  have hunion : free ∪ S = Finset.univ := by
    simp [free]
  -- Count fixed 1-bits on `S` after applying `mask`.
  let a : ℕ := #(S.filter fun j => (fix j ^^ mask j) = true)
  have ha_le : a ≤ #S := Finset.card_filter_le _ _
  -- Reindex `u ↦ (fun j => u j ^^ mask j.1)` on `free → Bool` (a bijection).
  let flipFree : (free → Bool) ≃ (free → Bool) :=
    { toFun := fun u j => u j ^^ mask j.1
      invFun := fun u j => u j ^^ mask j.1
      left_inv := fun u => by ext j; simp
      right_inv := fun u => by ext j; simp }
  have hweight : ∀ u : free → Bool,
      weight (fun j : Fin ℓ => (if h : j ∈ free then u ⟨j, h⟩ else fix j) ^^ mask j) =
        a + weight (flipFree u) := by
    intro u
    rw [weight_eq_sum_toNat, weight_eq_sum_toNat, ← hunion, Finset.sum_union hdisj]
    have hfree_sum :
        ∑ j ∈ free, ((if h : j ∈ free then u ⟨j, h⟩ else fix j) ^^ mask j).toNat =
          ∑ j : free, (flipFree u j).toNat := by
      rw [← Finset.sum_attach free]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [flipFree, j.2]
    have hS_sum :
        ∑ j ∈ S, ((if h : j ∈ free then u ⟨j, h⟩ else fix j) ^^ mask j).toNat = a := by
      have hnot : ∀ j ∈ S, j ∉ free := fun j hj => Finset.disjoint_right.mp hdisj hj
      calc ∑ j ∈ S, ((if h : j ∈ free then u ⟨j, h⟩ else fix j) ^^ mask j).toNat
          = ∑ j ∈ S, (fix j ^^ mask j).toNat := by
            refine Finset.sum_congr rfl fun j hj => ?_
            simp [hnot j hj]
        _ = ∑ j ∈ S, if (fix j ^^ mask j) = true then 1 else 0 := by
            refine Finset.sum_congr rfl fun j _ => ?_
            cases (fix j ^^ mask j) <;> rfl
        _ = a := by rw [Finset.sum_boole]; simp [a]
    rw [hfree_sum, hS_sum, add_comm]
  -- Count `goodTrue`: those `u` where `majority = true`.
  let goodTrue : Finset (free → Bool) :=
    Finset.univ.filter fun u =>
      Cslib.majority ℓ (fun j => (if h : j ∈ free then u ⟨j, h⟩ else fix j) ^^ mask j) = true
  let t : ℤ := (((ℓ + 1) / 2 : ℕ) : ℤ) - (a : ℤ)
  have hcard_true : (#goodTrue : ℝ) / (2 : ℝ) ^ q = binomTail q t := by
    have hbij : #goodTrue = #{v : free → Bool | t ≤ (weight v : ℤ)} := by
      refine Finset.card_bij (fun u _ => flipFree u) ?_ ?_ ?_
      · intro u hu
        simp only [goodTrue, Finset.mem_filter, Finset.mem_univ, true_and,
          Cslib.majority_eq_true_iff, hweight] at hu ⊢
        omega
      · intro u₁ _ u₂ _ h
        exact flipFree.injective h
      · intro v hv
        refine ⟨flipFree.symm v, ?_, by simp⟩
        simp only [goodTrue, Finset.mem_filter, Finset.mem_univ, true_and,
          Cslib.majority_eq_true_iff, hweight, Equiv.apply_symm_apply] at hv ⊢
        omega
    have hlayers :
        #{v : free → Bool | t ≤ (weight v : ℤ)} =
          ∑ r ∈ Finset.range (q + 1), if t ≤ (r : ℤ) then Nat.choose q r else 0 := by
      have hpart :
          (Finset.univ.filter fun v : free → Bool => t ≤ (weight v : ℤ)) =
            (Finset.range (q + 1)).biUnion fun r =>
              if t ≤ (r : ℤ) then Finset.univ.filter (fun v : free → Bool => weight v = r)
              else ∅ := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
          Finset.mem_range]
        constructor
        · intro hv
          refine ⟨weight v, ?_, ?_⟩
          · have hw : weight v ≤ Fintype.card free := weight_le v
            rw [Fintype.card_coe] at hw
            omega
          · simp [hv]
        · rintro ⟨r, _, hr⟩
          split_ifs at hr with htr
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
            rwa [hr]
          · simp at hr
      rw [hpart, Finset.card_biUnion]
      · refine Finset.sum_congr rfl fun r _ => ?_
        split_ifs
        · rw [card_filter_weight_eq, Fintype.card_coe]
        · simp
      · intro r₁ _ r₂ _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro v hv1 hv2
        by_cases h1 : t ≤ (r₁ : ℤ) <;> by_cases h2 : t ≤ (r₂ : ℤ) <;> simp_all
    rw [hbij, hlayers]
    unfold binomTail
    congr 1
    push_cast
    refine Finset.sum_congr rfl fun r _ => ?_
    split_ifs <;> simp
  have hdev_true : |(#goodTrue : ℝ) / (2 : ℝ) ^ q - 1 / 2| ≤ δ := by
    rw [hcard_true]
    refine (abs_binomTail_sub_half_le q t).trans ?_
    have hS_le : #S ≤ ℓ := by
      calc #S ≤ #(Finset.univ : Finset (Fin ℓ)) := Finset.card_le_card (Finset.subset_univ _)
        _ = ℓ := by simp
    have hnum : (|2 * t - ((q : ℤ) + 1)| : ℝ) ≤ (#S + 1 : ℝ) := by
      have hint : |2 * t - ((q : ℤ) + 1)| ≤ (#S : ℤ) + 1 := by
        rw [abs_le]
        dsimp only [t]
        rw [hq]
        have hdiv_lo : (ℓ : ℤ) ≤ 2 * (((ℓ + 1) / 2 : ℕ) : ℤ) := by omega
        have hdiv_hi : 2 * (((ℓ + 1) / 2 : ℕ) : ℤ) ≤ (ℓ : ℤ) + 1 := by omega
        have hsub_cast : ((ℓ - #S : ℕ) : ℤ) = (ℓ : ℤ) - (#S : ℤ) := by omega
        rw [hsub_cast]
        constructor <;> omega
      exact_mod_cast hint
    rw [show (q : ℝ) + 1 = (ℓ - #S + 1 : ℝ) by
      rw [hq]
      have hcast : ((ℓ - #S : ℕ) : ℝ) = (ℓ : ℝ) - (#S : ℝ) := Nat.cast_sub hS_le
      linarith]
    exact div_le_div_of_nonneg_right hnum (by positivity)
  have hdev : |(#good : ℝ) / (2 : ℝ) ^ q - 1 / 2| ≤ δ := by
    cases β
    · have hcompl : #good + #goodTrue = 2 ^ q := by
        have htot : #good + #goodTrue = Fintype.card (free → Bool) := by
          have hd : Disjoint good goodTrue := by
            rw [Finset.disjoint_filter]
            intro u _ h1 h2
            rw [h1] at h2
            exact Bool.false_ne_true h2
          have hu : good ∪ goodTrue = Finset.univ := by
            ext u
            simp only [good, goodTrue, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
              true_and]
            cases Cslib.majority ℓ _ <;> simp
          rw [← Finset.card_union_of_disjoint hd, hu, Finset.card_univ]
        rw [htot, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
      have hrel : (#good : ℝ) / (2 : ℝ) ^ q = 1 - (#goodTrue : ℝ) / (2 : ℝ) ^ q := by
        have h2pos : (2 : ℝ) ^ q ≠ 0 := by positivity
        have hreal : (#good : ℝ) + (#goodTrue : ℝ) = (2 : ℝ) ^ q := by exact_mod_cast hcompl
        field_simp [h2pos]
        linarith
      rw [hrel, show 1 - (#goodTrue : ℝ) / (2 : ℝ) ^ q - 1 / 2 =
        -((#goodTrue : ℝ) / (2 : ℝ) ^ q - 1 / 2) by ring, abs_neg]
      exact hdev_true
    · exact hdev_true
  have hpos : (0 : ℝ) < (2 : ℝ) ^ q := by positivity
  rw [abs_le] at hdev
  constructor
  · have := (le_div_iff₀ hpos).mp (show 1 / 2 - δ ≤ (#good : ℝ) / (2 : ℝ) ^ q by linarith)
    linarith
  · have := (div_le_iff₀ hpos).mp (show (#good : ℝ) / (2 : ℝ) ^ q ≤ 1 / 2 + δ by linarith)
    linarith

/-! ### Conditioning Induction and Almost `k`-Wise Independence -/

/-- Adding one NW output bit `j₀ ∉ js` multiplies the count of consistent seeds by a factor in
`[1/2 - δ, 1/2 + δ]`, where `δ = (s + 1) / (2 √(ℓ - s + 1))` and `s = #(D.block j₀ ∩ A)`
bounds the coordinates of `D.block j₀` shared with previously conditioned seed/output bits. -/
private theorem card_nw_cond_step {t ℓ p m : ℕ} (D : Design t ℓ p m)
    (neg : Fin m → Fin ℓ → Bool)
    (IC : Finset (Fin t)) (αC : Fin t → Bool)
    (js : Finset (Fin m)) (αD : Fin m → Bool)
    (j₀ : Fin m) (_hj₀ : j₀ ∉ js) :
    let A : Finset (Fin t) := IC ∪ js.biUnion D.block
    let s : ℕ := #(D.block j₀ ∩ A)
    let δ : ℝ := (s + 1 : ℝ) / (2 * Real.sqrt (ℓ - s + 1 : ℝ))
    let prev : Finset (Fin t → Bool) :=
      Finset.univ.filter fun x =>
        (∀ i ∈ IC, x i = αC i) ∧
        (∀ j ∈ js, nwGeneratorWithNeg D (Cslib.majority ℓ) neg x j = αD j)
    let next : Finset (Fin t → Bool) :=
      prev.filter fun x => nwGeneratorWithNeg D (Cslib.majority ℓ) neg x j₀ = αD j₀
    (1 / 2 - δ) * (#prev : ℝ) ≤ (#next : ℝ) ∧ (#next : ℝ) ≤ (1 / 2 + δ) * (#prev : ℝ) := by
  intro A s δ prev next
  let Fset : Finset (Fin t) := D.block j₀ \ A
  let Kset : Finset (Fin t) := Finset.univ \ Fset
  have hFK_disj : Disjoint Fset Kset := by
    rw [Finset.disjoint_left]
    intro x hx hK
    exact (Finset.mem_sdiff.mp hK).2 hx
  have hFK_union : Fset ∪ Kset = Finset.univ := by
    ext x
    simp [Kset]
  have hA_sub_K : A ⊆ Kset := by
    intro x hx
    simp only [Kset, Fset, Finset.mem_sdiff, Finset.mem_univ, true_and, not_and, not_not]
    intro _
    exact hx
  -- Equivalence splitting `x : Fin t → Bool` into `(x|_Kset, x|_Fset)`.
  let splitKF : (Fin t → Bool) ≃ (Kset → Bool) × (Fset → Bool) :=
    { toFun := fun x => (fun k => x k.1, fun f => x f.1)
      invFun := fun p i =>
        if h : i ∈ Fset then p.2 ⟨i, h⟩
        else p.1 ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h⟩⟩
      left_inv := fun x => by
        ext i
        by_cases h : i ∈ Fset <;> simp [h]
      right_inv := fun ⟨pK, pF⟩ => by
        ext k
        · have hk : k.1 ∉ Fset := (Finset.mem_sdiff.mp k.2).2
          simp [hk]
        · simp [k.2] }
  -- `prev` depends only on `x|_Kset`.
  let prevK : Finset (Kset → Bool) :=
    Finset.univ.filter fun pK =>
      (∀ i (hi : i ∈ IC), pK ⟨i, hA_sub_K (Finset.mem_union_left _ hi)⟩ = αC i) ∧
      (∀ j ∈ js,
        let x0 := splitKF.symm (pK, fun _ => false)
        nwGeneratorWithNeg D (Cslib.majority ℓ) neg x0 j = αD j)
  have hprev_iff : ∀ pK pF, splitKF.symm (pK, pF) ∈ prev ↔ pK ∈ prevK := by
    intro pK pF
    have hagree : ∀ i ∈ A,
        splitKF.symm (pK, pF) i = splitKF.symm (pK, fun _ => false) i := by
      intro i hi
      have hnot : i ∉ Fset := (Finset.mem_sdiff.mp (hA_sub_K hi)).2
      simp [splitKF, hnot]
    simp only [prev, prevK, Finset.mem_filter, Finset.mem_univ, true_and]
    refine and_congr ?_ ?_
    · refine forall₂_congr fun i hi => ?_
      have hnot : i ∉ Fset := (Finset.mem_sdiff.mp (hA_sub_K (Finset.mem_union_left _ hi))).2
      simp [splitKF, hnot]
    · refine forall₂_congr fun j hj => ?_
      have hblock_eq :
          D.restrict j (splitKF.symm (pK, pF)) =
            D.restrict j (splitKF.symm (pK, fun _ => false)) := by
        ext r
        simp only [Cslib.Crypto.PRG.NisanWigderson.Design.restrict_apply]
        apply hagree
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, hj,
          Finset.orderEmbOfFin_mem _ _ r⟩)
      rw [nwGeneratorWithNeg_apply, nwGeneratorWithNeg_apply, hblock_eq]
  -- Card of `prev` is `#prevK * 2^#Fset`.
  have hcard_prev : #prev = #prevK * 2 ^ #Fset := by
    have hbij : #prev = #(prevK ×ˢ (Finset.univ : Finset (Fset → Bool))) := by
      refine Finset.card_bij (fun x _ => splitKF x) ?_ ?_ ?_
      · intro x hx
        rw [Finset.mem_product]
        refine ⟨?_, Finset.mem_univ _⟩
        have hx' : splitKF.symm (splitKF x) ∈ prev := by simpa using hx
        exact (hprev_iff _ _).mp hx'
      · intro x₁ _ x₂ _ h
        exact splitKF.injective h
      · intro p hp
        rw [Finset.mem_product] at hp
        exact ⟨splitKF.symm p, (hprev_iff p.1 p.2).mpr hp.1, splitKF.apply_symm_apply p⟩
    rw [hbij, Finset.card_product, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_coe]
  -- Card of `next` is the sum over `pK ∈ prevK` of the fiber count over `pF : Fset → Bool`.
  let fiber (pK : Kset → Bool) : Finset (Fset → Bool) :=
    Finset.univ.filter fun pF =>
      nwGeneratorWithNeg D (Cslib.majority ℓ) neg (splitKF.symm (pK, pF)) j₀ = αD j₀
  have hcard_next : #next = ∑ pK ∈ prevK, #(fiber pK) := by
    have hbij : #next = #(prevK.sigma fiber) := by
      refine Finset.card_bij (fun x _ => ⟨(splitKF x).1, (splitKF x).2⟩) ?_ ?_ ?_
      · intro x hx
        rw [Finset.mem_sigma]
        have hx' := Finset.mem_filter.mp hx
        have hpK : (splitKF x).1 ∈ prevK :=
          (hprev_iff (splitKF x).1 (splitKF x).2).mp (by simpa using hx'.1)
        refine ⟨hpK, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
        simpa using hx'.2
      · intro x₁ _ x₂ _ h
        apply splitKF.injective
        exact Prod.ext (congrArg Sigma.fst h) (by simpa using congrArg Sigma.snd h)
      · rintro ⟨pK, pF⟩ hmem
        rw [Finset.mem_sigma] at hmem
        refine ⟨splitKF.symm (pK, pF), ?_, by simp⟩
        rw [Finset.mem_filter]
        exact ⟨(hprev_iff pK pF).mpr hmem.1, (Finset.mem_filter.mp hmem.2).2⟩
    rw [hbij, Finset.card_sigma]
  -- Relate each fiber to `majority_cond_count_bounds` via `orderEmbOfFin` on `D.block j₀`.
  let emb : Fin ℓ ↪o Fin t := (D.block j₀).orderEmbOfFin (D.card_block j₀)
  let S : Finset (Fin ℓ) := Finset.univ.filter fun r => emb r ∈ A
  have hcard_S : #S = s := by
    refine Finset.card_bij (fun r _ => emb r) ?_ ?_ ?_
    · intro r hr
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hr
      exact Finset.mem_inter.mpr ⟨Finset.orderEmbOfFin_mem _ _ r, hr⟩
    · intro r₁ _ r₂ _ h
      exact emb.injective h
    · intro x hx
      rcases Finset.mem_inter.mp hx with ⟨hxB, hxA⟩
      have hrange : x ∈ Set.range emb := by
        simpa [emb] using hxB
      obtain ⟨r, rfl⟩ := hrange
      exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxA⟩, rfl⟩
  let free : Finset (Fin ℓ) := Finset.univ \ S
  let hF_equiv_free : Fset ≃ free :=
    { toFun := fun x =>
        let hxB : x.1 ∈ D.block j₀ := (Finset.mem_sdiff.mp x.2).1
        let hxA : x.1 ∉ A := (Finset.mem_sdiff.mp x.2).2
        let r : Fin ℓ := ((D.block j₀).orderIsoOfFin (D.card_block j₀)).symm ⟨x.1, hxB⟩
        ⟨r, by
          simp only [free, S, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_filter]
          have hemb : emb r = x.1 := by
            simp only [emb, r, ← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
          rwa [hemb]⟩
      invFun := fun r =>
        ⟨emb r.1, by
          have hr : emb r.1 ∉ A := by
            have := (Finset.mem_sdiff.mp r.2).2
            simpa [S] using this
          exact Finset.mem_sdiff.mpr ⟨Finset.orderEmbOfFin_mem _ _ r.1, hr⟩⟩
      left_inv := fun x => by
        ext
        simp [emb, ← Finset.coe_orderIsoOfFin_apply]
      right_inv := fun r => by
        apply Subtype.ext
        apply emb.injective
        simp [emb, ← Finset.coe_orderIsoOfFin_apply] }
  have hcard_F : #Fset = #free := by
    have := Fintype.card_congr hF_equiv_free
    simpa using this
  have hfiber_bounds : ∀ pK : Kset → Bool,
      (1 / 2 - δ) * (2 : ℝ) ^ #Fset ≤ (#(fiber pK) : ℝ) ∧
        (#(fiber pK) : ℝ) ≤ (1 / 2 + δ) * (2 : ℝ) ^ #Fset := by
    intro pK
    let fix : Fin ℓ → Bool := fun r =>
      if h : emb r ∈ Fset then false
      else pK ⟨emb r, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h⟩⟩
    have hmb := majority_cond_count_bounds S fix (neg j₀) (αD j₀)
    have hcard_fiber :
        #(fiber pK) =
          #(Finset.univ.filter fun u : free → Bool =>
            Cslib.majority ℓ
              (fun j => (if h : j ∈ free then u ⟨j, h⟩ else fix j) ^^ neg j₀ j) = αD j₀) := by
      refine Finset.card_bij (fun pF _ r => pF (hF_equiv_free.symm r)) ?_ ?_ ?_
      · intro pF hpF
        simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and,
          nwGeneratorWithNeg_apply] at hpF ⊢
        convert hpF using 2
        ext r
        congr 1
        simp only [Cslib.Crypto.PRG.NisanWigderson.Design.restrict_apply, splitKF,
          Equiv.coe_fn_symm_mk]
        by_cases hr : r ∈ free
        · have hmem : emb r ∈ Fset := (hF_equiv_free.symm ⟨r, hr⟩).2
          rw [dite_eq_left hr, dite_eq_left hmem]
          rfl
        · have hnot : emb r ∉ Fset := by
            intro hmem
            apply hr
            have hnotA : emb r ∉ A := (Finset.mem_sdiff.mp hmem).2
            simp [free, S, hnotA]
          rw [dite_eq_right hr, dite_eq_right hnot]
          dsimp only [fix]
          rw [dite_eq_right hnot]
      · intro pF₁ _ pF₂ _ h
        ext x
        have := congrFun h (hF_equiv_free x)
        simpa using this
      · intro u hu
        refine ⟨fun x => u (hF_equiv_free x), ?_, by ext r; simp⟩
        simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and,
          nwGeneratorWithNeg_apply] at hu ⊢
        convert hu using 2
        ext r
        congr 1
        simp only [Cslib.Crypto.PRG.NisanWigderson.Design.restrict_apply, splitKF,
          Equiv.coe_fn_symm_mk]
        by_cases hr : r ∈ free
        · have hmem : emb r ∈ Fset := (hF_equiv_free.symm ⟨r, hr⟩).2
          rw [dite_eq_left hmem, dite_eq_left hr]
          have heq : hF_equiv_free ⟨emb r, hmem⟩ = ⟨r, hr⟩ :=
            hF_equiv_free.apply_symm_apply ⟨r, hr⟩
          rw [heq]
        · have hnot : emb r ∉ Fset := by
            intro hmem
            apply hr
            have hnotA : emb r ∉ A := (Finset.mem_sdiff.mp hmem).2
            simp [free, S, hnotA]
          rw [dite_eq_right hnot, dite_eq_right hr]
          dsimp only [fix]
          rw [dite_eq_right hnot]
    rw [hcard_fiber, hcard_F]
    simpa only [δ, hcard_S] using hmb
  rw [hcard_next, hcard_prev]
  push_cast
  have hlo :
      (1 / 2 - δ) * ((#prevK : ℝ) * (2 : ℝ) ^ #Fset) ≤ ∑ pK ∈ prevK, (#(fiber pK) : ℝ) := by
    calc (1 / 2 - δ) * ((#prevK : ℝ) * (2 : ℝ) ^ #Fset)
        = ∑ _pK ∈ prevK, ((1 / 2 - δ) * (2 : ℝ) ^ #Fset) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ pK ∈ prevK, (#(fiber pK) : ℝ) :=
          Finset.sum_le_sum fun pK _ => (hfiber_bounds pK).1
  have hhi :
      ∑ pK ∈ prevK, (#(fiber pK) : ℝ) ≤ (1 / 2 + δ) * ((#prevK : ℝ) * (2 : ℝ) ^ #Fset) := by
    calc ∑ pK ∈ prevK, (#(fiber pK) : ℝ)
        ≤ ∑ _pK ∈ prevK, ((1 / 2 + δ) * (2 : ℝ) ^ #Fset) :=
          Finset.sum_le_sum fun pK _ => (hfiber_bounds pK).2
      _ = (1 / 2 + δ) * ((#prevK : ℝ) * (2 : ℝ) ^ #Fset) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
  exact ⟨hlo, hhi⟩

/-- Elementary bound `1 - k * x ≤ (1 - x) ^ k` for `0 ≤ x ≤ 1`. -/
private theorem one_sub_mul_le_pow {x : ℝ} (_ : 0 ≤ x) (hx1 : x ≤ 1) (k : ℕ) :
    1 - (k : ℝ) * x ≤ (1 - x) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.cast_succ]
    have h1 : 0 ≤ 1 - x := by linarith
    have h2 : (1 - (k : ℝ) * x) * (1 - x) ≤ (1 - x) ^ k * (1 - x) :=
      mul_le_mul_of_nonneg_right ih h1
    have h3 : (1 - (k : ℝ) * x) * (1 - x) = 1 - ((k : ℝ) + 1) * x + (k : ℝ) * x ^ 2 := by ring
    have h4 : 0 ≤ (k : ℝ) * x ^ 2 := by positivity
    linarith

/-- Clean elementary bound `Real.exp y ≤ 1 + 2 * y` for `0 ≤ y ≤ 1`. -/
private theorem exp_le_one_add_two_mul {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    Real.exp y ≤ 1 + 2 * y := by
  have hb := Real.exp_bound (x := y) (n := 2) (by rw [abs_of_nonneg hy0]; exact hy1) (by decide)
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero] at hb
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, pow_one, Nat.factorial_one,
    zero_add] at hb
  rw [abs_le] at hb
  have hterm : |y| ^ 2 * ((2 + 1 : ℕ) / ((2 : ℕ).factorial * (2 : ℕ))) = 3 / 4 * y ^ 2 := by
    rw [abs_of_nonneg hy0]
    norm_num
    ring
  have hsq : y ^ 2 ≤ y := by nlinarith
  linarith [hb.2, hterm, hsq]

/-- Elementary bound `(1 + x) ^ k ≤ 1 + 2 * (k * x)` for `0 ≤ x` and `k * x ≤ 1`. -/
private theorem one_add_pow_le_one_add_two_mul {x : ℝ} (hx0 : 0 ≤ x) {k : ℕ}
    (hkx : (k : ℝ) * x ≤ 1) :
    (1 + x) ^ k ≤ 1 + 2 * ((k : ℝ) * x) := by
  have hexp1 : 1 + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have hpow : (1 + x) ^ k ≤ Real.exp ((k : ℝ) * x) := by
    calc (1 + x) ^ k ≤ (Real.exp x) ^ k := pow_le_pow_left₀ (by linarith) hexp1 k
      _ = Real.exp ((k : ℝ) * x) := by rw [← Real.exp_nat_mul]
  exact hpow.trans (exp_le_one_add_two_mul (by positivity) hkx)

/-- Almost `k`-wise independence of the joint Nisan–Wigderson distribution with majority:
for any `(ℓ, p)`-design `D` in a universe of size `t` with `1 ≤ p` and `1 ≤ ℓ`, and any `k`
satisfying `2 * √2 * p * k^2 ≤ √ℓ`, the joint Nisan–Wigderson distribution
`(U_t, NW^majority_D(U_t))` (for any fixed per-coordinate negation pattern `neg`) is
`(4 * √2 * p * k^2 / √ℓ)`-almost `k`-wise independent. -/
theorem nwMajority_isAlmostKWiseIndependent {t ℓ p m : ℕ} (D : Design t ℓ p m)
    (neg : Fin m → Fin ℓ → Bool) (hp : 1 ≤ p) (hℓ : 1 ≤ ℓ) (k : ℕ)
    (hk : 2 * Real.sqrt 2 * (p : ℝ) * (k : ℝ) ^ 2 ≤ Real.sqrt (ℓ : ℝ)) :
    IsAlmostKWiseIndependent (4 * Real.sqrt 2 * (p : ℝ) * (k : ℝ) ^ 2 / Real.sqrt (ℓ : ℝ)) k
      (nwJointDist D (Cslib.majority ℓ) neg) := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk_pos
  · intro idx α
    have huniv : {x : Fin (t + m) → Bool | ∀ j : Fin 0, x (idx j) = α j} = Set.univ := by
      ext x
      simp
    rw [huniv]
    have hsum := Cslib.Probability.PMF.toOuterMeasure_toReal_eq_sum_ite
      (nwJointDist D (Cslib.majority ℓ) neg) (Set.univ)
    simp only [Set.mem_univ, ↓reduceIte, mul_one, Cslib.Probability.PMF.sum_toReal] at hsum
    rw [hsum]
    norm_num
  have hℓ_pos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
  have hsqrt_ℓ_pos : (0 : ℝ) < Real.sqrt (ℓ : ℝ) := Real.sqrt_pos.mpr hℓ_pos
  have hp_pos : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hk_ge1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_pos
  -- Uniform single-step bias bound `δ := √2 * p * k / √ℓ`.
  let δ : ℝ := Real.sqrt 2 * (p : ℝ) * (k : ℝ) / Real.sqrt (ℓ : ℝ)
  have hδ_nonneg : 0 ≤ δ := by positivity
  have h2kδ : 2 * (k : ℝ) * δ ≤ 1 := by
    have hcalc : 2 * (k : ℝ) * δ = 2 * Real.sqrt 2 * (p : ℝ) * (k : ℝ) ^ 2 / Real.sqrt (ℓ : ℝ) := by
      dsimp only [δ]
      ring
    rw [hcalc, div_le_one hsqrt_ℓ_pos]
    exact hk
  have h2δ_le1 : 2 * δ ≤ 1 := by
    have : 2 * δ ≤ 2 * (k : ℝ) * δ := by nlinarith
    linarith
  have hpk_le_half : 2 * (p * k) ≤ ℓ := by
    have h1 : 2 * Real.sqrt 2 * ((p * k : ℕ) : ℝ) ≤ Real.sqrt (ℓ : ℝ) := by
      push_cast
      have hk_sq : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
      have hpk_le : (p : ℝ) * (k : ℝ) ≤ (p : ℝ) * (k : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hk_sq (by positivity)
      have hmul : 2 * Real.sqrt 2 * ((p : ℝ) * (k : ℝ)) ≤
          2 * Real.sqrt 2 * ((p : ℝ) * (k : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hpk_le (by positivity)
      linarith
    have hsq : (2 * Real.sqrt 2 * ((p * k : ℕ) : ℝ)) ^ 2 ≤ (Real.sqrt (ℓ : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hℓ_pos.le] at hsq
    have hnat : 8 * (p * k) ^ 2 ≤ ℓ := by
      have : (8 : ℝ) * ((p * k : ℕ) : ℝ) ^ 2 ≤ (ℓ : ℝ) := by linarith
      exact_mod_cast this
    have hpk1 : 1 ≤ p * k := Nat.mul_pos hp hk_pos
    nlinarith
  intro idx α
  -- Split the `k` coordinates into `IC ⊆ Fin t` and `JD ⊆ Fin m`.
  let IC : Finset (Fin t) :=
    Finset.univ.filter fun i => ∃ a : Fin k, idx a = Fin.castAdd m i
  let JD : Finset (Fin m) :=
    Finset.univ.filter fun j => ∃ a : Fin k, idx a = Fin.natAdd t j
  have hcard_split : #IC + #JD = k := by
    let S_C : Finset (Fin k) := Finset.univ.filter fun a => (idx a).val < t
    let S_D : Finset (Fin k) := Finset.univ.filter fun a => t ≤ (idx a).val
    have hIC : #IC = #S_C := by
      refine Finset.card_bij (fun i hi => Classical.choose (Finset.mem_filter.mp hi).2) ?_ ?_ ?_
      · intro i hi
        have hspec := Classical.choose_spec (Finset.mem_filter.mp hi).2
        simp only [S_C, Finset.mem_filter, Finset.mem_univ, true_and, hspec, Fin.val_castAdd]
        exact i.isLt
      · intro i₁ hi₁ i₂ hi₂ h
        have hs1 := Classical.choose_spec (Finset.mem_filter.mp hi₁).2
        have hs2 := Classical.choose_spec (Finset.mem_filter.mp hi₂).2
        rw [h] at hs1
        exact Fin.castAdd_injective t m (hs1.symm.trans hs2)
      · intro a ha
        simp only [S_C, Finset.mem_filter, Finset.mem_univ, true_and] at ha
        let i : Fin t := ⟨(idx a).val, ha⟩
        have hcast : idx a = Fin.castAdd m i := Fin.ext rfl
        have hi : i ∈ IC := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨a, hcast⟩⟩
        refine ⟨i, hi, ?_⟩
        exact idx.injective ((Classical.choose_spec (Finset.mem_filter.mp hi).2).trans hcast.symm)
    have hJD : #JD = #S_D := by
      refine Finset.card_bij (fun j hj => Classical.choose (Finset.mem_filter.mp hj).2) ?_ ?_ ?_
      · intro j hj
        have hspec := Classical.choose_spec (Finset.mem_filter.mp hj).2
        simp only [S_D, Finset.mem_filter, Finset.mem_univ, true_and, hspec, Fin.val_natAdd]
        omega
      · intro j₁ hj₁ j₂ hj₂ h
        have hs1 := Classical.choose_spec (Finset.mem_filter.mp hj₁).2
        have hs2 := Classical.choose_spec (Finset.mem_filter.mp hj₂).2
        rw [h] at hs1
        exact Fin.natAdd_injective m t (hs1.symm.trans hs2)
      · intro a ha
        simp only [S_D, Finset.mem_filter, Finset.mem_univ, true_and] at ha
        let j : Fin m := ⟨(idx a).val - t, by omega⟩
        have hnat : idx a = Fin.natAdd t j := Fin.ext (by simp [j]; omega)
        have hj : j ∈ JD := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨a, hnat⟩⟩
        refine ⟨j, hj, ?_⟩
        exact idx.injective ((Classical.choose_spec (Finset.mem_filter.mp hj).2).trans hnat.symm)
    have hdisj : Disjoint S_C S_D := by
      rw [Finset.disjoint_filter]
      intro a _ h1 h2
      omega
    have hunion : S_C ∪ S_D = Finset.univ := by
      ext a
      simp only [S_C, S_D, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      exact iff_true_intro (lt_or_ge (idx a).val t)
    rw [hIC, hJD, ← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
  -- Define target bits `αC` on `IC` and `αD` on `JD`.
  let αC : Fin t → Bool := fun i =>
    if h : ∃ a : Fin k, idx a = Fin.castAdd m i then α (Classical.choose h) else false
  let αD : Fin m → Bool := fun j =>
    if h : ∃ a : Fin k, idx a = Fin.natAdd t j then α (Classical.choose h) else false
  -- Rewrite the event probability as `#E / 2^t`.
  let E : Finset (Fin t → Bool) :=
    Finset.univ.filter fun x =>
      (∀ i ∈ IC, x i = αC i) ∧
      (∀ j ∈ JD, nwGeneratorWithNeg D (Cslib.majority ℓ) neg x j = αD j)
  have hprob_eq :
      ((nwJointDist D (Cslib.majority ℓ) neg).toOuterMeasure {y | ∀ a, y (idx a) = α a}).toReal =
        (#E : ℝ) / (2 : ℝ) ^ t := by
    rw [nwJointDist_toOuterMeasure_toReal]
    congr 1
    exact_mod_cast congrArg Finset.card (by
      ext x
      simp only [E, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hx
        refine ⟨fun i hi => ?_, fun j hj => ?_⟩
        · have hex := (Finset.mem_filter.mp hi).2
          have hspec := Classical.choose_spec hex
          have hx' := hx (Classical.choose hex)
          rw [hspec, Fin.append_left] at hx'
          simpa [αC, hex] using hx'
        · have hex := (Finset.mem_filter.mp hj).2
          have hspec := Classical.choose_spec hex
          have hx' := hx (Classical.choose hex)
          rw [hspec, Fin.append_right] at hx'
          simpa [αD, hex] using hx'
      · rintro ⟨hC, hD⟩ a
        by_cases hlt : (idx a).val < t
        · let i : Fin t := ⟨(idx a).val, hlt⟩
          have hcast : idx a = Fin.castAdd m i := Fin.ext rfl
          have hex : ∃ a', idx a' = Fin.castAdd m i := ⟨a, hcast⟩
          have ha_eq : Classical.choose hex = a :=
            idx.injective ((Classical.choose_spec hex).trans hcast.symm)
          have hi : i ∈ IC := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hex⟩
          have hCi := hC i hi
          simp only [αC, dite_eq_left hex, ha_eq] at hCi
          rw [hcast, Fin.append_left]
          exact hCi
        · let j : Fin m := ⟨(idx a).val - t, by omega⟩
          have hnat : idx a = Fin.natAdd t j := Fin.ext (by simp [j]; omega)
          have hex : ∃ a', idx a' = Fin.natAdd t j := ⟨a, hnat⟩
          have ha_eq : Classical.choose hex = a :=
            idx.injective ((Classical.choose_spec hex).trans hnat.symm)
          have hj : j ∈ JD := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hex⟩
          have hDj := hD j hj
          simp only [αD, dite_eq_left hex, ha_eq] at hDj
          rw [hnat, Fin.append_right]
          exact hDj)
  -- Induct on `js ⊆ JD` to bound the event cardinality.
  have hind : ∀ js : Finset (Fin m), js ⊆ JD →
      let Ejs : Finset (Fin t → Bool) :=
        Finset.univ.filter fun x =>
          (∀ i ∈ IC, x i = αC i) ∧
          (∀ j ∈ js, nwGeneratorWithNeg D (Cslib.majority ℓ) neg x j = αD j)
      (2 : ℝ) ^ t * (2 : ℝ)⁻¹ ^ #IC * (1 / 2 - δ) ^ #js ≤ (#Ejs : ℝ) ∧
        (#Ejs : ℝ) ≤ (2 : ℝ) ^ t * (2 : ℝ)⁻¹ ^ #IC * (1 / 2 + δ) ^ #js := by
    intro js
    induction js using Finset.induction_on with
    | empty =>
      intro _
      simp only [Finset.notMem_empty, false_implies, implies_true, and_true, Finset.card_empty,
        pow_zero, mul_one]
      let E0 : Finset (Fin t → Bool) := Finset.univ.filter fun x => ∀ i ∈ IC, x i = αC i
      have hcard0 : #E0 = 2 ^ (t - #IC) := by
        let comp : Finset (Fin t) := Finset.univ \ IC
        have hcard_comp : #comp = t - #IC := by
          dsimp only [comp]
          rw [Finset.card_sdiff_of_subset (Finset.subset_univ IC), Finset.card_univ,
            Fintype.card_fin]
        have hbij : #E0 = Fintype.card (comp → Bool) := by
          rw [← Finset.card_univ]
          refine Finset.card_bij (fun x _ i => x i.1) (fun _ _ => Finset.mem_univ _) ?_ ?_
          · intro x₁ hx₁ x₂ hx₂ h
            simp only [E0, Finset.mem_filter, Finset.mem_univ, true_and] at hx₁ hx₂
            ext i
            by_cases hi : i ∈ IC
            · rw [hx₁ i hi, hx₂ i hi]
            · exact congrFun h ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩⟩
          · intro u _
            refine ⟨fun i => if hi : i ∈ IC then αC i else u ⟨i, Finset.mem_sdiff.mpr
              ⟨Finset.mem_univ _, hi⟩⟩, ?_, ?_⟩
            · simp only [E0, Finset.mem_filter, Finset.mem_univ, true_and]
              intro i hi
              simp [hi]
            · ext ⟨i, hi⟩
              have hnot : i ∉ IC := (Finset.mem_sdiff.mp hi).2
              simp [hnot]
        rw [hbij, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, hcard_comp]
      have hIC_le : #IC ≤ t := by
        calc #IC ≤ #(Finset.univ : Finset (Fin t)) := Finset.card_le_card (Finset.subset_univ _)
          _ = t := by simp
      have hpow_eq : (2 : ℝ) ^ t * (2 : ℝ)⁻¹ ^ #IC = ((2 ^ (t - #IC) : ℕ) : ℝ) := by
        rw [Nat.cast_pow, Nat.cast_ofNat, inv_pow, ← pow_sub₀ (2 : ℝ) (by norm_num) hIC_le]
      change (2 : ℝ) ^ t * (2 : ℝ)⁻¹ ^ #IC ≤ (#E0 : ℝ) ∧ (#E0 : ℝ) ≤ (2 : ℝ) ^ t * (2 : ℝ)⁻¹ ^ #IC
      rw [hcard0, hpow_eq]
      exact ⟨le_rfl, le_rfl⟩
    | @insert j₀ js hj₀ ih =>
      intro hsub
      have hjs_sub : js ⊆ JD := (Finset.subset_insert j₀ js).trans hsub
      obtain ⟨hlo_prev, hhi_prev⟩ := ih hjs_sub
      have hstep := card_nw_cond_step D neg IC αC js αD j₀ hj₀
      let A : Finset (Fin t) := IC ∪ js.biUnion D.block
      let s : ℕ := #(D.block j₀ ∩ A)
      -- Bound `s ≤ p * k - 1` (since `j₀ ∉ js`, `j₀ ∈ JD`, so `#IC + #js < k`).
      have hs_le : s ≤ p * k - 1 := by
        have hjs_lt : #IC + #js < k := by
          have hcard_ins : #(insert j₀ js) ≤ #JD := Finset.card_le_card hsub
          rw [Finset.card_insert_of_notMem hj₀] at hcard_ins
          omega
        have hinter_sub :
            D.block j₀ ∩ A ⊆ (D.block j₀ ∩ IC) ∪ js.biUnion (fun j => D.block j₀ ∩ D.block j) := by
          intro x hx
          rcases Finset.mem_inter.mp hx with ⟨hx0, hxA⟩
          rcases Finset.mem_union.mp hxA with hxIC | hxU
          · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hx0, hxIC⟩)
          · rcases Finset.mem_biUnion.mp hxU with ⟨j, hj, hxj⟩
            exact Finset.mem_union_right _
              (Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_inter.mpr ⟨hx0, hxj⟩⟩)
        have hs1 : s ≤ #IC + #js * p := by
          calc s ≤ #((D.block j₀ ∩ IC) ∪ js.biUnion (fun j => D.block j₀ ∩ D.block j)) :=
                Finset.card_le_card hinter_sub
            _ ≤ #(D.block j₀ ∩ IC) + #(js.biUnion fun j => D.block j₀ ∩ D.block j) :=
                Finset.card_union_le _ _
            _ ≤ #IC + ∑ j ∈ js, #(D.block j₀ ∩ D.block j) :=
                add_le_add (Finset.card_le_card Finset.inter_subset_right)
                  Finset.card_biUnion_le
            _ ≤ #IC + ∑ _j ∈ js, p :=
                add_le_add le_rfl (Finset.sum_le_sum fun j hj =>
                  D.card_inter_le (fun heq => hj₀ (heq ▸ hj)))
            _ = #IC + #js * p := by rw [Finset.sum_const, smul_eq_mul]
        have hp_le : #IC ≤ #IC * p := Nat.le_mul_of_pos_right _ hp
        have hpk_pos : 1 ≤ p * k := Nat.mul_pos hp hk_pos
        have : #IC + #js * p ≤ (#IC + #js) * p := by rw [add_mul]; omega
        have : (#IC + #js) * p ≤ (k - 1) * p := Nat.mul_le_mul_right p (by omega)
        have : (k - 1) * p ≤ p * k - 1 := by
          rw [mul_comm, Nat.mul_sub_left_distrib, mul_one]
          omega
        omega
      have hs_add_le : (s + 1 : ℝ) ≤ (p : ℝ) * (k : ℝ) := by
        have : s + 1 ≤ p * k := by
          have : 1 ≤ p * k := Nat.mul_pos hp hk_pos
          omega
        exact_mod_cast this
      have hδs_le : (s + 1 : ℝ) / (2 * Real.sqrt (ℓ - s + 1 : ℝ)) ≤ δ := by
        have hsub_ge : (ℓ : ℝ) / 2 ≤ (ℓ - s + 1 : ℝ) := by
          have hs_le_pk : s ≤ p * k := by omega
          have hcast : ((ℓ - s : ℕ) : ℝ) = (ℓ : ℝ) - (s : ℝ) := Nat.cast_sub (by omega)
          have h2s : (2 * s : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast (show 2 * s ≤ ℓ by omega)
          linarith
        have hsqrt_ge : Real.sqrt (ℓ : ℝ) / Real.sqrt 2 ≤ Real.sqrt (ℓ - s + 1 : ℝ) := by
          rw [← Real.sqrt_div hℓ_pos.le]
          exact Real.sqrt_le_sqrt hsub_ge
        have hden_ge : Real.sqrt (ℓ : ℝ) / Real.sqrt 2 * 2 ≤ 2 * Real.sqrt (ℓ - s + 1 : ℝ) := by
          linarith
        have hden_eq : Real.sqrt (ℓ : ℝ) / Real.sqrt 2 * 2 = Real.sqrt 2 * Real.sqrt (ℓ : ℝ) := by
          have h2 : Real.sqrt 2 ≠ 0 := by positivity
          field_simp [h2]
          rw [Real.sq_sqrt (by norm_num)]
        calc (s + 1 : ℝ) / (2 * Real.sqrt (ℓ - s + 1 : ℝ))
            ≤ ((p : ℝ) * (k : ℝ)) / (2 * Real.sqrt (ℓ - s + 1 : ℝ)) :=
              div_le_div_of_nonneg_right hs_add_le (by positivity)
          _ ≤ ((p : ℝ) * (k : ℝ)) / (Real.sqrt 2 * Real.sqrt (ℓ : ℝ)) :=
              div_le_div_of_nonneg_left (by positivity) (by positivity) (hden_eq ▸ hden_ge)
          _ ≤ δ := by
              dsimp only [δ]
              have hsq2 : (1 : ℝ) ≤ Real.sqrt 2 * Real.sqrt 2 := by
                rw [Real.mul_self_sqrt (by norm_num)]; norm_num
              have hden_pos : (0 : ℝ) < Real.sqrt 2 * Real.sqrt (ℓ : ℝ) := by positivity
              rw [div_le_div_iff₀ hden_pos hsqrt_ℓ_pos]
              have : (p : ℝ) * (k : ℝ) * Real.sqrt (ℓ : ℝ) * 1 ≤
                  (p : ℝ) * (k : ℝ) * Real.sqrt (ℓ : ℝ) * (Real.sqrt 2 * Real.sqrt 2) :=
                mul_le_mul_of_nonneg_left hsq2 (by positivity)
              linarith
      -- Rewrite `E_{insert j₀ js}` as `next`.
      have hEeq :
          (Finset.univ.filter fun x =>
            (∀ i ∈ IC, x i = αC i) ∧
            (∀ j ∈ insert j₀ js, nwGeneratorWithNeg D (Cslib.majority ℓ) neg x j = αD j)) =
          ((Finset.univ.filter fun x =>
            (∀ i ∈ IC, x i = αC i) ∧
            (∀ j ∈ js, nwGeneratorWithNeg D (Cslib.majority ℓ) neg x j = αD j)).filter fun x =>
            nwGeneratorWithNeg D (Cslib.majority ℓ) neg x j₀ = αD j₀) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          forall_eq_or_imp]
        tauto
      rw [hEeq, Finset.card_insert_of_notMem hj₀, pow_succ]
      have hhalf_sub : 0 ≤ 1 / 2 - δ := by linarith
      constructor
      · calc (2 : ℝ) ^ t * (2 : ℝ)⁻¹ ^ #IC * ((1 / 2 - δ) ^ #js * (1 / 2 - δ))
            = (1 / 2 - δ) * ((2 : ℝ) ^ t * (2 : ℝ)⁻¹ ^ #IC * (1 / 2 - δ) ^ #js) := by ring
          _ ≤ (1 / 2 - δ) * _ := mul_le_mul_of_nonneg_left hlo_prev hhalf_sub
          _ ≤ (1 / 2 - (s + 1 : ℝ) / (2 * Real.sqrt (ℓ - s + 1 : ℝ))) * _ :=
              mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
          _ ≤ _ := hstep.1
      · calc _ ≤ (1 / 2 + (s + 1 : ℝ) / (2 * Real.sqrt (ℓ - s + 1 : ℝ))) * _ := hstep.2
          _ ≤ (1 / 2 + δ) * _ :=
              mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
          _ ≤ (1 / 2 + δ) * ((2 : ℝ) ^ t * (2 : ℝ)⁻¹ ^ #IC * (1 / 2 + δ) ^ #js) :=
              mul_le_mul_of_nonneg_left hhi_prev (by positivity)
          _ = (2 : ℝ) ^ t * (2 : ℝ)⁻¹ ^ #IC * ((1 / 2 + δ) ^ #js * (1 / 2 + δ)) := by ring
  obtain ⟨hloE, hhiE⟩ := hind JD Subset.rfl
  rw [hprob_eq]
  have h2t_pos : (0 : ℝ) < (2 : ℝ) ^ t := by positivity
  have h2k_eq : (2 : ℝ)⁻¹ ^ #IC * (2 : ℝ)⁻¹ ^ #JD = (2 : ℝ)⁻¹ ^ k := by
    rw [← pow_add, hcard_split]
  have hpow_lo : (1 - 2 * δ) ^ #JD ≤ ((#E : ℝ) / (2 : ℝ) ^ t) / (2 : ℝ)⁻¹ ^ k := by
    have h1 : (2 : ℝ)⁻¹ ^ #IC * (1 / 2 - δ) ^ #JD ≤ (#E : ℝ) / (2 : ℝ) ^ t := by
      rw [le_div_iff₀ h2t_pos]
      linarith
    have h2 : (1 / 2 - δ) ^ #JD = (2 : ℝ)⁻¹ ^ #JD * (1 - 2 * δ) ^ #JD := by
      rw [← mul_pow]
      congr 1
      ring
    rw [h2, ← mul_assoc, h2k_eq] at h1
    exact (le_div_iff₀ (by positivity)).mpr (by linarith)
  have hpow_hi : ((#E : ℝ) / (2 : ℝ) ^ t) / (2 : ℝ)⁻¹ ^ k ≤ (1 + 2 * δ) ^ #JD := by
    have h1 : (#E : ℝ) / (2 : ℝ) ^ t ≤ (2 : ℝ)⁻¹ ^ #IC * (1 / 2 + δ) ^ #JD := by
      rw [div_le_iff₀ h2t_pos]
      linarith
    have h2 : (1 / 2 + δ) ^ #JD = (2 : ℝ)⁻¹ ^ #JD * (1 + 2 * δ) ^ #JD := by
      rw [← mul_pow]
      congr 1
      ring
    rw [h2, ← mul_assoc, h2k_eq] at h1
    exact (div_le_iff₀ (by positivity)).mpr (by linarith)
  have hJD_le : (#JD : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show #JD ≤ k by omega)
  have hJD_mul : (#JD : ℝ) * (2 * δ) ≤ 1 := by
    calc (#JD : ℝ) * (2 * δ) ≤ (k : ℝ) * (2 * δ) :=
          mul_le_mul_of_nonneg_right hJD_le (by positivity)
      _ = 2 * (k : ℝ) * δ := by ring
      _ ≤ 1 := h2kδ
  have hε_eq :
      4 * Real.sqrt 2 * (p : ℝ) * (k : ℝ) ^ 2 / Real.sqrt (ℓ : ℝ) = 4 * (k : ℝ) * δ := by
    dsimp only [δ]
    ring
  rw [hε_eq]
  constructor
  · have hbern := one_sub_mul_le_pow (by positivity) h2δ_le1 #JD
    have hcmp : (#JD : ℝ) * (2 * δ) ≤ 4 * (k : ℝ) * δ := by nlinarith
    linarith
  · have hexp := one_add_pow_le_one_add_two_mul (x := 2 * δ) (by positivity) hJD_mul
    have hcmp : 2 * ((#JD : ℝ) * (2 * δ)) ≤ 4 * (k : ℝ) * δ := by nlinarith
    linarith


end CslibFrontier.Crypto.Primitives.PRG.NisanWigderson
