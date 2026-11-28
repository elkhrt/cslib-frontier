module

public import Cslib.Computability.Circuit.Boolean.Basic
public import CslibFrontier.Computability.Circuit.Frontier.Nondeterministic
public import CslibFrontier.Foundations.Data.BitString.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Cslib.Computability.Circuit.Boolean.Synthesis
import Cslib.Computability.Circuit.Composition
import Cslib.Foundations.Data.Polynomial.Monotone
import CslibFrontier.Computability.Circuit.Boolean.AtLeast
import CslibFrontier.Computability.Circuit.Boolean.Substitution
import CslibFrontier.Computability.Circuit.Synthesis
import CslibFrontier.Foundations.Data.Nat.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Demi-Bit Generators, Sublinear Parallel Stretching, and Shift Covering

This module formalizes non-uniform stretching circuit generators (`PPolyGenerator`),
nondeterministic demi-hardness against nondeterministic Boolean circuits (`demiHardness`) and the
Demi-Bit Conjecture (`DemiBitConjecture`), parallel concatenation stretching of demi-bit generators
from one-bit stretch `n + 1` to logarithmic (and sublinear) stretch `n + ⌈log₂ n⌉ + 1` preserving
subexponential demi-hardness (`exists_stretched_demiBit_clog`), and probabilistic XOR shift-covering
bound (`card_xorShiftCover_ge`), proved under standard Lean axioms.

Given a stretching map `g : BitString n → BitString m` (`n < m`), its demi-hardness is the least
positive integer `s` for which some nondeterministic De Morgan circuit of size at most `s` decides
a subset of `(Set.range g)ᶜ` of uniform density at least `s⁻¹`. Taking `k` independent parallel
copies `x ↦ (f(x₁), …, f(xₖ))` converts any nondeterministic range-avoiding distinguisher either
by hardwiring a range block (induction on `k`) or by an empirical monotone threshold over
independent random suffixes (via elementary exponential-moment Chernoff bounds), yielding a
nondeterministic distinguisher against a single copy `f`.

## Main definitions

* `CslibFrontier.Computability.PPolyGenerator`: a family of stretching maps
  `BitString n → BitString (m n)` with `n < m n` computed by polynomial-size De Morgan circuits.
* `CslibFrontier.Computability.IsDemiDistinguisher`: existence of a size-`≤ s` nondeterministic De
  Morgan circuit deciding a subset of `(Set.range g)ᶜ` of measure at least `s⁻¹`.
* `CslibFrontier.Computability.demiHardness`: Rudich's demi-hardness of `g : BitString n → BitString
  m`.
* `CslibFrontier.Computability.DemiBitConjecture`: Rudich's Demi-Bit Conjecture asserting the
  existence of a `P/poly` generator of stretch `m(n) = n + 1` with demi-hardness at least `2 ^ (n ^
  ε)` for some `ε > 0`.
* `CslibFrontier.Computability.bitXor`: bitwise exclusive-or on `BitString m`.
* `CslibFrontier.Computability.CoversByXorShifts`: a tuple of shifts `s : Fin r → BitString m`
  covers `BitString m` by translates `s_j ⊕ A`.

## Main results

* `CslibFrontier.Computability.demiHardness_spec`,
  `CslibFrontier.Computability.two_le_demiHardness`,
  `CslibFrontier.Computability.density_lt_inv_of_lt_demiHardness`: attainment, non-degeneracy, and
  density upper bound below `demiHardness`.
* `CslibFrontier.Computability.exists_nondet_single_of_parallel`: parallel-concatenation
  demi-hardness reduction from `k` independent copies of `f : BitString r → BitString (r + 1)` to
  one copy.
* `CslibFrontier.Computability.exists_stretched_demiBit_clog`: `DemiBitConjecture` yields a `P/poly`
  generator of stretch `m(n) = n + ⌈log₂ n⌉ + 1` with demi-hardness at least `2 ^ (n ^ δ)` for
  some `δ > 0` (and hence super-polynomial demi-hardness `n ^ ω(1)`).
* `CslibFrontier.Computability.card_xorShiftCover_ge`: XOR shift-covering probability bound
  `Pr_{s₁,…,sᵣ}[⋃_j (s_j ⊕ A) = {0,1}^m] ≥ 1 - ρ ^ r * 2 ^ m` whenever `|A| / 2 ^ m > 1 - ρ`.


-/

public section

namespace CslibFrontier.Computability

open Filter Finset
open Cslib Cslib.Circuits Cslib.Circuits.Boolean

/-! ### Non-uniform stretching generators and demi-hardness -/

/-- A **`P/poly` stretching generator** with output-length function `m : ℕ → ℕ`: for each input
length `n`, a De Morgan circuit `circuit n` maps `n` bits to `m n > n` bits and has gate count
bounded by a fixed polynomial in `m n`. -/
structure PPolyGenerator (m : ℕ → ℕ) where
  /-- The De Morgan circuit computing the generator on `n`-bit inputs. -/
  circuit : (n : ℕ) → Circuit signature n (m n)
  /-- The generator is strictly stretching at every input length. -/
  stretch : ∀ n, n < m n
  /-- The size of `circuit n` is bounded by a polynomial in the output length `m n`. -/
  size_poly : ∃ p : Polynomial ℕ, ∀ n, (circuit n).size ≤ p.eval (m n)

/-- The `n`-th stretching Boolean map `BitString n → BitString (m n)` computed by `g`. -/
@[expose]
def PPolyGenerator.eval {m : ℕ → ℕ} (g : PPolyGenerator m) (n : ℕ) :
    BitString n → BitString (m n) :=
  (g.circuit n).eval interpretation

/-- Evaluation of `g.eval n` equals De Morgan evaluation of `g.circuit n`. -/
@[simp]
theorem PPolyGenerator.eval_circuit {m : ℕ → ℕ} (g : PPolyGenerator m) (n : ℕ) (x : BitString n) :
    (g.circuit n).eval interpretation x = g.eval n x :=
  rfl

/-- `s` is a **demi-distinguishing parameter** for `g : BitString n → BitString m` if `s ≥ 1` and
some nondeterministic De Morgan circuit `D` on `m` inputs (and `k` nondeterministic witness bits)
of gate size at most `s` decides a subset `S ⊆ (Set.range g)ᶜ` of uniform measure
`|S| / 2 ^ m ≥ s⁻¹`. -/
@[expose]
def IsDemiDistinguisher {n m : ℕ} (g : BitString n → BitString m) (s : ℕ) : Prop :=
  1 ≤ s ∧ ∃ (k : ℕ) (D : Circuit signature (m + k) 1) (S : Set (BitString m)),
    D.size ≤ s ∧ D.NondeterministicDecides interpretation {true} S ∧
      Disjoint S (Set.range g) ∧ (s : ℝ)⁻¹ ≤ (S.ncard : ℝ) / (2 : ℝ) ^ m

/-- Monotonicity of `IsDemiDistinguisher` in the size-and-inverse-density threshold `s`. -/
theorem IsDemiDistinguisher.mono {n m s t : ℕ} {g : BitString n → BitString m}
    (h : IsDemiDistinguisher g s) (hst : s ≤ t) : IsDemiDistinguisher g t := by
  obtain ⟨hs1, k, D, S, hsz, hdec, hdisj, hmeas⟩ := h
  refine ⟨hs1.trans hst, k, D, S, hsz.trans hst, hdec, hdisj, ?_⟩
  exact (inv_anti₀ (by exact_mod_cast hs1) (by exact_mod_cast hst)).trans hmeas

/-- Every strictly stretching map `g : BitString n → BitString m` (`n < m`) admits a finite
demi-distinguisher: a singleton `{y₀}` outside `Set.range g` is decided by a minterm circuit. -/
theorem exists_isDemiDistinguisher {n m : ℕ} (hnm : n < m) (g : BitString n → BitString m) :
    ∃ s, IsDemiDistinguisher g s := by
  classical
  have hcard : #(univ.image g) < #(univ : Finset (BitString m)) :=
    calc #(univ.image g) ≤ #(univ : Finset (BitString n)) := card_image_le
      _ = 2 ^ n := by rw [card_univ, BitString.card]
      _ < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) hnm
      _ = #(univ : Finset (BitString m)) := by rw [card_univ, BitString.card]
  obtain ⟨y₀, -, hy₀⟩ := exists_mem_notMem_of_card_lt_card hcard
  have hy₀' : y₀ ∉ Set.range g := fun ⟨x, hx⟩ => hy₀ (mem_image.2 ⟨x, mem_univ x, hx⟩)
  obtain ⟨D, hD, hDsz⟩ := (synthesis_minterm (n := m) id y₀).exists_circuit
  have hdec : D.Decides interpretation {true} {y₀} := fun x => by
    have hx := congrFun (hD x) 0
    simp only [single_apply, Set.mem_singleton_iff, id_eq] at hx ⊢
    rw [hx, decide_eq_true_eq]
  set s := max (2 * m + 1) (2 ^ m)
  refine ⟨s, (Nat.one_le_two_pow).trans (le_max_right _ _), 0, D, {y₀},
    hDsz.trans (le_max_left _ _), hdec.nondeterministicDecides,
    Set.disjoint_singleton_left.2 hy₀', ?_⟩
  rw [Set.ncard_singleton, Nat.cast_one, one_div]
  exact inv_anti₀ (by positivity) (by exact_mod_cast le_max_right (2 * m + 1) (2 ^ m))

/-- **Rudich's demi-hardness** of a map `g : BitString n → BitString m`: the minimal size `s ≥ 1`
of a nondeterministic De Morgan circuit defining a subset of `(Set.range g)ᶜ` of uniform measure
at least `s⁻¹`. -/
noncomputable def demiHardness {n m : ℕ} (g : BitString n → BitString m) : ℕ :=
  sInf {s | IsDemiDistinguisher g s}

/-- For a stretching map (`n < m`), `demiHardness g` is attained as a valid demi-distinguisher. -/
theorem demiHardness_spec {n m : ℕ} (hnm : n < m) (g : BitString n → BitString m) :
    IsDemiDistinguisher g (demiHardness g) :=
  Nat.sInf_mem (s := {s | IsDemiDistinguisher g s}) (exists_isDemiDistinguisher hnm g)

/-- Any valid demi-distinguisher for `g` has parameter at least `demiHardness g`. -/
theorem demiHardness_le {n m s : ℕ} {g : BitString n → BitString m}
    (h : IsDemiDistinguisher g s) : demiHardness g ≤ s :=
  Nat.sInf_le h

/-- Every strictly stretching map `g : BitString n → BitString m` has `demiHardness g ≥ 2`, since
no subset avoiding the nonempty range `Set.range g` can have density `1`. -/
theorem two_le_demiHardness {n m : ℕ} (hnm : n < m) (g : BitString n → BitString m) :
    2 ≤ demiHardness g := by
  obtain ⟨hs1, k, D, S, -, -, hdisj, hmeas⟩ := demiHardness_spec hnm g
  by_contra hlt
  have hs : demiHardness g = 1 := by omega
  rw [hs, Nat.cast_one, inv_one, le_div_iff₀ (by positivity), one_mul] at hmeas
  have hnot : g (fun _ => false) ∉ S :=
    Set.disjoint_right.1 hdisj ⟨fun _ => false, rfl⟩
  have hlt_card : S.ncard < (Set.univ : Set (BitString m)).ncard :=
    Set.ncard_lt_ncard (Set.ssubset_univ_iff.2 fun h => hnot (h ▸ Set.mem_univ _)) Set.finite_univ
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, BitString.card] at hlt_card
  have : (S.ncard : ℝ) < (2 : ℝ) ^ m := by exact_mod_cast hlt_card
  linarith

/-- **Density bound below demi-hardness.** If `1 ≤ s < demiHardness g` (with `n < m`), then every
subset `S ⊆ (Set.range g)ᶜ` nondeterministically decided by a De Morgan circuit of size at most
`s` has uniform density strictly less than `s⁻¹`. -/
theorem density_lt_inv_of_lt_demiHardness {n m s k : ℕ} {g : BitString n → BitString m}
    (hs1 : 1 ≤ s) (hs : s < demiHardness g) {D : Circuit signature (m + k) 1}
    (hD : D.size ≤ s) {S : Set (BitString m)}
    (hdec : D.NondeterministicDecides interpretation {true} S)
    (hdisj : Disjoint S (Set.range g)) :
    (S.ncard : ℝ) / (2 : ℝ) ^ m < (s : ℝ)⁻¹ := by
  by_contra hge
  push Not at hge
  exact not_lt_of_ge (demiHardness_le ⟨hs1, k, D, S, hD, hdec, hdisj, hge⟩) hs

/-- **Rudich's Demi-Bit Conjecture**: there exists a `P/poly`
generator `g` with one-bit stretch `m(n) = n + 1` and a constant `ε > 0` such that
`demiHardness (g.eval n) ≥ 2 ^ (n ^ ε)` for all sufficiently large `n`. -/
@[expose]
def DemiBitConjecture : Prop :=
  ∃ (g : PPolyGenerator (fun n => n + 1)) (ε : ℝ),
    0 < ε ∧ ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ ((n : ℝ) ^ ε) ≤ (demiHardness (g.eval n) : ℝ)

/-! ### Elementary exponential-moment Chernoff bounds on finite product spaces -/

/-- Exact exponential moment generating function of a sum of `t` independent indicators over a
finite type `Ω`. -/
private theorem sum_pow_count_mem {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (E : Finset Ω)
    (a : ℝ) : ∀ t : ℕ,
      (∑ z : Fin t → Ω, a ^ #{j : Fin t | z j ∈ E}) =
        ((#E : ℝ) * a + ((Fintype.card Ω : ℝ) - #E)) ^ t
  | 0 => by simp
  | t + 1 => by
    have hstep (x : Ω) (z : Fin t → Ω) :
        a ^ #{j : Fin (t + 1) | Fin.cons (α := fun _ => Ω) x z j ∈ E} =
          (if x ∈ E then a else 1) * a ^ #{j : Fin t | z j ∈ E} := by
      simp only [card_filter, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      by_cases hx : x ∈ E <;> simp [hx, pow_add]
    have hsum_step (x : Ω) :
        (∑ z : Fin t → Ω, a ^ #{j : Fin (t + 1) | Fin.cons (α := fun _ => Ω) x z j ∈ E}) =
          (if x ∈ E then a else 1) * ((#E : ℝ) * a + ((Fintype.card Ω : ℝ) - #E)) ^ t := by
      simp_rw [hstep x, ← mul_sum, sum_pow_count_mem E a t]
    have hsum_eq : (∑ p : Ω × (Fin t → Ω),
        a ^ #{j : Fin (t + 1) | Fin.consEquiv (fun _ => Ω) p j ∈ E}) =
        (∑ x : Ω, if x ∈ E then a else 1) *
          ((#E : ℝ) * a + ((Fintype.card Ω : ℝ) - #E)) ^ t := by
      rw [Fintype.sum_prod_type, sum_mul]
      exact sum_congr rfl fun x _ => hsum_step x
    rw [← (Fin.consEquiv fun _ : Fin (t + 1) => Ω).sum_comp, hsum_eq, pow_succ,
      mul_comm (((#E : ℝ) * a + _) ^ t)]
    congr 1
    rw [sum_ite, filter_not, filter_mem_eq_inter, univ_inter, sum_const, sum_const,
      card_sdiff_of_subset (subset_univ E), card_univ]
    have hle : #E ≤ Fintype.card Ω := card_le_univ E
    rw [nsmul_eq_mul, nsmul_eq_mul, mul_one, Nat.cast_sub hle]

/-- Normalized exponential moment `𝔼[a^X] = (1 + p (a - 1))^t` for `p = |E| / |Ω|`. -/
private theorem avg_pow_count_mem {Ω : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    (E : Finset Ω) (a : ℝ) (t : ℕ) :
    (∑ z : Fin t → Ω, a ^ #{j : Fin t | z j ∈ E}) / (Fintype.card Ω : ℝ) ^ t =
      (1 + (#E : ℝ) / (Fintype.card Ω : ℝ) * (a - 1)) ^ t := by
  have hN : (0 : ℝ) < Fintype.card Ω := Nat.cast_pos.2 Fintype.card_pos
  rw [sum_pow_count_mem, ← div_pow]
  congr 1
  field_simp
  ring

private theorem log_five_fourths_gt : (2 : ℝ) / 9 < Real.log (5 / 4) := by
  rw [div_lt_iff₀ (by norm_num), mul_comm, show (9 : ℝ) = ((9 : ℕ) : ℝ) by norm_num,
    ← Real.log_pow, Real.lt_log_iff_exp_lt (by positivity)]
  have he := Real.exp_one_lt_d9
  rw [show Real.exp 2 = Real.exp 1 * Real.exp 1 by rw [← Real.exp_add]; norm_num]
  have h0 : 0 < Real.exp 1 := Real.exp_pos 1
  nlinarith [show (2.7182818286 : ℝ) * 2.7182818286 < (5 / 4 : ℝ) ^ 9 by norm_num]

private theorem log_six_fifths_lt : Real.log (6 / 5) < (3 : ℝ) / 16 := by
  rw [lt_div_iff₀ (by norm_num), mul_comm, show (16 : ℝ) = ((16 : ℕ) : ℝ) by norm_num,
    ← Real.log_pow, Real.log_lt_iff_lt_exp (by positivity)]
  have he := Real.exp_one_gt_d9
  rw [show Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num]
  nlinarith [show (6 / 5 : ℝ) ^ 16 < (2.7182818283 : ℝ) ^ 3 by norm_num,
    sq_nonneg (Real.exp 1 - 2.7182818283)]

private theorem log_le_mul_rpow_eventually {r c : ℝ} (hr : 0 < r) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, Real.log x ≤ c * x ^ r := by
  have ht := tendsto_rpow_atTop (show 0 < r / 2 by positivity)
  filter_upwards [ht.eventually (eventually_ge_atTop (2 / (r * c))), eventually_ge_atTop 1]
    with x hx hx1
  have hpos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have h1 : r / 2 * Real.log x ≤ x ^ (r / 2) := by
    rw [← Real.log_rpow hpos]
    linarith [Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hpos (r / 2))]
  have h2 : Real.log x ≤ 2 / r * x ^ (r / 2) := by
    rw [mul_comm, ← le_div_iff₀ (by positivity)] at h1
    exact h1.trans_eq (by field_simp)
  have h3 : 2 / r ≤ c * x ^ (r / 2) := by
    have hrc := (div_le_iff₀ (by positivity : 0 < r * c)).1 hx
    rw [div_le_iff₀ hr]; nlinarith
  calc Real.log x ≤ 2 / r * x ^ (r / 2) := h2
    _ ≤ c * x ^ (r / 2) * x ^ (r / 2) := mul_le_mul_of_nonneg_right h3 (by positivity)
    _ = c * x ^ r := by rw [mul_assoc, ← Real.rpow_add hpos]; congr 2; ring

/-- Upper-tail Chernoff bound: if `|E| / |Ω| ≤ δ / 2`, the fraction of `t`-tuples hitting `E` at
least `(5 / 8) * δ * t` times is at most `exp (-δ * t / 72)`. -/
private theorem card_count_ge_le {Ω : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    (E : Finset Ω) {δ : ℝ} (hδ : 0 < δ)
    (hp : (#E : ℝ) / (Fintype.card Ω : ℝ) ≤ δ / 2) (t : ℕ) :
    ((#{z : Fin t → Ω | 5 / 8 * δ * (t : ℝ) ≤ (#{j : Fin t | z j ∈ E} : ℝ)} : ℕ) : ℝ) /
      (Fintype.card Ω : ℝ) ^ t ≤ Real.exp (-(δ * (t : ℝ) / 72)) := by
  have hN : (0 : ℝ) < (Fintype.card Ω : ℝ) ^ t := pow_pos (Nat.cast_pos.2 Fintype.card_pos) t
  set bad := univ.filter fun z : Fin t → Ω =>
    5 / 8 * δ * (t : ℝ) ≤ (#{j : Fin t | z j ∈ E} : ℝ)
  have hmarkov : (#bad : ℝ) * Real.exp (5 / 8 * δ * (t : ℝ) * Real.log (5 / 4)) ≤
      ∑ z : Fin t → Ω, (5 / 4 : ℝ) ^ #{j : Fin t | z j ∈ E} := by
    calc (#bad : ℝ) * Real.exp (5 / 8 * δ * (t : ℝ) * Real.log (5 / 4))
        = ∑ _z ∈ bad, Real.exp (5 / 8 * δ * (t : ℝ) * Real.log (5 / 4)) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ z ∈ bad, (5 / 4 : ℝ) ^ #{j : Fin t | z j ∈ E} := by
          refine sum_le_sum fun z hz => ?_
          have hz' := (mem_filter.1 hz).2
          rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 5 / 4),
            mul_comm (Real.log (5 / 4))]
          exact Real.exp_le_exp.2
            (mul_le_mul_of_nonneg_right hz' (Real.log_pos (by norm_num)).le)
      _ ≤ ∑ z : Fin t → Ω, (5 / 4 : ℝ) ^ #{j : Fin t | z j ∈ E} :=
          sum_le_univ_sum_of_nonneg fun _ => by positivity
  have hmgf : (∑ z : Fin t → Ω, (5 / 4 : ℝ) ^ #{j : Fin t | z j ∈ E}) / (Fintype.card Ω : ℝ) ^ t ≤
      Real.exp (δ * (t : ℝ) / 8) := by
    rw [avg_pow_count_mem]
    calc (1 + (#E : ℝ) / (Fintype.card Ω : ℝ) * (5 / 4 - 1)) ^ t
        ≤ (1 + δ / 8) ^ t := pow_le_pow_left₀ (by positivity) (by linarith) t
      _ ≤ (Real.exp (δ / 8)) ^ t :=
          pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (δ / 8)]) t
      _ = Real.exp (δ * (t : ℝ) / 8) := by rw [← Real.exp_nat_mul]; congr 1; ring
  have h1 : (#bad : ℝ) / (Fintype.card Ω : ℝ) ^ t ≤
      Real.exp (δ * (t : ℝ) / 8 - 5 / 8 * δ * (t : ℝ) * Real.log (5 / 4)) := by
    rw [Real.exp_sub, le_div_iff₀ (Real.exp_pos _), div_mul_eq_mul_div]
    exact (div_le_div_of_nonneg_right hmarkov hN.le).trans hmgf
  refine h1.trans (Real.exp_le_exp.2 ?_)
  have hlog := log_five_fourths_gt
  have hdt : 0 ≤ δ * (t : ℝ) := by positivity
  nlinarith

/-- Lower-tail Chernoff bound: if `|E| / |Ω| ≥ (3 / 4) * δ`, the fraction of `t`-tuples hitting
`E` strictly fewer than `(5 / 8) * δ * t` times is at most `exp (-δ * t / 128)`. -/
private theorem card_count_lt_le {Ω : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    (E : Finset Ω) {δ : ℝ} (hδ : 0 < δ)
    (hp : 3 / 4 * δ ≤ (#E : ℝ) / (Fintype.card Ω : ℝ)) (t : ℕ) :
    ((#{z : Fin t → Ω | (#{j : Fin t | z j ∈ E} : ℝ) < 5 / 8 * δ * (t : ℝ)} : ℕ) : ℝ) /
      (Fintype.card Ω : ℝ) ^ t ≤ Real.exp (-(δ * (t : ℝ) / 128)) := by
  have hN : (0 : ℝ) < (Fintype.card Ω : ℝ) ^ t := pow_pos (Nat.cast_pos.2 Fintype.card_pos) t
  have hp1 : (#E : ℝ) / (Fintype.card Ω : ℝ) ≤ 1 :=
    (div_le_one (Nat.cast_pos.2 Fintype.card_pos)).2 (by exact_mod_cast card_le_univ E)
  set bad := univ.filter fun z : Fin t → Ω =>
    (#{j : Fin t | z j ∈ E} : ℝ) < 5 / 8 * δ * (t : ℝ)
  have hmarkov : (#bad : ℝ) * Real.exp (-(5 / 8 * δ * (t : ℝ) * Real.log (6 / 5))) ≤
      ∑ z : Fin t → Ω, (5 / 6 : ℝ) ^ #{j : Fin t | z j ∈ E} := by
    have hlog_neg : Real.log (5 / 6) = -Real.log (6 / 5) := by
      rw [show (5 / 6 : ℝ) = (6 / 5)⁻¹ by norm_num, Real.log_inv]
    calc (#bad : ℝ) * Real.exp (-(5 / 8 * δ * (t : ℝ) * Real.log (6 / 5)))
        = ∑ _z ∈ bad, Real.exp (-(5 / 8 * δ * (t : ℝ) * Real.log (6 / 5))) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ z ∈ bad, (5 / 6 : ℝ) ^ #{j : Fin t | z j ∈ E} := by
          refine sum_le_sum fun z hz => ?_
          have hz' := (mem_filter.1 hz).2.le
          rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 5 / 6), hlog_neg]
          refine Real.exp_le_exp.2 ?_
          nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 6 / 5)]
      _ ≤ ∑ z : Fin t → Ω, (5 / 6 : ℝ) ^ #{j : Fin t | z j ∈ E} :=
          sum_le_univ_sum_of_nonneg fun _ => by positivity
  have hmgf : (∑ z : Fin t → Ω, (5 / 6 : ℝ) ^ #{j : Fin t | z j ∈ E}) / (Fintype.card Ω : ℝ) ^ t ≤
      Real.exp (-(δ * (t : ℝ) / 8)) := by
    rw [avg_pow_count_mem]
    have hbase0 : 0 ≤ 1 + (#E : ℝ) / (Fintype.card Ω : ℝ) * (5 / 6 - 1) := by linarith
    calc (1 + (#E : ℝ) / (Fintype.card Ω : ℝ) * (5 / 6 - 1)) ^ t
        ≤ (1 + (-δ / 8)) ^ t := pow_le_pow_left₀ hbase0 (by linarith) t
      _ ≤ (Real.exp (-δ / 8)) ^ t :=
          pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-δ / 8)]) t
      _ = Real.exp (-(δ * (t : ℝ) / 8)) := by rw [← Real.exp_nat_mul]; congr 1; ring
  have h1 : (#bad : ℝ) / (Fintype.card Ω : ℝ) ^ t ≤
      Real.exp (-(δ * (t : ℝ) / 8) + 5 / 8 * δ * (t : ℝ) * Real.log (6 / 5)) := by
    rw [show -(δ * (t : ℝ) / 8) + 5 / 8 * δ * (t : ℝ) * Real.log (6 / 5) =
      -(δ * (t : ℝ) / 8) - -(5 / 8 * δ * (t : ℝ) * Real.log (6 / 5)) by ring,
      Real.exp_sub, le_div_iff₀ (Real.exp_pos _), div_mul_eq_mul_div]
    exact (div_le_div_of_nonneg_right hmarkov hN.le).trans hmgf
  refine h1.trans (Real.exp_le_exp.2 ?_)
  have hlog := log_six_fifths_lt
  have hdt : 0 ≤ δ * (t : ℝ) := by positivity
  nlinarith

/-! ### Nondeterministic circuit transformations and parallel demi-bit stretching -/

/-- Reindexing the ordinary inputs of a nondeterministic circuit by a constant-and-variable
substitution `ρ : Fin M → Fin m ⊕ Bool` increases its gate count by at most `2`. -/
private theorem nondet_substitute {M m k : ℕ} (D : Circuit signature (M + k) 1)
    (ρ : Fin M → Fin m ⊕ Bool) {S : Set (BitString M)}
    (hdec : D.NondeterministicDecides interpretation {true} S) :
    ∃ D' : Circuit signature (m + k) 1,
      D'.size ≤ D.size + 2 ∧
      D'.NondeterministicDecides interpretation {true} {x | substitute ρ x ∈ S} := by
  let ρ' : Fin (M + k) → Fin (m + k) ⊕ Bool :=
    Fin.append (fun i => (ρ i).map (Fin.castAdd k) id) (fun j => .inl (Fin.natAdd m j))
  refine ⟨D.comp (substituteCircuit ρ'),
    by rw [Circuit.size_comp, size_substituteCircuit, add_comm], fun x => ?_⟩
  have hsub (w : BitString k) : substitute ρ' (Fin.append x w) = Fin.append (substitute ρ x) w := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · simp only [ρ', substitute, Fin.append_left]
      cases ρ a <;> simp
    · simp [ρ', substitute]
  simpa only [Set.mem_ofPred_eq, Circuit.eval_comp, eval_substituteCircuit, hsub] using
    hdec (substitute ρ x)

/-- Monotone empirical-threshold amplification of a nondeterministic circuit across `t` fixed
suffixes `z : Fin t → BitString q`: accepts `y : BitString p` iff at least `θ` of the pairs
`(y, z j)` belong to `B`, using `t * k` witness bits and at most `t * D.size + 4 * t ^ 2 + 12`
gates. -/
private theorem nondet_empirical_threshold {p q k t : ℕ} (D : Circuit signature (p + q + k) 1)
    {B : Set (BitString (p + q))} [DecidablePred (· ∈ B)]
    (hdec : D.NondeterministicDecides interpretation {true} B)
    (z : Fin t → BitString q) (θ : ℕ) (hθ : θ ≤ t + 1) :
    ∃ D' : Circuit signature (p + t * k) 1,
      D'.size ≤ t * D.size + (2 + 2 + t * (2 * (t + 2))) ∧
      D'.NondeterministicDecides interpretation {true}
        {y : BitString p | θ ≤ #{j : Fin t | Fin.append y (z j) ∈ B}} := by
  have hconst : Synthesis interpretation (inputs (p + t * k))
      ({fun _ => true} ∪ {fun _ => false}) 2 :=
    (Synthesis.const true).union (Synthesis.const false)
  set S₁ := inputs (p + t * k) ∪ ({fun _ => true} ∪ {fun _ => false})
  let copy : Fin t → BooleanFunction (p + t * k) := fun j yw =>
    D.eval interpretation
      (Fin.append
        (Fin.append (fun i => yw (Fin.castAdd (t * k) i)) (z j))
        (fun l => yw (Fin.natAdd p (finProdFinEquiv (j, l))))) 0
  have hcopy (j : Fin t) : Synthesis interpretation S₁ {copy j} D.size := by
    let g : Fin (p + q + k) → BooleanFunction (p + t * k) :=
      Fin.append
        (Fin.append
          (fun i yw => yw (Fin.castAdd (t * k) i))
          (fun i _ => z j i))
        (fun l yw => yw (Fin.natAdd p (finProdFinEquiv (j, l))))
    have hg (idx : Fin (p + q + k)) : g idx ∈ S₁ := by
      dsimp only [g]
      refine Fin.addCases (fun a => ?_) (fun l => ?_) idx
      · rw [Fin.append_left]
        refine Fin.addCases (fun i => ?_) (fun i => ?_) a
        · rw [Fin.append_left]
          exact Set.mem_union_left _ ⟨Fin.castAdd (t * k) i, rfl⟩
        · rw [Fin.append_right]
          cases z j i
          · exact Set.mem_union_right _ (Set.mem_union_right _ rfl)
          · exact Set.mem_union_right _ (Set.mem_union_left _ rfl)
      · rw [Fin.append_right]
        exact Set.mem_union_left _ ⟨Fin.natAdd p (finProdFinEquiv (j, l)), rfl⟩
    have heq : (fun yw => D.eval interpretation (fun idx => g idx yw) 0) = copy j := by
      funext yw
      simp only [copy]
      congr 1
      funext idx
      exact Fin.addCases (fun a => Fin.addCases (fun i => by simp [g])
        (fun i => by simp [g]) a) (fun l => by simp [g]) idx
    exact (Synthesis.circuit (I := interpretation) D g hg).mono Set.Subset.rfl
      (Set.singleton_subset_iff.2 ⟨0, heq⟩) le_rfl
  have hall := Synthesis.iUnion (I := interpretation) (s := S₁)
    (fun j => {copy j}) (fun _ => D.size) hcopy
  set S₂ := S₁ ∪ ⋃ j : Fin t, {copy j}
  let seq : ℕ → BooleanFunction (p + t * k) :=
    fun l => if hl : l < t then copy ⟨l, hl⟩ else fun _ => false
  have hthr := synthesis_atLeast seq (s := S₂) (k := t) (j := θ)
    (fun l hl => by
      simp only [seq, hl, dite_true]
      exact Set.mem_union_right _ (Set.mem_iUnion.2 ⟨⟨l, hl⟩, rfl⟩)) hθ
  have htot := hconst.trans (hall.trans hthr)
  obtain ⟨D', hD', hD'sz⟩ := htot.exists_circuit
  refine ⟨D', hD'sz.trans ?_, fun y => ?_⟩
  · simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
    omega
  · simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    have heval (w : BitString (t * k)) :
        D'.eval interpretation (Fin.append y w) 0 = true ↔
          θ ≤ #{j : Fin t | D.eval interpretation
            (Fin.append (Fin.append y (z j)) (fun l => w (finProdFinEquiv (j, l)))) 0 = true} := by
      rw [congrFun (hD' (Fin.append y w)) 0]
      simp only [single_apply, atLeast, decide_eq_true_eq]
      have hcard : #{l ∈ range t | seq l (Fin.append y w) = true} =
          #{j : Fin t | D.eval interpretation
            (Fin.append (Fin.append y (z j)) (fun l => w (finProdFinEquiv (j, l)))) 0 = true} := by
        refine card_bij (fun l hl => ⟨l, mem_range.1 (mem_filter.1 hl).1⟩)
          (fun l hl => ?_) (fun _ _ _ _ h => congrArg Fin.val h)
          (fun j hj => ⟨j.val, mem_filter.2 ⟨mem_range.2 j.isLt, ?_⟩, rfl⟩)
        · have h2 := (mem_filter.1 hl).2
          have hlt := mem_range.1 (mem_filter.1 hl).1
          simp only [seq, hlt, dite_true, copy, Fin.append_left, Fin.append_right] at h2
          exact mem_filter.2 ⟨mem_univ _, h2⟩
        · have h2 := (mem_filter.1 hj).2
          simpa only [seq, j.isLt, dite_true, copy, Fin.append_left, Fin.append_right] using h2
      rw [hcard]
    constructor
    · intro hge
      have hwit (j : Fin t) : ∃ u : BitString k,
          Fin.append y (z j) ∈ B →
            D.eval interpretation (Fin.append (Fin.append y (z j)) u) 0 = true := by
        by_cases hmem : Fin.append y (z j) ∈ B
        · obtain ⟨u, hu⟩ := (hdec _).1 hmem
          exact ⟨u, fun _ => hu⟩
        · exact ⟨fun _ => false, fun h => absurd h hmem⟩
      choose u hu using hwit
      let w : BitString (t * k) := fun idx => u (finProdFinEquiv.symm idx).1
        (finProdFinEquiv.symm idx).2
      refine ⟨w, (heval w).2 (hge.trans (card_le_card fun j hj => ?_))⟩
      simp only [mem_filter, mem_univ, true_and, w, Equiv.symm_apply_apply] at hj ⊢
      exact hu j hj
    · rintro ⟨w, hw⟩
      refine ((heval w).1 hw).trans (card_le_card fun j hj => ?_)
      simp only [mem_filter, mem_univ, true_and] at hj ⊢
      exact (hdec _).2 ⟨fun l => w (finProdFinEquiv (j, l)), hj⟩

/-- `k`-fold parallel product `G_k(x₁, …, xₖ) = (f(x₁), …, f(xₖ))` of a map
`f : BitString r → BitString m`. -/
def parallelMap {r m : ℕ} (f : BitString r → BitString m) :
    (k : ℕ) → BitString (k * r) → BitString (k * m)
  | 0, _ => fun i => (Nat.not_lt_zero i.val (by have := i.isLt; omega)).elim
  | k + 1, x =>
    let eIn : r + k * r = (k + 1) * r := by ring
    let eOut : (k + 1) * m = m + k * m := by ring
    Fin.append
      (f fun i => x (Fin.cast eIn (Fin.castAdd (k * r) i)))
      (parallelMap f k fun i => x (Fin.cast eIn (Fin.natAdd r i))) ∘ Fin.cast eOut

/-- `k`-fold parallel circuit computing `parallelMap (c.eval interpretation) k`, of size
`k * c.size`. -/
def parallelCircuit {r m : ℕ} (c : Circuit signature r m) :
    (k : ℕ) → Circuit signature (k * r) (k * m)
  | 0 => Circuit.wiring signature fun i => (Nat.not_lt_zero i.val (by have := i.isLt; omega)).elim
  | k + 1 =>
    let eIn : r + k * r = (k + 1) * r := by ring
    let eOut : (k + 1) * m = m + k * m := by ring
    ((Circuit.wiring signature (Fin.cast eOut)).comp
      ((c.comp (Circuit.wiring signature fun i => Fin.cast eIn (Fin.castAdd (k * r) i))).append
        ((parallelCircuit c k).comp
          (Circuit.wiring signature fun i => Fin.cast eIn (Fin.natAdd r i)))))

private theorem eval_parallelCircuit {r m : ℕ} (c : Circuit signature r m) :
    ∀ (k : ℕ) (x : BitString (k * r)),
      (parallelCircuit c k).eval interpretation x = parallelMap (c.eval interpretation) k x
  | 0, _ => funext fun i => (Nat.not_lt_zero i.val (by have := i.isLt; omega)).elim
  | k + 1, x => by
    simp only [parallelCircuit, parallelMap, Circuit.eval_comp, Circuit.eval_wiring,
      Circuit.eval_append, eval_parallelCircuit c k]
    rfl

private theorem size_parallelCircuit {r m : ℕ} (c : Circuit signature r m) :
    ∀ k : ℕ, (parallelCircuit c k).size = k * c.size
  | 0 => by simp [parallelCircuit]
  | k + 1 => by
    simp only [parallelCircuit, Circuit.size_comp, Circuit.size_wiring, Circuit.size_append,
      size_parallelCircuit c k]
    ring

/-- The probabilistic sampling budget `⌈128 * (r + 3) / (δ / 2 ^ k)⌉₊` for `k`-fold parallel
demi-bit stretching. -/
private noncomputable def stretchSamples (r k : ℕ) (δ : ℝ) : ℕ :=
  ⌈128 * ((r : ℝ) + 3) * (2 : ℝ) ^ k / δ⌉₊

/-- **Parallel-concatenation demi-hardness reduction.** If a
nondeterministic circuit `D` of size `s` avoids the range of `k + 1` independent parallel copies
of `f : BitString r → BitString (r + 1)` on a set of density at least `δ > 0`, then some
nondeterministic circuit `D*` on `r + 1` inputs avoids `Set.range f` on a set of density at least
`δ / 2 ^ (k + 3)` and has gate size at most `T * (s + 4 * k) + 8 * T ^ 2` where
`T = ⌈128 * (r + 3) * 2 ^ k / δ⌉₊`. -/
theorem exists_nondet_single_of_parallel {r : ℕ} (f : BitString r → BitString (r + 1)) :
    ∀ (k : ℕ) {w : ℕ} (D : Circuit signature ((k + 1) * (r + 1) + w) 1)
      {B : Set (BitString ((k + 1) * (r + 1)))} {δ : ℝ},
      0 < δ →
      D.NondeterministicDecides interpretation {true} B →
      Disjoint B (Set.range (parallelMap f (k + 1))) →
      δ ≤ (B.ncard : ℝ) / (2 : ℝ) ^ ((k + 1) * (r + 1)) →
      let T := ⌈128 * ((r : ℝ) + 3) * (2 : ℝ) ^ k / δ⌉₊
      ∃ (w' : ℕ) (D' : Circuit signature ((r + 1) + w') 1) (A : Set (BitString (r + 1))),
        D'.size ≤ T * (D.size + 4 * k) + 8 * T ^ 2 ∧
        D'.NondeterministicDecides interpretation {true} A ∧
        Disjoint A (Set.range f) ∧
        δ / (2 : ℝ) ^ (k + 3) ≤ (A.ncard : ℝ) / (2 : ℝ) ^ (r + 1) := by
  intro k
  induction k with
  | zero =>
    intro w D B δ hδ hdec hdisj hdens T
    have hT1 : 1 ≤ T := Nat.succ_le_of_lt
      (Nat.ceil_pos.2 (by positivity : (0 : ℝ) < 128 * ((r : ℝ) + 3) * (2 : ℝ) ^ 0 / δ))
    have heq : 1 * (r + 1) = r + 1 := one_mul _
    let ρ : Fin (1 * (r + 1)) → Fin (r + 1) ⊕ Bool := fun i => .inl (Fin.cast heq i)
    obtain ⟨D', hD'sz, hD'dec⟩ := nondet_substitute D ρ hdec
    refine ⟨w, D', {y | substitute ρ y ∈ B}, ?_, hD'dec, ?_, ?_⟩
    · have hT2 : 2 ≤ 8 * T ^ 2 := by nlinarith
      have hDle : D.size ≤ T * D.size := Nat.le_mul_of_pos_left _ hT1
      simpa using hD'sz.trans (by omega)
    · refine Set.disjoint_left.2 fun y hy hmem => Set.disjoint_left.1 hdisj hy ?_
      obtain ⟨x, hx⟩ := hmem
      rw [← hx]
      refine ⟨x ∘ Fin.cast (one_mul r), funext fun i => ?_⟩
      simp only [parallelMap, ρ, substitute, Function.comp_apply, Sum.elim_inl]
      have h10 : (0 + 1) * (r + 1) = r + 1 + 0 * (r + 1) := by ring
      have hc : Fin.cast h10 i = Fin.castAdd (0 * (r + 1)) (Fin.cast heq i) := Fin.ext rfl
      rw [hc, Fin.append_left]
      congr 1
    · have hcard : ({y : BitString (r + 1) | substitute ρ y ∈ B}).ncard = B.ncard := by
        let e : BitString (r + 1) ≃ BitString (1 * (r + 1)) :=
          Equiv.piCongrLeft' _ (finCongr heq.symm)
        have hpre : {y : BitString (r + 1) | substitute ρ y ∈ B} = e ⁻¹' B := rfl
        rw [hpre, ← Set.ncard_image_of_injective _ e.injective, e.image_preimage]
      rw [hcard]
      simp only [zero_add, one_mul] at hdens
      exact (div_le_self hδ.le (by norm_num)).trans hdens
  | succ k ih =>
    classical
    intro w D B δ hδ hdec hdisj hdens T
    let p := r + 1
    let q := (k + 1) * p
    have hpq : p + q = (k + 1 + 1) * p := by dsimp only [p, q]; ring
    let ρsplit : Fin ((k + 1 + 1) * p) → Fin (p + q) ⊕ Bool := fun i => .inl (Fin.cast hpq.symm i)
    obtain ⟨D₀, hD₀sz, hD₀dec⟩ := nondet_substitute D ρsplit hdec
    let B₀ : Set (BitString (p + q)) := {yz | substitute ρsplit yz ∈ B}
    let slice : BitString p → Finset (BitString q) :=
      fun y => univ.filter fun z => Fin.append y z ∈ B₀
    have hB₀_card : B₀.ncard = ∑ y : BitString p, #(slice y) := by
      have hB₀_eq : B₀.ncard = #(univ.filter fun yz : BitString (p + q) => yz ∈ B₀) := by
        rw [← Set.ncard_coe_finset]; simp [coe_filter]
      have happ (yz : BitString (p + q)) :
          Fin.append (fun i => yz (Fin.castAdd q i)) (fun j => yz (Fin.natAdd p j)) = yz :=
        funext fun i => Fin.addCases (fun _ => by simp) (fun _ => by simp) i
      rw [hB₀_eq, ← card_sigma]
      refine card_nbij'
        (fun yz => ⟨fun i => yz (Fin.castAdd q i), fun j => yz (Fin.natAdd p j)⟩)
        (fun s => Fin.append s.1 s.2)
        (fun yz hyz => by
          have h1 : yz ∈ B₀ := (mem_filter.1 (mem_coe.1 hyz)).2
          exact mem_coe.2 (mem_sigma.2 ⟨mem_univ _, mem_filter.2 ⟨mem_univ _,
            (happ yz).symm ▸ h1⟩⟩))
        (fun s hs => by
          have h1 : Fin.append s.1 s.2 ∈ B₀ := (mem_filter.1 (mem_sigma.1 (mem_coe.1 hs)).2).2
          exact mem_coe.2 (mem_filter.2 ⟨mem_univ _, h1⟩))
        (fun yz _ => happ yz)
        (fun ⟨y, z⟩ _ => Sigma.ext (by simp) (heq_of_eq (by simp)))
    have hB₀_eq_B : B₀.ncard = B.ncard := by
      let e : BitString (p + q) ≃ BitString ((k + 1 + 1) * p) :=
        Equiv.piCongrLeft' _ (finCongr hpq)
      have hpre : B₀ = e ⁻¹' B := by ext yz; rfl
      rw [hpre, ← Set.ncard_image_of_injective _ e.injective, e.image_preimage]
    have hdisj₀ : ∀ (x₁ : BitString r) (x₂ : BitString ((k + 1) * r)),
        Fin.append (f x₁) (parallelMap f (k + 1) x₂) ∉ B₀ := by
      intro x₁ x₂ hmem
      refine Set.disjoint_left.1 hdisj hmem ?_
      let eIn : r + (k + 1) * r = (k + 1 + 1) * r := by ring
      refine ⟨Fin.append x₁ x₂ ∘ Fin.cast eIn.symm, funext fun i => ?_⟩
      dsimp only [ρsplit, substitute, Function.comp_apply, Sum.elim_inl]
      have hpm : parallelMap f (k + 1 + 1) (Fin.append x₁ x₂ ∘ Fin.cast eIn.symm) =
          Fin.append (f x₁) (parallelMap f (k + 1) x₂) ∘ Fin.cast hpq.symm := by
        conv_lhs => rw [parallelMap]
        refine congrArg (· ∘ Fin.cast hpq.symm) (congrArg₂ Fin.append ?_ ?_)
        · congr 1; funext j; dsimp only [Function.comp_apply]
          rw [show Fin.cast eIn.symm (Fin.cast eIn (Fin.castAdd ((k + 1) * r) j)) =
            Fin.castAdd ((k + 1) * r) j from Fin.ext rfl, Fin.append_left]
        · congr 1; funext j; dsimp only [Function.comp_apply]
          rw [show Fin.cast eIn.symm (Fin.cast eIn (Fin.natAdd r j)) =
            Fin.natAdd r j from Fin.ext rfl, Fin.append_right]
      rw [hpm]; rfl
    have hδ1 : δ ≤ 1 := by
      refine hdens.trans ((div_le_one (by positivity)).2 ?_)
      have hle := Set.ncard_le_ncard (Set.subset_univ B) Set.finite_univ
      rw [Set.ncard_univ, Nat.card_eq_fintype_card, BitString.card] at hle
      exact_mod_cast hle
    -- Case A: some `y = f x₁` in the range of `f` has slice density at least `δ / 2`.
    by_cases hcase : ∃ x₁ : BitString r,
        δ / 2 ≤ (#(slice (f x₁)) : ℝ) / (2 : ℝ) ^ q
    · obtain ⟨x₁, hx₁⟩ := hcase
      obtain ⟨D₁, hD₁sz, hD₁dec⟩ := nondet_substitute D₀ (prependInputs (f x₁)) hD₀dec
      set B₁ : Set (BitString q) := {z | substitute (prependInputs (f x₁)) z ∈ B₀}
      have hB₁_disj : Disjoint B₁ (Set.range (parallelMap f (k + 1))) :=
        Set.disjoint_left.2 fun z hz ⟨x₂, hx₂⟩ => by
          rw [← hx₂] at hz
          simp only [B₁, Set.mem_ofPred_eq, substitute_prependInputs] at hz
          exact hdisj₀ x₁ x₂ hz
      have hB₁_card : B₁.ncard = #(slice (f x₁)) := by
        rw [← Set.ncard_coe_finset]; congr 1; ext z; simp [B₁, slice]
      have hTeq : ⌈128 * ((r : ℝ) + 3) * (2 : ℝ) ^ k / (δ / 2)⌉₊ = T := by
        dsimp only [T]; congr 1; rw [pow_succ]; ring
      obtain ⟨w', D', A, hsz', hdec', hdisj', hdens'⟩ :=
        ih D₁ (by positivity : 0 < δ / 2) hD₁dec hB₁_disj (by rwa [hB₁_card])
      rw [hTeq] at hsz'
      refine ⟨w', D', A, hsz'.trans ?_, hdec', hdisj', ?_⟩
      · have hD1 : D₁.size + 4 * k ≤ D.size + 4 * (k + 1) := by omega
        exact Nat.add_le_add_right (Nat.mul_le_mul_left T hD1) _
      · convert hdens' using 1
        rw [pow_succ (2 : ℝ) (k + 3)]
        ring
    -- Case B: every `y = f x₁` in `Set.range f` has slice density `< δ / 2`.
    · push Not at hcase
      set H : Finset (BitString p) :=
        univ.filter fun y => 3 / 4 * δ ≤ (#(slice y) : ℝ) / (2 : ℝ) ^ q
      have hH_disj : ∀ x₁ : BitString r, f x₁ ∉ H := fun x₁ hx₁ =>
        by linarith [(mem_filter.1 hx₁).2, hcase x₁]
      have hH_card : δ / 4 * (2 : ℝ) ^ p ≤ (#H : ℝ) := by
        have hsum_ge : δ * (2 : ℝ) ^ p * (2 : ℝ) ^ q ≤
            ∑ y : BitString p, (#(slice y) : ℝ) := by
          have := (le_div_iff₀ (by positivity)).1 hdens
          rw [← hB₀_eq_B, hB₀_card, Nat.cast_sum, ← hpq, pow_add] at this
          linarith
        have hsum_le : (∑ y : BitString p, (#(slice y) : ℝ)) ≤
            (#H : ℝ) * (2 : ℝ) ^ q + 3 / 4 * δ * (2 : ℝ) ^ p * (2 : ℝ) ^ q := by
          rw [← sum_filter_add_sum_filter_not univ
            (fun y : BitString p => 3 / 4 * δ ≤ (#(slice y) : ℝ) / (2 : ℝ) ^ q)]
          have h1 : (∑ y ∈ H, (#(slice y) : ℝ)) ≤ (#H : ℝ) * (2 : ℝ) ^ q :=
            calc (∑ y ∈ H, (#(slice y) : ℝ)) ≤ ∑ _y ∈ H, (2 : ℝ) ^ q :=
                  sum_le_sum fun y _ => by
                    exact_mod_cast (card_le_univ (slice y)).trans_eq BitString.card
              _ = (#H : ℝ) * (2 : ℝ) ^ q := by rw [sum_const, nsmul_eq_mul]
          have h2 : (∑ y ∈ univ.filter (fun y : BitString p =>
              ¬ (3 / 4 * δ ≤ (#(slice y) : ℝ) / (2 : ℝ) ^ q)), (#(slice y) : ℝ)) ≤
              3 / 4 * δ * (2 : ℝ) ^ p * (2 : ℝ) ^ q :=
            calc _ ≤ ∑ _y ∈ univ.filter (fun y : BitString p =>
                  ¬ (3 / 4 * δ ≤ (#(slice y) : ℝ) / (2 : ℝ) ^ q)), (3 / 4 * δ * (2 : ℝ) ^ q) :=
                  sum_le_sum fun y hy => by
                    have hlt := not_le.1 (mem_filter.1 hy).2
                    exact ((div_lt_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ q)).1 hlt).le
              _ ≤ (2 : ℝ) ^ p * (3 / 4 * δ * (2 : ℝ) ^ q) := by
                  rw [sum_const, nsmul_eq_mul]
                  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                  exact_mod_cast (card_le_univ _).trans_eq BitString.card
              _ = 3 / 4 * δ * (2 : ℝ) ^ p * (2 : ℝ) ^ q := by ring
          linarith
        have hqpos : (0 : ℝ) < (2 : ℝ) ^ q := by positivity
        nlinarith
      have hH_pos : (0 : ℝ) < #H := (by positivity : (0 : ℝ) < δ / 4 * (2 : ℝ) ^ p).trans_le hH_card
      set t : ℕ := ⌈128 * ((r : ℝ) + 3) / δ⌉₊
      have ht_le_T : t ≤ T := by
        refine Nat.ceil_mono (div_le_div_of_nonneg_right ?_ hδ.le)
        exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ one_le_two)
      have hδt : 128 * ((r : ℝ) + 3) ≤ δ * (t : ℝ) := by
        have := (div_le_iff₀ hδ).1 (Nat.le_ceil (128 * ((r : ℝ) + 3) / δ))
        linarith
      have ht_ge : 4 ≤ t := by
        have : (128 * 3 : ℝ) ≤ (t : ℝ) := by nlinarith [hδt, hδ1]
        exact_mod_cast (show (4 : ℝ) ≤ t by linarith)
      set θ : ℕ := ⌈5 / 8 * δ * (t : ℝ)⌉₊
      have hθ_le : θ ≤ t + 1 := by
        have : 5 / 8 * δ * (t : ℝ) ≤ (t : ℝ) := by nlinarith [hδ1, show (0 : ℝ) ≤ t by positivity]
        exact (Nat.ceil_le.2 this).trans (Nat.le_succ t)
      let Ω := BitString q
      have hΩ : (Fintype.card Ω : ℝ) = (2 : ℝ) ^ q := by
        rw [BitString.card, Nat.cast_pow, Nat.cast_ofNat]
      -- Bad event 1: some `y ∈ Set.range f` crosses threshold `θ`.
      set rngF : Finset (BitString p) := univ.image f
      set bad₁ : Finset (Fin t → Ω) :=
        univ.filter fun z => ∃ y ∈ rngF, θ ≤ #{j : Fin t | z j ∈ slice y}
      have hexp2 : ∀ m : ℕ, Real.exp (-(m : ℝ)) ≤ ((2 : ℝ) ^ m)⁻¹ := fun m => by
        rw [Real.exp_neg, inv_le_inv₀ (Real.exp_pos _) (by positivity)]
        calc (2 : ℝ) ^ m ≤ (Real.exp 1) ^ m :=
              pow_le_pow_left₀ zero_le_two (by linarith [Real.add_one_le_exp 1]) m
          _ = Real.exp (m : ℝ) := by rw [← Real.exp_nat_mul, mul_one]
      have hbad₁ : (#bad₁ : ℝ) / (Fintype.card Ω : ℝ) ^ t ≤ 1 / 4 := by
        have hsub : bad₁ ⊆ rngF.biUnion fun y =>
            univ.filter fun z : Fin t → Ω =>
              5 / 8 * δ * (t : ℝ) ≤ (#{j : Fin t | z j ∈ slice y} : ℝ) := by
          intro z hz
          obtain ⟨y, hy, hθy⟩ := (mem_filter.1 hz).2
          exact mem_biUnion.2 ⟨y, hy, mem_filter.2 ⟨mem_univ z,
            (Nat.le_ceil _).trans (by exact_mod_cast hθy)⟩⟩
        have hle_sum : (#bad₁ : ℝ) / (Fintype.card Ω : ℝ) ^ t ≤
            ∑ _y ∈ rngF, Real.exp (-(δ * (t : ℝ) / 72)) := by
          calc (#bad₁ : ℝ) / (Fintype.card Ω : ℝ) ^ t
              ≤ ((∑ y ∈ rngF, #{z : Fin t → Ω |
                  5 / 8 * δ * (t : ℝ) ≤ (#{j : Fin t | z j ∈ slice y} : ℝ)}) : ℝ) /
                  (Fintype.card Ω : ℝ) ^ t := by
                refine div_le_div_of_nonneg_right ?_ (by positivity)
                exact_mod_cast (card_le_card hsub).trans card_biUnion_le
            _ = ∑ y ∈ rngF, ((#{z : Fin t → Ω |
                  5 / 8 * δ * (t : ℝ) ≤ (#{j : Fin t | z j ∈ slice y} : ℝ)} : ℕ) : ℝ) /
                  (Fintype.card Ω : ℝ) ^ t := by rw [sum_div]
            _ ≤ ∑ y ∈ rngF, Real.exp (-(δ * (t : ℝ) / 72)) := by
                refine sum_le_sum fun y hy => ?_
                obtain ⟨x₁, -, rfl⟩ := mem_image.1 hy
                exact card_count_ge_le (slice (f x₁)) hδ (by rw [hΩ]; exact (hcase x₁).le) t
        have hrng : (#rngF : ℝ) ≤ (2 : ℝ) ^ r := by
          exact_mod_cast card_image_le.trans_eq (by rw [card_univ, BitString.card])
        have htail : Real.exp (-(δ * (t : ℝ) / 72)) ≤ ((2 : ℝ) ^ (r + 3))⁻¹ :=
          (Real.exp_le_exp.2 (by push_cast; linarith [hδt])).trans (hexp2 (r + 3))
        calc (#bad₁ : ℝ) / (Fintype.card Ω : ℝ) ^ t
            ≤ (#rngF : ℝ) * Real.exp (-(δ * (t : ℝ) / 72)) := by
              simpa [sum_const, nsmul_eq_mul] using hle_sum
          _ ≤ (2 : ℝ) ^ r * ((2 : ℝ) ^ (r + 3))⁻¹ :=
              mul_le_mul hrng htail (Real.exp_pos _).le (by positivity)
          _ = 1 / 8 := by rw [pow_add]; field_simp; norm_num
          _ ≤ 1 / 4 := by norm_num
      -- Bad event 2: more than half of `H` fails to reach threshold `θ`.
      let miss (z : Fin t → Ω) : Finset (BitString p) :=
        H.filter fun y => #{j : Fin t | z j ∈ slice y} < θ
      set bad₂ : Finset (Fin t → Ω) := univ.filter fun z => (#H : ℝ) / 2 < (#(miss z) : ℝ)
      have hbad₂ : (#bad₂ : ℝ) / (Fintype.card Ω : ℝ) ^ t ≤ 1 / 2 := by
        have hswap : (∑ z : Fin t → Ω, (#(miss z) : ℝ)) =
            ∑ y ∈ H, ((#{z : Fin t → Ω | #{j : Fin t | z j ∈ slice y} < θ} : ℕ) : ℝ) := by
          simp_rw [miss, card_filter, Nat.cast_sum]
          exact sum_comm
        have hexp_miss : (∑ z : Fin t → Ω, (#(miss z) : ℝ)) / (Fintype.card Ω : ℝ) ^ t ≤
            (#H : ℝ) / 4 := by
          rw [hswap, sum_div]
          calc ∑ y ∈ H, ((#{z : Fin t → Ω | #{j : Fin t | z j ∈ slice y} < θ} : ℕ) : ℝ) /
                (Fintype.card Ω : ℝ) ^ t
              ≤ ∑ _y ∈ H, Real.exp (-(δ * (t : ℝ) / 128)) := by
                refine sum_le_sum fun y hy => ?_
                have hsub : (univ.filter fun z : Fin t → Ω => #{j : Fin t | z j ∈ slice y} < θ) ⊆
                    univ.filter fun z : Fin t → Ω =>
                      (#{j : Fin t | z j ∈ slice y} : ℝ) < 5 / 8 * δ * (t : ℝ) :=
                  fun z hz => mem_filter.2 ⟨mem_univ z, Nat.lt_ceil.1 (mem_filter.1 hz).2⟩
                have hcle : ((#{z : Fin t → Ω | #{j : Fin t | z j ∈ slice y} < θ} : ℕ) : ℝ) ≤
                    ((#{z : Fin t → Ω |
                      (#{j : Fin t | z j ∈ slice y} : ℝ) < 5 / 8 * δ * (t : ℝ)} : ℕ) : ℝ) := by
                  exact_mod_cast card_le_card hsub
                exact (div_le_div_of_nonneg_right hcle (by positivity)).trans
                  (card_count_lt_le (slice y) hδ (by rw [hΩ]; exact (mem_filter.1 hy).2) t)
            _ ≤ ∑ _y ∈ H, ((1 : ℝ) / 4) := sum_le_sum fun _ _ => by
                calc Real.exp (-(δ * (t : ℝ) / 128))
                    ≤ Real.exp (-(3 : ℝ)) := Real.exp_le_exp.2 (by linarith [hδt])
                  _ ≤ ((2 : ℝ) ^ 3)⁻¹ := by simpa using hexp2 3
                  _ ≤ 1 / 4 := by norm_num
            _ = (#H : ℝ) / 4 := by rw [sum_const, nsmul_eq_mul]; ring
        have hmk : (#bad₂ : ℝ) * ((#H : ℝ) / 2) ≤ ∑ z : Fin t → Ω, (#(miss z) : ℝ) :=
          calc (#bad₂ : ℝ) * ((#H : ℝ) / 2) = ∑ _z ∈ bad₂, (#H : ℝ) / 2 := by
                rw [sum_const, nsmul_eq_mul]
            _ ≤ ∑ z ∈ bad₂, (#(miss z) : ℝ) := sum_le_sum fun z hz => (mem_filter.1 hz).2.le
            _ ≤ ∑ z : Fin t → Ω, (#(miss z) : ℝ) := sum_le_univ_sum_of_nonneg fun _ => by positivity
        have hdiv := (div_le_div_of_nonneg_right hmk (by positivity)).trans hexp_miss
        rw [mul_comm, mul_div_assoc] at hdiv
        nlinarith [hH_pos, show 0 ≤ (#bad₂ : ℝ) / (Fintype.card Ω : ℝ) ^ t by positivity]
      -- Some sample tuple `z*` avoids both `bad₁` and `bad₂`.
      have hcard_union : #(bad₁ ∪ bad₂) < #(univ : Finset (Fin t → Ω)) := by
        have hlt : ((#(bad₁ ∪ bad₂) : ℕ) : ℝ) < (Fintype.card Ω : ℝ) ^ t := by
          have h1 : ((#(bad₁ ∪ bad₂) : ℕ) : ℝ) / (Fintype.card Ω : ℝ) ^ t ≤
              (#bad₁ : ℝ) / (Fintype.card Ω : ℝ) ^ t + (#bad₂ : ℝ) / (Fintype.card Ω : ℝ) ^ t := by
            rw [← add_div]
            exact div_le_div_of_nonneg_right (by exact_mod_cast card_union_le bad₁ bad₂)
              (by positivity)
          exact (div_lt_one (by positivity)).1 (by linarith [h1, hbad₁, hbad₂])
        rw [card_univ, Fintype.card_fun, Fintype.card_fin]
        exact_mod_cast hlt
      obtain ⟨z, -, hz⟩ := exists_mem_notMem_of_card_lt_card hcard_union
      rw [mem_union, not_or] at hz
      have hz1 : ∀ x₁ : BitString r, #{j : Fin t | Fin.append (f x₁) (z j) ∈ B₀} < θ := by
        intro x₁
        have h1 : ¬ ∃ y ∈ rngF, θ ≤ #{j : Fin t | z j ∈ slice y} :=
          fun h => hz.1 (mem_filter.2 ⟨mem_univ z, h⟩)
        push Not at h1
        simpa only [slice, mem_filter, mem_univ, true_and] using
          h1 (f x₁) (mem_image.2 ⟨x₁, mem_univ x₁, rfl⟩)
      have hz2 : (#(miss z) : ℝ) ≤ (#H : ℝ) / 2 :=
        not_lt.1 fun h => hz.2 (mem_filter.2 ⟨mem_univ z, h⟩)
      obtain ⟨D', hD'sz, hD'dec⟩ := nondet_empirical_threshold D₀ hD₀dec z θ hθ_le
      set A : Set (BitString p) := {y | θ ≤ #{j : Fin t | Fin.append y (z j) ∈ B₀}}
      refine ⟨t * w, D', A, ?_, hD'dec, ?_, ?_⟩
      · have h1 : t * D₀.size + (2 + 2 + t * (2 * (t + 2))) ≤
            t * (D.size + 4 * (k + 1)) + 8 * t ^ 2 := by
          have : t * D₀.size ≤ t * (D.size + 4 * (k + 1)) := Nat.mul_le_mul_left t (by omega)
          nlinarith [ht_ge]
        have h2 : t * (D.size + 4 * (k + 1)) + 8 * t ^ 2 ≤
            T * (D.size + 4 * (k + 1)) + 8 * T ^ 2 :=
          Nat.add_le_add (Nat.mul_le_mul_right _ ht_le_T)
            (Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left ht_le_T 2))
        exact hD'sz.trans (h1.trans h2)
      · exact Set.disjoint_left.2 fun y hy ⟨x₁, hx₁⟩ => (hz1 x₁).not_ge (hx₁ ▸ hy)
      · set Hgood := H.filter fun y => θ ≤ #{j : Fin t | z j ∈ slice y}
        have hpart : #Hgood + #(miss z) = #H := by
          simpa only [Hgood, miss, not_le] using
            card_filter_add_card_filter_not (s := H) fun y => θ ≤ #{j : Fin t | z j ∈ slice y}
        have hHgood_sub : (Hgood : Set (BitString p)) ⊆ A := fun y hy => by
          have h2 := (mem_filter.1 (mem_coe.1 hy)).2
          simpa only [A, Set.mem_ofPred_eq, slice, mem_filter, mem_univ, true_and] using h2
        have hA_card : (#H : ℝ) / 2 ≤ (A.ncard : ℝ) := by
          have hle : #Hgood ≤ A.ncard := by
            rw [← Set.ncard_coe_finset]
            exact Set.ncard_le_ncard hHgood_sub (Set.toFinite A)
          have hpart' : (#Hgood : ℝ) + (#(miss z) : ℝ) = (#H : ℝ) := by exact_mod_cast hpart
          have hle' : (#Hgood : ℝ) ≤ (A.ncard : ℝ) := by exact_mod_cast hle
          linarith
        have h8 : δ / (2 : ℝ) ^ (k + 1 + 3) ≤ δ / 8 :=
          div_le_div_of_nonneg_left hδ.le (by norm_num)
            (calc (8 : ℝ) = (2 : ℝ) ^ 3 := by norm_num
              _ ≤ (2 : ℝ) ^ (k + 1 + 3) := pow_le_pow_right₀ one_le_two (by omega))
        refine h8.trans ((le_div_iff₀ (by positivity)).2 ?_)
        linarith [hH_card, hA_card]

private theorem stretched_sstar_le {n r c s dsz T s_star : ℕ} (hs1 : 1 ≤ s) (hr : r ≤ n)
    (hc : c ≤ n) (h2c : (2 : ℝ) ^ c ≤ 2 * (n : ℝ)) (hdsz : dsz ≤ s + 4)
    (hT : T = ⌈128 * ((r : ℝ) + 3) * (2 : ℝ) ^ c / (s : ℝ)⁻¹⌉₊)
    (hss : s_star = max (T * (dsz + 4 * c) + 8 * T ^ 2) (2 ^ (c + 3) * s)) :
    (s_star : ℝ) ≤ (2 ^ 25 : ℝ) * ((n : ℝ) + 3) ^ 6 * (s : ℝ) ^ 2 := by
  have hr' : (r : ℝ) ≤ n := by exact_mod_cast hr
  have hs1' : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hT_le : (T : ℝ) ≤ 256 * ((n : ℝ) + 3) ^ 2 * (s : ℝ) := by
    have hraw : 128 * ((r : ℝ) + 3) * (2 : ℝ) ^ c / (s : ℝ)⁻¹ ≤
        256 * ((r : ℝ) + 3) * (n : ℝ) * (s : ℝ) := by
      rw [div_inv_eq_mul]
      calc 128 * ((r : ℝ) + 3) * (2 : ℝ) ^ c * (s : ℝ)
          ≤ 128 * ((r : ℝ) + 3) * (2 * (n : ℝ)) * (s : ℝ) := by gcongr
        _ = 256 * ((r : ℝ) + 3) * (n : ℝ) * (s : ℝ) := by ring
    rw [hT]
    calc (⌈128 * ((r : ℝ) + 3) * (2 : ℝ) ^ c / (s : ℝ)⁻¹⌉₊ : ℝ)
        ≤ 128 * ((r : ℝ) + 3) * (2 : ℝ) ^ c / (s : ℝ)⁻¹ + 1 :=
          (Nat.ceil_lt_add_one (by positivity)).le
      _ ≤ 256 * ((n : ℝ) + 3) * (n : ℝ) * (s : ℝ) + 1 := by
          linarith [hraw,
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (by linarith : 256 * ((r : ℝ) + 3) ≤ 256 * ((n : ℝ) + 3))
                hn0) (show (0 : ℝ) ≤ s by positivity)]
      _ ≤ 256 * ((n : ℝ) + 3) ^ 2 * (s : ℝ) := by
          have : ((n : ℝ) + 3) * (n : ℝ) + 1 ≤ ((n : ℝ) + 3) ^ 2 := by nlinarith
          nlinarith
  have hD1_le : ((dsz + 4 * c : ℕ) : ℝ) ≤ 5 * ((n : ℝ) + 3) * (s : ℝ) := by
    have : ((dsz + 4 * c : ℕ) : ℝ) ≤ (s : ℝ) + 4 + 4 * (n : ℝ) := by
      exact_mod_cast Nat.add_le_add hdsz (Nat.mul_le_mul_left 4 hc)
    nlinarith
  have hleft : ((T * (dsz + 4 * c) + 8 * T ^ 2 : ℕ) : ℝ) ≤
      (2 ^ 25 : ℝ) * ((n : ℝ) + 3) ^ 6 * (s : ℝ) ^ 2 := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    have hp1 : (T : ℝ) * ((dsz + 4 * c : ℕ) : ℝ) ≤ 1280 * ((n : ℝ) + 3) ^ 3 * (s : ℝ) ^ 2 :=
      (mul_le_mul hT_le hD1_le (by positivity) (by positivity)).trans_eq (by ring)
    have hp2 : 8 * (T : ℝ) ^ 2 ≤ 524288 * ((n : ℝ) + 3) ^ 4 * (s : ℝ) ^ 2 :=
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hT_le 2) (by norm_num)).trans_eq
        (by ring)
    have h46 : ((n : ℝ) + 3) ^ 4 * (s : ℝ) ^ 2 ≤ ((n : ℝ) + 3) ^ 6 * (s : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith) (by norm_num)) (sq_nonneg _)
    have h36 : ((n : ℝ) + 3) ^ 3 * (s : ℝ) ^ 2 ≤ ((n : ℝ) + 3) ^ 6 * (s : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith) (by norm_num)) (sq_nonneg _)
    have hc25 : (1280 : ℝ) + 524288 ≤ 2 ^ 25 := by norm_num
    have hnn : (0 : ℝ) ≤ ((n : ℝ) + 3) ^ 6 * (s : ℝ) ^ 2 := by positivity
    nlinarith
  have hright : ((2 ^ (c + 3) * s : ℕ) : ℝ) ≤
      (2 ^ 25 : ℝ) * ((n : ℝ) + 3) ^ 6 * (s : ℝ) ^ 2 := by
    push_cast
    rw [pow_add, show (2 : ℝ) ^ 3 = 8 by norm_num]
    have h1 : (2 : ℝ) ^ c * 8 * (s : ℝ) ≤ 16 * (n : ℝ) * (s : ℝ) :=
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2c (by norm_num))
        (by positivity)).trans_eq (by ring)
    have hn6 : (n : ℝ) ≤ ((n : ℝ) + 3) ^ 6 :=
      (by linarith : (n : ℝ) ≤ (n : ℝ) + 3).trans (le_self_pow₀ (by linarith) (by norm_num))
    have hs2 : (s : ℝ) ≤ (s : ℝ) ^ 2 := le_self_pow₀ hs1' (by norm_num)
    have hns : (n : ℝ) * (s : ℝ) ≤ ((n : ℝ) + 3) ^ 6 * (s : ℝ) ^ 2 :=
      mul_le_mul hn6 hs2 (by positivity) (by positivity)
    linarith [show (0 : ℝ) ≤ ((n : ℝ) + 3) ^ 6 * (s : ℝ) ^ 2 by positivity]
  rw [hss, Nat.cast_max]
  exact max_le hleft hright

private theorem stretched_poly_lt_subexp {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (2 ^ 25 : ℝ) * ((n : ℝ) + 3) ^ 6 * ((2 : ℝ) ^ ((n : ℝ) ^ (ε / 2))) ^ 2 <
        (2 : ℝ) ^ ((n : ℝ) ^ (3 * ε / 4) - 1) := by
  have h1 : ∀ᶠ n : ℕ in atTop, 4 * (n : ℝ) ^ (ε / 2) + 26 ≤ (n : ℝ) ^ (3 * ε / 4) := by
    have ht := (tendsto_rpow_atTop (show 0 < ε / 4 by positivity)).comp tendsto_natCast_atTop_atTop
    filter_upwards [ht.eventually (eventually_ge_atTop 30), eventually_ge_atTop 1] with n hn hn1
    have hge1 : (1 : ℝ) ≤ (n : ℝ) ^ (ε / 2) :=
      Real.one_le_rpow (by exact_mod_cast hn1) (by positivity)
    have hprod : (n : ℝ) ^ (3 * ε / 4) = (n : ℝ) ^ (ε / 4) * (n : ℝ) ^ (ε / 2) := by
      rw [← Real.rpow_add (by positivity)]; congr 1; ring
    have hn' : (30 : ℝ) ≤ (n : ℝ) ^ (ε / 4) := hn
    rw [hprod]; nlinarith
  have h2 : ∀ᶠ n : ℕ in atTop, 6 * Real.log ((n : ℝ) + 3) / Real.log 2 < (n : ℝ) ^ (ε / 2) := by
    have hev := log_le_mul_rpow_eventually (r := ε / 2) (c := Real.log 2 / 13)
      (by positivity) (by positivity)
    filter_upwards [hev.natCast_atTop, eventually_ge_atTop 4] with n hn hn4
    have hlog3 : Real.log ((n : ℝ) + 3) ≤ 2 * Real.log (n : ℝ) := by
      rw [show 2 * Real.log (n : ℝ) = Real.log ((n : ℝ) ^ 2) by
        rw [Real.log_pow]; push_cast; rfl]
      refine Real.log_le_log (by positivity) ?_
      have : (4 : ℝ) ≤ n := by exact_mod_cast hn4
      nlinarith
    have hpos_rpow : (0 : ℝ) < (n : ℝ) ^ (ε / 2) := by positivity
    rw [div_lt_iff₀ (Real.log_pos one_lt_two)]
    nlinarith [Real.log_pos one_lt_two]
  filter_upwards [h1, h2, eventually_ge_atTop 2] with n hn1 hn2 hn2'
  have hpow6 : ((n : ℝ) + 3) ^ 6 < (2 : ℝ) ^ ((n : ℝ) ^ (ε / 2)) := by
    rw [← Real.log_lt_log_iff (by positivity) (by positivity), Real.log_pow, Real.log_rpow two_pos]
    have := (div_lt_iff₀ (Real.log_pos one_lt_two)).1 hn2
    push_cast; linarith
  calc (2 ^ 25 : ℝ) * ((n : ℝ) + 3) ^ 6 * ((2 : ℝ) ^ ((n : ℝ) ^ (ε / 2))) ^ 2
      < (2 : ℝ) ^ (25 : ℝ) * (2 : ℝ) ^ ((n : ℝ) ^ (ε / 2)) *
          ((2 : ℝ) ^ ((n : ℝ) ^ (ε / 2)) * (2 : ℝ) ^ ((n : ℝ) ^ (ε / 2))) := by
        rw [sq, show (2 ^ 25 : ℝ) = (2 : ℝ) ^ (25 : ℝ) by norm_num]; gcongr
    _ = (2 : ℝ) ^ (25 + 3 * (n : ℝ) ^ (ε / 2)) := by
        simp only [← Real.rpow_add two_pos]; congr 1; ring
    _ ≤ (2 : ℝ) ^ ((n : ℝ) ^ (3 * ε / 4) - 1) := by
        refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
        have : (1 : ℝ) ≤ (n : ℝ) ^ (ε / 2) :=
          Real.one_le_rpow (by exact_mod_cast (show 1 ≤ n by omega)) (by positivity)
        linarith

/-- **Stretching demi-bits to `n + ⌈log₂ n⌉ + 1`**. Under
`DemiBitConjecture`, there exist a `P/poly` generator `G` with output length
`m(n) = n + ⌈log₂ n⌉ + 1` and a constant `δ > 0` such that
`demiHardness (G.eval n) ≥ 2 ^ (n ^ δ)` for all sufficiently large `n` (and in particular `G` has
super-polynomial demi-hardness `n ^ ω(1)`). -/
theorem exists_stretched_demiBit_clog (hRud : DemiBitConjecture) :
    ∃ (G : PPolyGenerator (fun n => n + Nat.clog 2 n + 1)) (δ : ℝ),
      0 < δ ∧ ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ ((n : ℝ) ^ δ) ≤ (demiHardness (G.eval n) : ℝ) := by
  obtain ⟨g, ε, hε, hghard⟩ := hRud
  obtain ⟨pg, hpg⟩ := g.size_poly
  set m : ℕ → ℕ := fun n => n + Nat.clog 2 n + 1
  set k : ℕ → ℕ := fun n => Nat.clog 2 n + 1
  -- Build `G.circuit n`: for `k n ≤ n`, run `k n` parallel copies of `g.circuit (n / k n)` and
  -- pass the remaining `n % k n` input bits unchanged; for `n < k n`, pad with `false` bits.
  have hlen_in (n : ℕ) : k n * (n / k n) + n % k n = n := Nat.div_add_mod n (k n)
  have hlen_out (n : ℕ) : m n = k n * (n / k n + 1) + n % k n := by
    have := hlen_in n
    dsimp only [m, k] at this ⊢
    linarith
  let circ (n : ℕ) : Circuit signature n (m n) :=
    if _ : k n ≤ n then
      let r := n / k n
      let rem := n % k n
      (Circuit.wiring signature (Fin.cast (hlen_out n))).comp
        (((parallelCircuit (g.circuit r) (k n)).comp
            (Circuit.wiring signature fun i =>
              Fin.cast (hlen_in n) (Fin.castAdd rem i))).append
          ((Circuit.id signature rem).comp
            (Circuit.wiring signature fun i =>
              Fin.cast (hlen_in n) (Fin.natAdd (k n * r) i))))
    else
      substituteCircuit (fun j : Fin (m n) => if hj : j.val < n then .inl ⟨j.val,
        hj⟩ else .inr false)
  have hstretch (n : ℕ) : n < m n := by dsimp only [m]; omega
  have hsize_poly : ∃ p : Polynomial ℕ, ∀ n, (circ n).size ≤ p.eval (m n) := by
    refine ⟨Polynomial.X * pg + 2, fun n => ?_⟩
    dsimp only [circ]
    split_ifs with hkn
    · simp only [Circuit.size_comp, Circuit.size_wiring, Circuit.size_append,
        size_parallelCircuit, Circuit.id, zero_add, add_zero, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
      have hk_le : k n ≤ m n := by dsimp only [m, k]; omega
      have hr_le : n / k n + 1 ≤ m n :=
        Nat.succ_le_succ ((Nat.div_le_self n (k n)).trans (by omega))
      exact (Nat.mul_le_mul hk_le ((hpg _).trans (pg.eval_mono hr_le))).trans (Nat.le_add_right _ 2)
    · simp
  let G : PPolyGenerator m := ⟨circ, hstretch, hsize_poly⟩
  refine ⟨G, ε / 2, by positivity, ?_⟩
  obtain ⟨r₀, hr₀⟩ := eventually_atTop.1 hghard
  have hdiv_tend : Tendsto (fun n : ℕ => n / k n) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    -- Use `clog 2 n + 1 ≤ ⌊√n⌋` for large `n`, or directly `2 * (log₂ n + 2) ≤ n / (b + 1)`.
    have hev : ∀ᶠ x : ℕ in atTop, (b + 1) * (x + 2) ≤ 2 ^ x := by
      have := Nat.eventually_mul_pow_le_pow_div (3 * (b + 1)) 1 1 one_lt_two one_pos
      filter_upwards [this, eventually_ge_atTop 2] with x hx hx2
      simp only [pow_one, Nat.div_one] at hx
      nlinarith
    obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 hev
    refine ⟨2 ^ (x₀ + 1), fun n hn => ?_⟩
    set x := Nat.log 2 n
    have hn_ne : n ≠ 0 := by
      have : 1 ≤ 2 ^ (x₀ + 1) := Nat.one_le_two_pow; omega
    have hx_ge : x₀ + 1 ≤ x := (Nat.le_log_iff_pow_le one_lt_two hn_ne).2 hn
    have hclog : k n ≤ x + 2 := by
      have hlt : n < 2 ^ (x + 1) := Nat.lt_pow_succ_log_self one_lt_two n
      have hc : Nat.clog 2 n ≤ x + 1 := (Nat.clog_le_iff_le_pow one_lt_two).2 hlt.le
      dsimp only [k]; omega
    have hpow : 2 ^ x ≤ n := Nat.pow_log_le_self 2 hn_ne
    have hbx : b * k n ≤ n :=
      calc b * k n ≤ (b + 1) * (x + 2) := Nat.mul_le_mul (Nat.le_succ b) hclog
        _ ≤ 2 ^ x := hx₀ x (by omega)
        _ ≤ n := hpow
    exact (Nat.le_div_iff_mul_le (by dsimp only [k]; positivity)).2 hbx
  -- Asymptotic inequalities:
  -- (1) `(n : ℝ) ^ (3 / 4) ≤ n / k n` for large `n` (since `k n ≤ n ^ (1 / 4)`),
  -- (2) `2 ^ (n ^ (ε / 2))` gives `s* < 2 ^ ((n / k n) ^ ε)`.
  have hk_rpow : ∀ᶠ n : ℕ in atTop, 2 * (k n : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 4) := by
    have hev := log_le_mul_rpow_eventually (r := (1 : ℝ) / 4) (c := Real.log 2 / 4)
      (by norm_num) (by positivity)
    filter_upwards [hev.natCast_atTop, eventually_ge_atTop (32 ^ 4)] with n hn hn32
    have h4 : (32 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 4) :=
      calc (32 : ℝ) = ((32 ^ 4 : ℕ) : ℝ) ^ ((1 : ℝ) / 4) := by
            rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
        _ ≤ (n : ℝ) ^ ((1 : ℝ) / 4) :=
            Real.rpow_le_rpow (by positivity) (by exact_mod_cast hn32) (by norm_num)
    have hclog_le : (Nat.clog 2 n : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 + 1 := by
      by_cases hc : Nat.clog 2 n = 0
      · rw [hc, Nat.cast_zero]; positivity
      · have hgt : 2 ^ (Nat.clog 2 n - 1) < n := (Nat.lt_clog_iff_pow_lt one_lt_two).1 (by omega)
        have hlog : ((Nat.clog 2 n - 1 : ℕ) : ℝ) * Real.log 2 ≤ Real.log (n : ℝ) := by
          rw [← Real.log_pow]; exact Real.log_le_log (by positivity) (by exact_mod_cast hgt.le)
        rw [Nat.cast_sub (by omega), Nat.cast_one] at hlog
        have := (le_div_iff₀ (Real.log_pos one_lt_two)).2 hlog; linarith
    have hlog_le : Real.log (n : ℝ) / Real.log 2 ≤ (n : ℝ) ^ ((1 : ℝ) / 4) / 4 := by
      rw [div_le_iff₀ (Real.log_pos one_lt_two)]; linarith
    have hk_eq : (k n : ℝ) = (Nat.clog 2 n : ℝ) + 1 := by simp [k]
    linarith
  have hpoly_subexp := stretched_poly_lt_subexp hε
  have hrpow_sub : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (3 * ε / 4) ≤ ((n / k n : ℕ) : ℝ) ^ ε := by
    filter_upwards [hk_rpow, hdiv_tend.eventually (eventually_ge_atTop 2), eventually_ge_atTop 4]
      with n hkn hr2 hn4
    have hdiv_ge : (n : ℝ) / (2 * (k n : ℝ)) ≤ ((n / k n : ℕ) : ℝ) := by
      have hlt : (n : ℝ) < ((n / k n : ℕ) + 1 : ℝ) * (k n : ℝ) := by
        have := Nat.lt_div_mul_add (a := n) (b := k n) (by dsimp only [k]; positivity)
        have hcast : (n : ℝ) < ((n / k n * k n + k n : ℕ) : ℝ) := by exact_mod_cast this
        push_cast at hcast
        linarith
      have hr2' : (2 : ℝ) ≤ (n / k n : ℕ) := by exact_mod_cast hr2
      have hkpos : (0 : ℝ) < k n := by dsimp only [k]; positivity
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have h34 : (n : ℝ) ^ ((3 : ℝ) / 4) ≤ (n : ℝ) / (2 * (k n : ℝ)) := by
      rw [le_div_iff₀ (by dsimp only [k]; positivity)]
      calc (n : ℝ) ^ ((3 : ℝ) / 4) * (2 * (k n : ℝ))
          ≤ (n : ℝ) ^ ((3 : ℝ) / 4) * (n : ℝ) ^ ((1 : ℝ) / 4) :=
            mul_le_mul_of_nonneg_left hkn (by positivity)
        _ = (n : ℝ) := by rw [← Real.rpow_add (by positivity)]; norm_num
    calc (n : ℝ) ^ (3 * ε / 4) = ((n : ℝ) ^ ((3 : ℝ) / 4)) ^ ε := by
          rw [← Real.rpow_mul (by positivity)]; congr 1; ring
      _ ≤ ((n / k n : ℕ) : ℝ) ^ ε :=
          Real.rpow_le_rpow (by positivity) (h34.trans hdiv_ge) hε.le
  filter_upwards [hdiv_tend.eventually (eventually_ge_atTop (max r₀ 2)), hk_rpow,
    hpoly_subexp, hrpow_sub, eventually_ge_atTop 8] with n hr_ge _ hsubexp hrsub hn8
  classical
  by_contra hlt
  push Not at hlt
  set s := demiHardness (G.eval n)
  have hkn : k n ≤ n := by
    have : 1 ≤ n / k n := by omega
    exact (Nat.le_div_iff_mul_le (by dsimp only [k]; positivity)).1 this |>.trans_eq' (one_mul _)
  obtain ⟨hs1, w, D, S, hDsz, hDdec, hdisj, hmeas⟩ := demiHardness_spec (hstretch n) (G.eval n)
  set r := n / k n
  set rem := n % k n
  set P := k n * (r + 1)
  have hm_eq : m n = P + rem := hlen_out n
  -- Reindex `S` along `m n = P + rem` and fix the best tail `u : BitString rem` by averaging.
  let ρm : Fin (m n) → Fin (P + rem) ⊕ Bool := fun i => .inl (Fin.cast hm_eq i)
  obtain ⟨D₀, hD₀sz, hD₀dec⟩ := nondet_substitute D ρm hDdec
  set S₀ : Set (BitString (P + rem)) := {yu | substitute ρm yu ∈ S}
  have hS₀_card : S₀.ncard = S.ncard := by
    let e : BitString (P + rem) ≃ BitString (m n) := Equiv.piCongrLeft' _ (finCongr hm_eq.symm)
    have hpre : S₀ = e ⁻¹' S := rfl
    rw [hpre, ← Set.ncard_image_of_injective _ e.injective, e.image_preimage]
  have hex_tail : ∃ u : BitString rem,
      (s : ℝ)⁻¹ ≤ (({y : BitString P | Fin.append y u ∈ S₀}).ncard : ℝ) / (2 : ℝ) ^ P := by
    have hsplit : S₀.ncard = ∑ u : BitString rem,
        #{y : BitString P | Fin.append y u ∈ S₀} := by
      have heq : S₀.ncard = #(univ.filter fun yu : BitString (P + rem) => yu ∈ S₀) := by
        rw [← Set.ncard_coe_finset]; congr 1; ext; simp
      have happ (yu : BitString (P + rem)) :
          Fin.append (fun i => yu (Fin.castAdd rem i)) (fun j => yu (Fin.natAdd P j)) = yu :=
        funext fun i => Fin.addCases (fun _ => by simp) (fun _ => by simp) i
      rw [heq, ← card_sigma]
      refine card_nbij'
        (fun yu => ⟨fun j => yu (Fin.natAdd P j), fun i => yu (Fin.castAdd rem i)⟩)
        (fun q => Fin.append q.2 q.1)
        (fun yu hyu => by simpa [happ] using hyu)
        (fun q hq => by simpa using hq)
        (fun yu _ => happ yu)
        (fun ⟨u, y⟩ _ => Sigma.ext (by simp) (heq_of_eq (by simp)))
    by_contra hall
    push Not at hall
    have hsum : (S₀.ncard : ℝ) < (s : ℝ)⁻¹ * (2 : ℝ) ^ (P + rem) := by
      rw [hsplit, Nat.cast_sum]
      have hlt_all : ∀ u : BitString rem,
          ((#{y : BitString P | Fin.append y u ∈ S₀} : ℕ) : ℝ) < (s : ℝ)⁻¹ * (2 : ℝ) ^ P :=
        fun u => by
          have h := (div_lt_iff₀ (show (0 : ℝ) < (2 : ℝ) ^ P from pow_pos two_pos P)).1 (hall u)
          have hnc : ({y : BitString P | Fin.append y u ∈ S₀}).ncard =
              #{y : BitString P | Fin.append y u ∈ S₀} := by
            rw [← Set.ncard_coe_finset]; simp [coe_filter]
          rwa [← hnc]
      calc (∑ u : BitString rem, ((#{y : BitString P | Fin.append y u ∈ S₀} : ℕ) : ℝ))
          < ∑ _u : BitString rem, (s : ℝ)⁻¹ * (2 : ℝ) ^ P :=
            sum_lt_sum_of_nonempty univ_nonempty fun u _ => hlt_all u
        _ = (2 : ℝ) ^ rem * ((s : ℝ)⁻¹ * (2 : ℝ) ^ P) := by
            rw [sum_const, card_univ, BitString.card, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
        _ = (s : ℝ)⁻¹ * (2 : ℝ) ^ (P + rem) := by rw [pow_add]; ring
    have hge := (le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ m n)).1 hmeas
    have h2eq : (2 : ℝ) ^ m n = (2 : ℝ) ^ (P + rem) := congrArg ((2 : ℝ) ^ ·) hm_eq
    rw [← hS₀_card, h2eq] at hge
    linarith
  obtain ⟨u, hu⟩ := hex_tail
  obtain ⟨D₁, hD₁sz, hD₁dec⟩ := nondet_substitute D₀ (appendInputs u) hD₀dec
  set B : Set (BitString ((Nat.clog 2 n + 1) * (r + 1))) :=
    {y | substitute (appendInputs u) y ∈ S₀}
  have hB_disj : Disjoint B (Set.range (parallelMap (g.eval r) (Nat.clog 2 n + 1))) := by
    refine Set.disjoint_left.2 fun y hy hmem => Set.disjoint_left.1 hdisj hy ?_
    obtain ⟨x, hx⟩ := hmem
    rw [← hx]
    refine ⟨Fin.append x u ∘ Fin.cast (hlen_in n).symm, funext fun i => ?_⟩
    simp only [G, PPolyGenerator.eval, circ, hkn, dite_true, Circuit.id, Circuit.eval_comp,
      Circuit.eval_wiring, Circuit.eval_append, eval_parallelCircuit,
      ρm, substitute, Function.comp_apply, Sum.elim_inl, substitute_appendInputs]
    have h1 : ((Fin.append x u ∘ Fin.cast (hlen_in n).symm) ∘ fun j =>
        Fin.cast (hlen_in n) (Fin.castAdd (n % k n) j)) = x :=
      funext fun j => by
        dsimp only [Function.comp_apply, r, rem]
        rw [show Fin.cast (hlen_in n).symm (Fin.cast (hlen_in n) (Fin.castAdd (n % k n) j)) =
          Fin.castAdd rem j from Fin.ext rfl, Fin.append_left]
    have h2 : (((Fin.append x u ∘ Fin.cast (hlen_in n).symm) ∘ fun j =>
        Fin.cast (hlen_in n) (Fin.natAdd (k n * (n / k n)) j)) ∘ id) = u :=
      funext fun j => by
        dsimp only [Function.comp_apply, id_eq, r, rem]
        rw [show Fin.cast (hlen_in n).symm (Fin.cast (hlen_in n) (Fin.natAdd (k n * (n / k n)) j)) =
          Fin.natAdd (k n * r) j from Fin.ext rfl, Fin.append_right]
    exact congrFun (congrArg₂ Fin.append (congrArg (parallelMap _ _) h1) h2) _
  have hB_dens : (s : ℝ)⁻¹ ≤ (B.ncard : ℝ) / (2 : ℝ) ^ ((Nat.clog 2 n + 1) * (r + 1)) := by
    simpa [B] using hu
  obtain ⟨w', D', A, hD'sz, hD'dec, hAdisj, hAdens⟩ :=
    exists_nondet_single_of_parallel (g.eval r) (Nat.clog 2 n) D₁
      (by exact_mod_cast inv_pos.2 (show (0 : ℝ) < s by exact_mod_cast hs1))
      hD₁dec hB_disj hB_dens
  set T := ⌈128 * ((r : ℝ) + 3) * (2 : ℝ) ^ Nat.clog 2 n / (s : ℝ)⁻¹⌉₊
  set s_star : ℕ := max (T * (D₁.size + 4 * Nat.clog 2 n) + 8 * T ^ 2)
    (2 ^ (Nat.clog 2 n + 3) * s)
  have hs_star_pos : 1 ≤ s_star :=
    (Nat.succ_le_of_lt (Nat.mul_pos (Nat.pow_pos two_pos) hs1)).trans (le_max_right _ _)
  have hdist : IsDemiDistinguisher (g.eval r) s_star := by
    refine ⟨hs_star_pos, w', D', A, hD'sz.trans (le_max_left _ _), hD'dec, hAdisj, ?_⟩
    have h1 : (s_star : ℝ)⁻¹ ≤ ((2 ^ (Nat.clog 2 n + 3) * s : ℕ) : ℝ)⁻¹ :=
      inv_anti₀ (Nat.cast_pos.2 (Nat.mul_pos (Nat.pow_pos two_pos) hs1))
        (by exact_mod_cast le_max_right _ _)
    refine h1.trans (hAdens.trans_eq' ?_)
    push_cast; field_simp
  have hg_le : (demiHardness (g.eval r) : ℝ) ≤ (s_star : ℝ) := by
    exact_mod_cast demiHardness_le hdist
  have hg_ge : (2 : ℝ) ^ ((r : ℝ) ^ ε) ≤ (demiHardness (g.eval r) : ℝ) :=
    hr₀ r ((le_max_left _ _).trans hr_ge)
  have h2clog : ((2 : ℝ) ^ Nat.clog 2 n) ≤ 2 * (n : ℝ) := by
    have hc : Nat.clog 2 n ≤ Nat.log 2 n + 1 :=
      (Nat.clog_le_iff_le_pow one_lt_two).2 (Nat.lt_pow_succ_log_self one_lt_two n).le
    calc (2 : ℝ) ^ Nat.clog 2 n ≤ (2 : ℝ) ^ (Nat.log 2 n + 1) := pow_le_pow_right₀ one_le_two hc
      _ = 2 * ((2 ^ Nat.log 2 n : ℕ) : ℝ) := by rw [pow_succ, mul_comm]; push_cast; rfl
      _ ≤ 2 * (n : ℝ) := mul_le_mul_of_nonneg_left
          (by exact_mod_cast Nat.pow_log_le_self 2 (by omega)) zero_le_two
  have hs_star_le := stretched_sstar_le hs1 (Nat.div_le_self n (k n))
    (by dsimp only [k] at hkn; omega) h2clog
    (hD₁sz.trans (Nat.add_le_add_right (hD₀sz.trans (Nat.add_le_add_right hDsz 2)) 2)) rfl rfl
  have hfinal : (s_star : ℝ) < (2 : ℝ) ^ ((r : ℝ) ^ ε) :=
    calc (s_star : ℝ) ≤ (2 ^ 25 : ℝ) * ((n : ℝ) + 3) ^ 6 * (s : ℝ) ^ 2 := hs_star_le
      _ ≤ (2 ^ 25 : ℝ) * ((n : ℝ) + 3) ^ 6 * ((2 : ℝ) ^ ((n : ℝ) ^ (ε / 2))) ^ 2 := by gcongr
      _ < (2 : ℝ) ^ ((n : ℝ) ^ (3 * ε / 4) - 1) := hsubexp
      _ ≤ (2 : ℝ) ^ ((r : ℝ) ^ ε) :=
          Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith [hrsub])
  linarith [hg_ge, hg_le, hfinal]

/-- Under `DemiBitConjecture`, the stretched `P/poly` generator of output length
`n + ⌈log₂ n⌉ + 1` has super-polynomial demi-hardness `n ^ ω(1)`. -/
theorem exists_stretched_demiBit_superpoly (hRud : DemiBitConjecture) :
    ∃ G : PPolyGenerator (fun n => n + Nat.clog 2 n + 1),
      ∀ d : ℕ, ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ d ≤ (demiHardness (G.eval n) : ℝ) := by
  obtain ⟨G, δ, hδ, hG⟩ := exists_stretched_demiBit_clog hRud
  refine ⟨G, fun d => ?_⟩
  have hev := log_le_mul_rpow_eventually (r := δ) (c := Real.log 2 / ((d : ℝ) + 1)) hδ
    (by positivity)
  filter_upwards [hG, hev.natCast_atTop, eventually_ge_atTop 1] with n hn hln hn1
  have h1 : (d : ℝ) * Real.log (n : ℝ) ≤ (n : ℝ) ^ δ * Real.log 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0 : ℝ) < (d : ℝ) + 1)] at hln
    have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
    linarith
  have hpow : (n : ℝ) ^ d ≤ (2 : ℝ) ^ ((n : ℝ) ^ δ) := by
    rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_pow, Real.log_rpow two_pos]
    exact h1
  exact hpow.trans hn

/-! ### Lautemann's XOR shift-covering lemma -/

/-- Bitwise exclusive-or `x ⊕ y` on `BitString m`. -/
@[expose]
def bitXor {m : ℕ} (x y : BitString m) : BitString m :=
  fun i => xor (x i) (y i)

/-- Coordinatewise criterion for equality with `bitXor x y`. -/
theorem eq_bitXor_of_forall {m : ℕ} {z x y : BitString m}
    (h : ∀ i : Fin m, z i = xor (x i) (y i)) : z = bitXor x y :=
  funext h

/-- Coordinate of `bitXor x y` when `y i = false`. -/
theorem bitXor_of_false_right {m : ℕ} (x y : BitString m) {i : Fin m} (hy : y i = false) :
    bitXor x y i = x i := by
  dsimp only [bitXor]; rw [hy, Bool.xor_false]

/-- Coordinate of `bitXor x y` when `y i = true`. -/
theorem bitXor_of_true_right {m : ℕ} (x y : BitString m) {i : Fin m} (hy : y i = true) :
    bitXor x y i = !x i := by
  dsimp only [bitXor]; rw [hy, Bool.xor_true]

/-- Bitwise exclusive-or is self-inverse (`x ⊕ x = false`). -/
@[simp]
theorem bitXor_self {m : ℕ} (x : BitString m) : bitXor x x = fun _ => false := by
  funext i; simp [bitXor]

/-- Bitwise exclusive-or is commutative. -/
theorem bitXor_comm {m : ℕ} (x y : BitString m) : bitXor x y = bitXor y x := by
  funext i; exact Bool.xor_comm (x i) (y i)

/-- Bitwise exclusive-or is associative. -/
theorem bitXor_assoc {m : ℕ} (x y z : BitString m) :
    bitXor (bitXor x y) z = bitXor x (bitXor y z) := by
  funext i; exact Bool.xor_assoc (x i) (y i) (z i)

/-- Cancelling a right XOR shift: `(x ⊕ s) ⊕ s = x`. -/
@[simp]
theorem bitXor_cancel_right {m : ℕ} (x s : BitString m) : bitXor (bitXor x s) s = x := by
  funext i; dsimp only [bitXor]; cases x i <;> cases s i <;> rfl

/-- Cancelling a left XOR shift: `s ⊕ (s ⊕ x) = x`. -/
@[simp]
theorem bitXor_cancel_left {m : ℕ} (s x : BitString m) : bitXor s (bitXor s x) = x := by
  funext i; dsimp only [bitXor]; cases s i <;> cases x i <;> rfl

/-- Bitwise XOR with a fixed shift `s` is an involution equivalence on `BitString m`. -/
def bitXorEquiv {m : ℕ} (s : BitString m) : BitString m ≃ BitString m where
  toFun x := bitXor s x
  invFun x := bitXor s x
  left_inv := bitXor_cancel_left s
  right_inv := bitXor_cancel_left s

/-- A shift tuple `s : Fin r → BitString m` covers `BitString m` by XOR translates of `A`, i.e.
`{0,1}^m = ⋃_j (s_j ⊕ A)`. -/
@[expose]
def CoversByXorShifts {m r : ℕ} (A : Set (BitString m)) (s : Fin r → BitString m) : Prop :=
  ∀ b : BitString m, ∃ j : Fin r, ∃ a ∈ A, b = bitXor a (s j)

/-- **Lautemann's shift-covering probability bound**: if `A ⊆ BitString m` has
uniform density `|A| / 2 ^ m ≥ 1 - ρ` with `0 ≤ ρ`, then the uniform probability over
`s = (s₁, …, sᵣ) ∈ (BitString m)^r` that `{0,1}^m = ⋃_j (s_j ⊕ A)` is at least
`1 - ρ ^ r * 2 ^ m`. -/
theorem card_xorShiftCover_ge {m r : ℕ} (A : Set (BitString m)) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hA : 1 - ρ ≤ (A.ncard : ℝ) / (2 : ℝ) ^ m) :
    1 - ρ ^ r * (2 : ℝ) ^ m ≤
      (({s : Fin r → BitString m | CoversByXorShifts A s}.ncard : ℝ) /
        ((2 : ℝ) ^ m) ^ r) := by
  classical
  have hnc : {s : Fin r → BitString m | CoversByXorShifts A s}.ncard =
      #{s : Fin r → BitString m | CoversByXorShifts A s} := by
    rw [← Set.ncard_coe_finset]; simp [coe_filter]
  rw [hnc]
  set Afin : Finset (BitString m) := univ.filter (· ∈ A)
  have hAfin : Afin.card = A.ncard := by
    rw [← Set.ncard_coe_finset]; simp [Afin, coe_filter]
  have hcompl_le : ((2 ^ m - Afin.card : ℕ) : ℝ) ≤ ρ * (2 : ℝ) ^ m := by
    have hle : Afin.card ≤ 2 ^ m := (card_le_univ Afin).trans_eq BitString.card
    rw [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_ofNat, hAfin]
    have := (le_div_iff₀ (by positivity)).1 hA
    linarith
  have hmiss (b : BitString m) :
      #{s : Fin r → BitString m | ∀ j : Fin r, bitXor b (s j) ∉ Afin} =
        (2 ^ m - Afin.card) ^ r := by
    let bad : Finset (BitString m) := univ.filter fun x => bitXor b x ∉ Afin
    have hbad : #bad = 2 ^ m - Afin.card := by
      have hgood : #{x : BitString m | bitXor b x ∈ Afin} = Afin.card :=
        card_bij (fun x _ => bitXor b x)
          (fun x hx => (mem_filter.1 hx).2)
          (fun x₁ _ x₂ _ h => (bitXorEquiv b).injective h)
          (fun a ha => ⟨bitXor b a, mem_filter.2 ⟨mem_univ _, by simpa using ha⟩, by simp⟩)
      have hpart := card_filter_add_card_filter_not (s := (univ : Finset (BitString m)))
        fun x => bitXor b x ∈ Afin
      rw [hgood, card_univ, BitString.card] at hpart
      dsimp only [bad]
      omega
    have hpi : (univ.filter fun s : Fin r → BitString m => ∀ j, bitXor b (s j) ∉ Afin) =
        Fintype.piFinset fun _ : Fin r => bad := by
      ext s; simp [Fintype.mem_piFinset, bad]
    rw [hpi, Fintype.card_piFinset_const, hbad]
  set uncov := univ.filter fun s : Fin r → BitString m => ¬ CoversByXorShifts A s
  have hsub : uncov ⊆ univ.biUnion fun b : BitString m =>
      univ.filter fun s : Fin r → BitString m => ∀ j : Fin r, bitXor b (s j) ∉ Afin := by
    intro s hs
    have hnc' := (mem_filter.1 hs).2
    simp only [CoversByXorShifts, not_forall, not_exists, not_and] at hnc'
    obtain ⟨b, hb⟩ := hnc'
    refine mem_biUnion.2 ⟨b, mem_univ b, mem_filter.2 ⟨mem_univ s, fun j hj => ?_⟩⟩
    exact hb j (bitXor b (s j)) (mem_filter.1 hj).2 (bitXor_cancel_right b (s j)).symm
  have huncov_le : (#uncov : ℝ) ≤ (2 : ℝ) ^ m * (ρ * (2 : ℝ) ^ m) ^ r := by
    have hnat : #uncov ≤ 2 ^ m * (2 ^ m - Afin.card) ^ r :=
      calc #uncov ≤ ∑ b : BitString m,
            #{s : Fin r → BitString m | ∀ j, bitXor b (s j) ∉ Afin} :=
            (card_le_card hsub).trans card_biUnion_le
        _ = 2 ^ m * (2 ^ m - Afin.card) ^ r := by
            simp_rw [hmiss]; rw [sum_const, card_univ, BitString.card, smul_eq_mul]
    calc (#uncov : ℝ) ≤ (2 : ℝ) ^ m * ((2 ^ m - Afin.card : ℕ) : ℝ) ^ r := by exact_mod_cast hnat
      _ ≤ (2 : ℝ) ^ m * (ρ * (2 : ℝ) ^ m) ^ r :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (Nat.cast_nonneg _) hcompl_le r) (by have := hρ; positivity)
  have htot : #{s : Fin r → BitString m | CoversByXorShifts A s} + #uncov = (2 ^ m) ^ r := by
    simpa [uncov, Fintype.card_fun, BitString.card] using
      card_filter_add_card_filter_not (s := (univ : Finset (Fin r → BitString m)))
        (CoversByXorShifts A)
  have htot' : ((#{s : Fin r → BitString m | CoversByXorShifts A s} : ℕ) : ℝ) =
      ((2 : ℝ) ^ m) ^ r - (#uncov : ℝ) := by
    have : ((#{s : Fin r → BitString m | CoversByXorShifts A s} : ℕ) : ℝ) + (#uncov : ℝ) =
        ((2 : ℝ) ^ m) ^ r := by exact_mod_cast htot
    linarith
  rw [htot', sub_div, div_self (by positivity)]
  have hdiv : (#uncov : ℝ) / ((2 : ℝ) ^ m) ^ r ≤ ρ ^ r * (2 : ℝ) ^ m := by
    rw [div_le_iff₀ (by positivity)]
    calc (#uncov : ℝ) ≤ (2 : ℝ) ^ m * (ρ * (2 : ℝ) ^ m) ^ r := huncov_le
      _ = ρ ^ r * (2 : ℝ) ^ m * ((2 : ℝ) ^ m) ^ r := by rw [mul_pow]; ring
  linarith

/-- Existence corollary of Lautemann's shift-covering bound: whenever `|A| / 2 ^ m > 1 - ρ` with
`0 ≤ ρ` and `ρ ^ r * 2 ^ m ≤ 1` (for `r ≥ 1`), or whenever `|A| / 2 ^ m ≥ 1 - ρ` and
`ρ ^ r * 2 ^ m < 1`, there exists `s : Fin r → BitString m` such that `CoversByXorShifts A s`. -/
theorem exists_coversByXorShifts {m r : ℕ} (A : Set (BitString m)) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hA : 1 - ρ ≤ (A.ncard : ℝ) / (2 : ℝ) ^ m) (hprob : ρ ^ r * (2 : ℝ) ^ m < 1) :
    ∃ s : Fin r → BitString m, CoversByXorShifts A s := by
  have h := card_xorShiftCover_ge (r := r) A hρ hA
  have hden : (0 : ℝ) < ((2 : ℝ) ^ m) ^ r := pow_pos (pow_pos two_pos m) r
  have hpos : 0 < ({s : Fin r → BitString m | CoversByXorShifts A s}.ncard : ℝ) :=
    (div_pos_iff_of_pos_right hden).1 (by linarith)
  have hne : {s : Fin r → BitString m | CoversByXorShifts A s}.Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by have : 0 < _ := Nat.cast_pos.1 hpos; omega)
  exact hne

end CslibFrontier.Computability
