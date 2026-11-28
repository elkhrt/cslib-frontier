module

public import CslibFrontier.Computability.Circuit.Arithmetic.VP
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

import CslibFrontier.Computability.Circuit.Program
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Homogeneous Frontier Sum-of-Products Decomposition for Arithmetic Circuits

Proves active-variable homogenization and homogeneous frontier sum-of-products decomposition for
binary arithmetic circuits (`Cslib.Circuits.Circuit (Cslib.Circuits.arithSignature K) m 1`) over
an arbitrary commutative semiring `K`, together with elementary homogeneous-component convolution
identities for multivariate polynomials.

## Main results

* `CslibFrontier.Computability.Circuit.Arithmetic.homogeneousComponent_C_of_pos`: positive-degree
  homogeneous components of constant multivariate polynomials vanish.
* `CslibFrontier.Computability.Circuit.Arithmetic.homogeneousComponent_X_eq`: homogeneous
  components of coordinate indeterminates.
* `CslibFrontier.Computability.Circuit.Arithmetic.homogeneousComponent_mul_pos`: convolution
  formula splitting out constant terms for positive-degree homogeneous components of a product.
* `CslibFrontier.Computability.Circuit.Arithmetic.sum_homogeneousComponent_pos_add_const`:
  decomposition of a polynomial of total degree at most `d` into its constant term plus positive
  homogeneous components up to degree `d`.
* `CslibFrontier.Computability.Circuit.Arithmetic.circuit_to_sum_of_prods`: decomposes any
  arithmetic circuit `c : Circuit (arithSignature K) m 1` of total degree `≤ d` (`d ≥ 1`) at
  threshold `t ≥ 1` into a sum of at most `d * ((c.size + 1) * d * (d + 6) + 2) ^ (2 * d / t)`
  products, each of at most `4 * d / t + 1` polynomials of total degree `≤ t` supported on at
  most `min m (2 * c.size + 1)` active variables.
-/

public section

namespace CslibFrontier.Computability.Circuit.Arithmetic

open Cslib Cslib.Circuits Cslib.Circuits.Arithmetic MvPolynomial
open scoped BigOperators

universe u

section HomogeneousHelpers

variable {K : Type u} [CommSemiring K] {n : ℕ}

/-- Every positive-degree homogeneous component of a constant polynomial is `0`. -/
theorem homogeneousComponent_C_of_pos {k : ℕ} (hk : 1 ≤ k) (a : K) :
    MvPolynomial.homogeneousComponent k (MvPolynomial.C a : MvPolynomial (Fin n) K) = 0 := by
  ext d
  rw [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_C]
  change (if d.degree = k then if 0 = d then a else 0 else 0) = (0 : MvPolynomial (Fin n) K).coeff d
  have hz : (0 : MvPolynomial (Fin n) K).coeff d = 0 := by simp
  rw [hz]
  split_ifs with h1 h2
  · subst h2; simp [Finsupp.degree] at h1; omega
  · rfl
  · rfl

/-- The degree-`k` homogeneous component of `X v` is `X v` if `k = 1` and `0` otherwise. -/
theorem homogeneousComponent_X_eq (k : ℕ) (v : Fin n) :
    MvPolynomial.homogeneousComponent k (X v : MvPolynomial (Fin n) K) =
      if k = 1 then X v else 0 := by
  ext d
  rw [MvPolynomial.coeff_homogeneousComponent]
  split_ifs with h1 h2 h3
  · rfl
  · subst h1
    rw [MvPolynomial.coeff_X]
    split_ifs with hd
    · subst hd; exfalso; apply h2; exact Finsupp.degree_single v 1
    · simp
  · rw [MvPolynomial.coeff_X]
    split_ifs with hd
    · subst hd; exfalso; apply h1; rw [Finsupp.degree_single, h3]
    · rfl
  · simp

private lemma degree_add_finsupp {σ : Type*} (a b : σ →₀ ℕ) :
    (a + b).degree = a.degree + b.degree :=
  map_add Finsupp.degree a b

private lemma degree_eq_zero_iff_finsupp {σ : Type*} (a : σ →₀ ℕ) :
    a.degree = 0 ↔ a = 0 := by
  constructor
  · intro h
    ext v
    by_contra hne
    have hmem : v ∈ a.support := Finsupp.mem_support_iff.mpr hne
    have hle : a v ≤ a.degree := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem
    have hpos : 0 < a v := Nat.pos_of_ne_zero hne
    omega
  · rintro rfl; simp [Finsupp.degree]

/-- Convolution formula for the degree-`k` (`k ≥ 1`) homogeneous component of a product `p * q`,
splitting out the constant terms `p.coeff 0` and `q.coeff 0`. -/
theorem homogeneousComponent_mul_pos {k : ℕ} (hk : 1 ≤ k)
    (p q : MvPolynomial (Fin n) K) :
    MvPolynomial.homogeneousComponent k (p * q) =
      MvPolynomial.C (p.coeff 0) * MvPolynomial.homogeneousComponent k q +
      MvPolynomial.C (q.coeff 0) * MvPolynomial.homogeneousComponent k p +
      ∑ j ∈ Finset.range (k - 1),
        MvPolynomial.homogeneousComponent (j + 1) p *
        MvPolynomial.homogeneousComponent (k - 1 - j) q := by
  ext d
  simp only [MvPolynomial.coeff_homogeneousComponent, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    MvPolynomial.coeff_C_mul, MvPolynomial.coeff_sum]
  by_cases hdk : d.degree = k
  · simp only [hdk, ↓reduceIte]
    have hsum_mid : ∑ j ∈ Finset.range (k - 1),
        (MvPolynomial.homogeneousComponent (j + 1) p *
          MvPolynomial.homogeneousComponent (k - 1 - j) q).coeff d =
        ∑ x ∈ Finset.antidiagonal d with 1 ≤ x.1.degree ∧ x.1.degree ≤ k - 1,
          p.coeff x.1 * q.coeff x.2 := by
      simp_rw [MvPolynomial.coeff_mul, MvPolynomial.coeff_homogeneousComponent]
      rw [Finset.sum_comm]
      calc ∑ x ∈ Finset.antidiagonal d, ∑ j ∈ Finset.range (k - 1),
              (if x.1.degree = j + 1 then p.coeff x.1 else 0) *
              (if x.2.degree = k - 1 - j then q.coeff x.2 else 0)
          = ∑ x ∈ Finset.antidiagonal d,
              if 1 ≤ x.1.degree ∧ x.1.degree ≤ k - 1 then p.coeff x.1 * q.coeff x.2 else 0 := by
            refine Finset.sum_congr rfl fun x hx => ?_
            have hxdeg : x.1.degree + x.2.degree = k := by
              rw [← degree_add_finsupp, Finset.mem_antidiagonal.mp hx, hdk]
            split_ifs with hmid
            · rw [Finset.sum_eq_single (x.1.degree - 1)]
              · have h1 : x.1.degree = x.1.degree - 1 + 1 := by omega
                have h2 : x.2.degree = k - 1 - (x.1.degree - 1) := by omega
                rw [ite_eq_left_iff.mpr (fun hc => absurd h1 hc),
                  ite_eq_left_iff.mpr (fun hc => absurd h2 hc)]
              · intro j _ hj
                have hne : x.1.degree ≠ j + 1 := by omega
                simp [hne]
              · intro hnot; exfalso; exact hnot (Finset.mem_range.mpr (by omega))
            · refine Finset.sum_eq_zero fun j hj => ?_
              have hj' := Finset.mem_range.mp hj
              have hne : x.1.degree ≠ j + 1 := by omega
              simp [hne]
        _ = _ := by rw [Finset.sum_filter]
    rw [hsum_mid, MvPolynomial.coeff_mul]
    have h0d : (0, d) ∈ Finset.antidiagonal d := Finset.mem_antidiagonal.mpr (zero_add d)
    have hd0 : (d, 0) ∈ Finset.antidiagonal d := Finset.mem_antidiagonal.mpr (add_zero d)
    have hne0d : (0, d) ≠ (d, 0) := by
      intro h; have h0 : d = 0 := (Prod.mk.inj h).2
      rw [h0] at hdk; simp [Finsupp.degree] at hdk; omega
    have hpart : Finset.antidiagonal d =
        insert (0, d) (insert (d, 0)
          (Finset.antidiagonal d |>.filter fun x => 1 ≤ x.1.degree ∧ x.1.degree ≤ k - 1)) := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_antidiagonal]
      constructor
      · intro hx
        have hxdeg : x.1.degree + x.2.degree = k := by rw [← degree_add_finsupp, hx, hdk]
        by_cases h0 : x.1.degree = 0
        · left
          have hx1 : x.1 = 0 := (degree_eq_zero_iff_finsupp x.1).mp h0
          rw [hx1, zero_add] at hx
          exact Prod.ext hx1 hx
        · by_cases hk' : x.1.degree = k
          · right; left
            have h20 : x.2.degree = 0 := by omega
            have hx2 : x.2 = 0 := (degree_eq_zero_iff_finsupp x.2).mp h20
            rw [hx2, add_zero] at hx
            exact Prod.ext hx hx2
          · right; right; exact ⟨hx, by omega, by omega⟩
      · rintro (rfl | rfl | ⟨hx, _⟩)
        · exact zero_add d
        · exact add_zero d
        · exact hx
    have hnot0 : (0, d) ∉ insert (d, 0)
        (Finset.antidiagonal d |>.filter fun x => 1 ≤ x.1.degree ∧ x.1.degree ≤ k - 1) := by
      simp only [Finset.mem_insert, Finset.mem_filter, hne0d, false_or, not_and]
      intro _ h; rw [map_zero] at h; omega
    have hnotd : (d, 0) ∉
        (Finset.antidiagonal d |>.filter fun x => 1 ≤ x.1.degree ∧ x.1.degree ≤ k - 1) := by
      simp only [Finset.mem_filter, not_and]; intro _ h; omega
    conv_lhs => rw [hpart]
    rw [Finset.sum_insert hnot0, Finset.sum_insert hnotd]
    ring
  · simp only [hdk, ↓reduceIte, mul_zero, add_zero, zero_add]
    symm
    refine Finset.sum_eq_zero fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    rw [MvPolynomial.coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_homogeneousComponent]
    have hxdeg : x.1.degree + x.2.degree = d.degree := by
      rw [← degree_add_finsupp, Finset.mem_antidiagonal.mp hx]
    split_ifs with h1 h2
    · omega
    all_goals simp

/-- Every polynomial `p` of total degree at most `d` equals its constant term plus the sum of its
positive-degree homogeneous components up to degree `d`. -/
theorem sum_homogeneousComponent_pos_add_const (p : MvPolynomial (Fin n) K) {d : ℕ}
    (hd : p.totalDegree ≤ d) :
    MvPolynomial.C (p.coeff 0) +
      ∑ k ∈ Finset.range d, MvPolynomial.homogeneousComponent (k + 1) p = p := by
  have htrim : ∑ k ∈ Finset.range (d + 1), MvPolynomial.homogeneousComponent k p = p := by
    conv_rhs => rw [← MvPolynomial.sum_homogeneousComponent (φ := p)]
    symm
    refine Finset.sum_subset (f := fun k => MvPolynomial.homogeneousComponent k p)
      (Finset.range_mono (Nat.succ_le_succ hd)) fun k hk hnot => ?_
    simp only [Finset.mem_range, not_lt] at hk hnot
    ext m
    rw [MvPolynomial.coeff_homogeneousComponent]
    have hz : (0 : MvPolynomial (Fin n) K).coeff m = 0 := by simp
    rw [hz]
    split_ifs with hm
    · by_contra hne
      have hle : m.degree ≤ p.totalDegree :=
        MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hne)
      omega
    · rfl
  conv_rhs => rw [← htrim]
  rw [Finset.sum_range_succ', MvPolynomial.homogeneousComponent_zero, add_comm]

end HomogeneousHelpers

/-! ### Homogeneous Layered Circuits and Frontier Decomposition -/

section HomCircuitFrontier

/-- Gate operations in a homogeneous layered circuit of positive-degree polynomials. -/
private inductive HomGate (K : Type u) (m idx : ℕ) : Type u
  | zero : HomGate K m idx
  | var (v : Fin m) : HomGate K m idx
  | add (terms : List (K × Fin idx)) : HomGate K m idx
  | mul (l r : Fin idx) : HomGate K m idx

/-- A topologically ordered homogeneous circuit in `m` variables whose gates all have an assigned
positive homogeneity degree `deg i ≥ 1` and only reference variables in `activeVars`. -/
private structure HomCircuit (K : Type u) (m : ℕ) : Type u where
  size : ℕ
  activeVars : Finset (Fin m)
  deg : Fin size → ℕ
  deg_pos : ∀ i, 1 ≤ deg i
  gates : (i : Fin size) → HomGate K m i.1
  var_ok : ∀ i v, gates i = .var v → deg i = 1 ∧ v ∈ activeVars
  add_ok : ∀ i ts, gates i = .add ts → ∀ t ∈ ts, deg ⟨t.2.1, lt_trans t.2.2 i.2⟩ = deg i
  mul_ok : ∀ i l r, gates i = .mul l r →
    deg ⟨l.1, lt_trans l.2 i.2⟩ + deg ⟨r.1, lt_trans r.2 i.2⟩ = deg i

namespace HomCircuit

variable {K : Type u} [CommSemiring K] {m : ℕ}

/-- Lift a predecessor index `Fin i.1` into `Fin H.size`. -/
private abbrev lift {H : HomCircuit K m} {i : Fin H.size} (j : Fin i.1) : Fin H.size :=
  ⟨j.1, lt_trans j.2 i.2⟩

/-- Polynomial computed by gate `i` of a homogeneous circuit `H`. -/
private noncomputable def poly (H : HomCircuit K m) (i : Fin H.size) : MvPolynomial (Fin m) K :=
  match H.gates i with
  | .zero => 0
  | .var v => X v
  | .add ts => (ts.map fun t => MvPolynomial.C t.1 * H.poly (lift t.2)).sum
  | .mul l r => H.poly (lift l) * H.poly (lift r)
termination_by i.1
decreasing_by
  all_goals first | exact t.2.2 | exact l.2 | exact r.2

private lemma poly_zero {H : HomCircuit K m} {i : Fin H.size} (h : H.gates i = .zero) :
    H.poly i = 0 := by rw [poly.eq_def, h]

private lemma poly_var {H : HomCircuit K m} {i : Fin H.size} {v : Fin m} (h : H.gates i = .var v) :
    H.poly i = X v := by rw [poly.eq_def, h]

private lemma poly_add {H : HomCircuit K m} {i : Fin H.size} {ts : List (K × Fin i.1)}
    (h : H.gates i = .add ts) :
    H.poly i = (ts.map fun t => MvPolynomial.C t.1 * H.poly (lift t.2)).sum := by
  rw [poly.eq_def, h]

private lemma poly_mul {H : HomCircuit K m} {i : Fin H.size} {l r : Fin i.1}
    (h : H.gates i = .mul l r) :
    H.poly i = H.poly (lift l) * H.poly (lift r) := by
  rw [poly.eq_def, h]

/-- Predicate asserting a polynomial is supported only on variables in `V`. -/
private def VarsIn (V : Finset (Fin m)) (p : MvPolynomial (Fin m) K) : Prop :=
  ∀ μ ∈ p.support, ∀ v : Fin m, μ v ≠ 0 → v ∈ V

private lemma varsIn_zero (V : Finset (Fin m)) : VarsIn (K := K) V 0 := by
  intro μ hμ; simp at hμ

private lemma varsIn_C (V : Finset (Fin m)) (a : K) : VarsIn V (MvPolynomial.C a) := by
  intro μ hμ v hv
  have h0 : μ = 0 := by
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C] at hμ
    by_contra hne
    exact hμ (by simp [Ne.symm hne])
  subst h0; simp at hv

private lemma varsIn_X {V : Finset (Fin m)} {v : Fin m} (hv : v ∈ V) :
    VarsIn (K := K) V (X v) := by
  intro μ hμ w hw
  rw [MvPolynomial.mem_support_iff, MvPolynomial.X, MvPolynomial.coeff_monomial] at hμ
  have hμ_eq : Finsupp.single v 1 = μ := by
    by_contra hne
    exact hμ (by simp [hne])
  subst hμ_eq
  by_cases hvw : w = v
  · exact hvw ▸ hv
  · exfalso; exact hw (Finsupp.single_eq_of_ne hvw)

private lemma varsIn_add {V : Finset (Fin m)} {p q : MvPolynomial (Fin m) K}
    (hp : VarsIn V p) (hq : VarsIn V q) : VarsIn V (p + q) := by
  intro μ hμ v hv
  rcases Finset.mem_union.mp (MvPolynomial.support_add hμ) with h1 | h2
  · exact hp μ h1 v hv
  · exact hq μ h2 v hv

private lemma varsIn_list_sum {V : Finset (Fin m)} (l : List (MvPolynomial (Fin m) K))
    (hl : ∀ p ∈ l, VarsIn V p) : VarsIn V l.sum := by
  induction l with
  | nil => exact varsIn_zero V
  | cons p ps ih =>
    rw [List.sum_cons]
    exact varsIn_add (hl p List.mem_cons_self) (ih fun q hq => hl q (List.mem_cons_of_mem p hq))

private lemma varsIn_mul {V : Finset (Fin m)} {p q : MvPolynomial (Fin m) K}
    (hp : VarsIn V p) (hq : VarsIn V q) : VarsIn V (p * q) := by
  intro μ hμ v hv
  rcases Finset.mem_add.mp (MvPolynomial.support_mul p q hμ) with ⟨a, ha, b, hb, rfl⟩
  rw [Finsupp.add_apply] at hv
  by_cases hav : a v = 0
  · exact hq b hb v (by omega)
  · exact hp a ha v hav

private lemma list_C_mul_sum_totalDegree_le {α : Type*} (l : List (K × α))
    (f : α → MvPolynomial (Fin m) K) (B : ℕ) (h : ∀ t ∈ l, (f t.2).totalDegree ≤ B) :
    (l.map fun (t : K × α) => MvPolynomial.C t.1 * f t.2).sum.totalDegree ≤ B := by
  induction l with
  | nil => simp
  | cons t ts ih =>
    rw [List.map_cons, List.sum_cons]
    refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ (ih fun s hs =>
      h s (List.mem_cons_of_mem t hs)))
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, zero_add]
    exact h t List.mem_cons_self

private lemma poly_totalDegree_le (H : HomCircuit K m) (i : Fin H.size) :
    (H.poly i).totalDegree ≤ H.deg i := by
  induction hk : i.1 using Nat.strongRecOn generalizing i with
  | ind n ih =>
    subst hk
    cases hg : H.gates i with
    | zero => rw [H.poly_zero hg]; simp
    | var v =>
      rw [H.poly_var hg, (H.var_ok i v hg).1, MvPolynomial.X]
      exact (MvPolynomial.totalDegree_monomial_le (Finsupp.single v 1) (1 : K)).trans (by simp)
    | add ts =>
      rw [H.poly_add hg]
      exact list_C_mul_sum_totalDegree_le ts (fun j => H.poly (lift (i := i) j)) (H.deg i)
        fun t ht => by
          have hd := ih t.2.1 t.2.2 (lift (i := i) t.2) rfl
          rwa [H.add_ok i ts hg t ht] at hd
    | mul l r =>
      rw [H.poly_mul hg, ← H.mul_ok i l r hg]
      exact (MvPolynomial.totalDegree_mul _ _).trans
        (Nat.add_le_add (ih l.1 l.2 (lift l) rfl) (ih r.1 r.2 (lift r) rfl))

private lemma poly_varsIn (H : HomCircuit K m) (i : Fin H.size) :
    VarsIn H.activeVars (H.poly i) := by
  induction hk : i.1 using Nat.strongRecOn generalizing i with
  | ind n ih =>
    subst hk
    cases hg : H.gates i with
    | zero => rw [H.poly_zero hg]; exact varsIn_zero _
    | var v => rw [H.poly_var hg]; exact varsIn_X (H.var_ok i v hg).2
    | add ts =>
      rw [H.poly_add hg]
      refine varsIn_list_sum _ fun p hp => ?_
      rcases List.mem_map.mp hp with ⟨t, _, rfl⟩
      exact varsIn_mul (varsIn_C _ _) (ih t.2.1 t.2.2 (lift t.2) rfl)
    | mul l r =>
      rw [H.poly_mul hg]
      exact varsIn_mul (ih l.1 l.2 (lift l) rfl) (ih r.1 r.2 (lift r) rfl)

/-- Frontier of `H` at threshold `a`: multiplication gates `w = mul l r` with `deg w > a` and
both children of degree `≤ a`. -/
private def IsFrontier (H : HomCircuit K m) (a : ℕ) (w : Fin H.size) : Prop :=
  ∃ (l r : Fin w.1), H.gates w = .mul l r ∧ a < H.deg w ∧
    H.deg (lift l) ≤ a ∧ H.deg (lift r) ≤ a

/-- Relative polynomial `[u : w]` at threshold `a` (for `w` in the frontier at `a`). -/
private noncomputable def relPoly (H : HomCircuit K m) (a : ℕ) (w u : Fin H.size) :
    MvPolynomial (Fin m) K := by
  classical
  exact if H.deg u ≤ a then 0
    else if u = w then 1
    else match H.gates u with
      | .zero => 0
      | .var _ => 0
      | .add ts => (ts.map fun t => MvPolynomial.C t.1 * H.relPoly a w (lift t.2)).sum
      | .mul l r =>
        if a < H.deg (lift l) ∧ H.deg (lift r) ≤ a then
          H.relPoly a w (lift l) * H.poly (lift r)
        else if H.deg (lift l) ≤ a ∧ a < H.deg (lift r) then
          H.poly (lift l) * H.relPoly a w (lift r)
        else 0
termination_by u.1
decreasing_by
  all_goals first | exact t.2.2 | exact l.2 | exact r.2

private lemma relPoly_eq_zero_of_deg_lt (H : HomCircuit K m) (a : ℕ) (w u : Fin H.size)
    (hlt : H.deg u < H.deg w) : H.relPoly a w u = 0 := by
  induction hk : u.1 using Nat.strongRecOn generalizing u with
  | ind n ih =>
    subst hk
    rw [relPoly.eq_def]
    split_ifs with h1 h2
    · rfl
    · subst h2; omega
    · cases hg : H.gates u with
      | zero => rfl
      | var _ => rfl
      | add ts =>
        dsimp only
        have hzero : ∀ t ∈ ts, MvPolynomial.C t.1 * H.relPoly a w (lift t.2) = 0 := fun t ht => by
          rw [ih t.2.1 t.2.2 (lift t.2) (by rw [H.add_ok u ts hg t ht]; exact hlt) rfl, mul_zero]
        have hmap : (ts.map fun t => MvPolynomial.C t.1 * H.relPoly a w (lift t.2)) =
            ts.map fun _ => (0 : MvPolynomial (Fin m) K) := List.map_congr_left hzero
        rw [hmap]; simp
      | mul l r =>
        have hsum := H.mul_ok u l r hg
        have hl1 := H.deg_pos (lift l)
        have hr1 := H.deg_pos (lift r)
        dsimp only [lift] at hsum hl1 hr1 ⊢
        split_ifs
        · rw [ih l.1 l.2 (lift l) (by dsimp only [lift]; omega) rfl, zero_mul]
        · rw [ih r.1 r.2 (lift r) (by dsimp only [lift]; omega) rfl, mul_zero]
        · rfl

private lemma relPoly_totalDegree_le (H : HomCircuit K m) (a : ℕ) (w u : Fin H.size) :
    (H.relPoly a w u).totalDegree ≤ H.deg u - H.deg w := by
  induction hk : u.1 using Nat.strongRecOn generalizing u with
  | ind n ih =>
    subst hk
    by_cases hlt : H.deg u < H.deg w
    · rw [H.relPoly_eq_zero_of_deg_lt a w u hlt]; simp
    · rw [relPoly.eq_def]
      split_ifs with h1 h2
      · simp
      · subst h2; simp
      · cases hg : H.gates u with
        | zero => simp
        | var _ => simp
        | add ts =>
          exact list_C_mul_sum_totalDegree_le ts (fun j => H.relPoly a w (lift (i := u) j))
            (H.deg u - H.deg w) fun t ht => by
              have hd := ih t.2.1 t.2.2 (lift (i := u) t.2) rfl
              rwa [H.add_ok u ts hg t ht] at hd
        | mul l r =>
          have hsum := H.mul_ok u l r hg
          dsimp only
          split_ifs
          · by_cases hltl : H.deg (lift l) < H.deg w
            · rw [H.relPoly_eq_zero_of_deg_lt a w (lift l) hltl, zero_mul]; simp
            · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
              have h1 := ih l.1 l.2 (lift l) rfl
              have h2 := H.poly_totalDegree_le (lift r)
              dsimp only [lift] at hsum h1 h2 hltl ⊢
              omega
          · by_cases hltr : H.deg (lift r) < H.deg w
            · rw [H.relPoly_eq_zero_of_deg_lt a w (lift r) hltr, mul_zero]; simp
            · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
              have h1 := H.poly_totalDegree_le (lift l)
              have h2 := ih r.1 r.2 (lift r) rfl
              dsimp only [lift] at hsum h1 h2 hltr ⊢
              omega
          · simp

private lemma relPoly_varsIn (H : HomCircuit K m) (a : ℕ) (w u : Fin H.size) :
    VarsIn H.activeVars (H.relPoly a w u) := by
  induction hk : u.1 using Nat.strongRecOn generalizing u with
  | ind n ih =>
    subst hk
    rw [relPoly.eq_def]
    split_ifs with h1 h2
    · exact varsIn_zero _
    · exact varsIn_C _ 1
    · cases hg : H.gates u with
      | zero => exact varsIn_zero _
      | var _ => exact varsIn_zero _
      | add ts =>
        refine varsIn_list_sum _ fun p hp => ?_
        rcases List.mem_map.mp hp with ⟨t, _, rfl⟩
        exact varsIn_mul (varsIn_C _ _) (ih t.2.1 t.2.2 (lift t.2) rfl)
      | mul l r =>
        dsimp only
        split_ifs
        · exact varsIn_mul (ih l.1 l.2 (lift l) rfl) (H.poly_varsIn (lift r))
        · exact varsIn_mul (H.poly_varsIn (lift l)) (ih r.1 r.2 (lift r) rfl)
        · exact varsIn_zero _

/-- **Linear Frontier Identity**: for any threshold `a ≥ 1` and any gate `u` with
`a < deg u ≤ 2 * a`, `H.poly u = ∑_{w ∈ frontier a} [u : w] * H.poly w`. -/
private lemma poly_eq_sum_frontier (H : HomCircuit K m) {a : ℕ} (_ha : 1 ≤ a) (u : Fin H.size)
    (hlo : a < H.deg u) (hhi : H.deg u ≤ 2 * a) :
    let F : Finset (Fin H.size) := by
      classical exact Finset.univ.filter fun w => H.IsFrontier a w
    H.poly u = ∑ w ∈ F, H.relPoly a w u * H.poly w := by
  classical
  intro F
  induction hk : u.1 using Nat.strongRecOn generalizing u with
  | ind n ih =>
    subst hk
    have hnotle : ¬ H.deg u ≤ a := by omega
    cases hg : H.gates u with
    | zero =>
      rw [H.poly_zero hg]
      symm
      refine Finset.sum_eq_zero fun w hw => ?_
      have hne : u ≠ w := by
        rintro rfl
        rcases (Finset.mem_filter.mp hw).2 with ⟨_, _, hgw, _⟩
        rw [hg] at hgw; cases hgw
      rw [relPoly.eq_def]
      simp only [hnotle, hne, ↓reduceIte, hg, zero_mul]
    | var v =>
      have := (H.var_ok u v hg).1; omega
    | add ts =>
      rw [H.poly_add hg]
      have hrel : ∀ w ∈ F, H.relPoly a w u =
          (ts.map fun t => MvPolynomial.C t.1 * H.relPoly a w (lift t.2)).sum := fun w hw => by
        have hne : u ≠ w := by
          rintro rfl
          rcases (Finset.mem_filter.mp hw).2 with ⟨_, _, hgw, _⟩
          rw [hg] at hgw; cases hgw
        rw [relPoly.eq_def]
        simp only [hnotle, hne, ↓reduceIte, hg]
      have hstep : ∀ (l : List (K × Fin u.1)), (∀ t ∈ l, H.deg (lift (i := u) t.2) = H.deg u) →
          (l.map fun t => MvPolynomial.C t.1 * H.poly (lift (i := u) t.2)).sum =
          ∑ w ∈ F, (l.map fun t => MvPolynomial.C t.1 * H.relPoly a w (lift (i := u) t.2)).sum *
            H.poly w := by
        intro l
        induction l with
        | nil => intro _; simp
        | cons t ts' ihl =>
          intro hok
          rw [List.map_cons, List.sum_cons, ihl fun s hs => hok s (List.mem_cons_of_mem t hs)]
          have htdeg := hok t List.mem_cons_self
          rw [ih t.2.1 t.2.2 (lift (i := u) t.2) (by omega) (by omega) rfl, Finset.mul_sum,
            ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun w _ => ?_
          rw [List.map_cons, List.sum_cons, add_mul, mul_assoc]
      calc (ts.map fun t => MvPolynomial.C t.1 * H.poly (lift t.2)).sum
          = ∑ w ∈ F, (ts.map fun t => MvPolynomial.C t.1 * H.relPoly a w (lift t.2)).sum *
              H.poly w := hstep ts (H.add_ok u ts hg)
        _ = ∑ w ∈ F, H.relPoly a w u * H.poly w :=
            Finset.sum_congr rfl fun w hw => by rw [hrel w hw]
    | mul l r =>
      have hsum := H.mul_ok u l r hg
      by_cases hl : a < H.deg (lift l)
      · have hr : H.deg (lift r) ≤ a := by dsimp only [lift] at hsum hl ⊢; omega
        have hnotF : u ∉ F := by
          intro hu; rcases (Finset.mem_filter.mp hu).2 with ⟨l', r', hgw, _, hl', _⟩
          rw [hg] at hgw; injection hgw with hl_eq _; subst hl_eq; omega
        have hrel : ∀ w ∈ F, H.relPoly a w u = H.relPoly a w (lift l) * H.poly (lift r) :=
          fun w hw => by
            have hne : u ≠ w := fun h => hnotF (h ▸ hw)
            rw [relPoly.eq_def]
            simp only [hnotle, hne, ↓reduceIte, hg, hl, hr, and_self]
        rw [H.poly_mul hg, ih l.1 l.2 (lift l) hl
            (by have := H.deg_pos (lift r); dsimp only [lift] at hsum this ⊢; omega) rfl,
          Finset.sum_mul]
        refine Finset.sum_congr rfl fun w hw => ?_
        rw [hrel w hw]; ring
      · by_cases hr : a < H.deg (lift r)
        · have hl' : H.deg (lift l) ≤ a := by omega
          have hnotF : u ∉ F := by
            intro hu; rcases (Finset.mem_filter.mp hu).2 with ⟨l', r', hgw, _, _, hr'⟩
            rw [hg] at hgw; injection hgw with _ hr_eq; subst hr_eq; omega
          have hrel : ∀ w ∈ F, H.relPoly a w u = H.poly (lift l) * H.relPoly a w (lift r) :=
            fun w hw => by
              have hne : u ≠ w := fun h => hnotF (h ▸ hw)
              rw [relPoly.eq_def]
              simp only [hnotle, hne, ↓reduceIte, hg, hl, hl', hr, false_and, and_self]
          rw [H.poly_mul hg, ih r.1 r.2 (lift r) hr
              (by have := H.deg_pos (lift l); dsimp only [lift] at hsum this ⊢; omega) rfl,
            Finset.mul_sum]
          refine Finset.sum_congr rfl fun w hw => ?_
          rw [hrel w hw]; ring
        · have hl' : H.deg (lift l) ≤ a := by omega
          have hr' : H.deg (lift r) ≤ a := by omega
          have huF : u ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ u, l, r, hg, hlo, hl', hr'⟩
          rw [Finset.sum_eq_single u]
          · rw [relPoly.eq_def]; simp only [hnotle, ↓reduceIte, one_mul]
          · intro w _ hwu
            rw [relPoly.eq_def]
            simp only [hnotle, Ne.symm hwu, ↓reduceIte, hg, hl, hr, false_and, and_false, zero_mul]
          · intro hnot; exact absurd huF hnot

/-- Recursive homogeneous frontier sum-of-products decomposition at any threshold `t ≥ 1`. -/
private theorem frontier_sum_of_prods (H : HomCircuit K m) {t : ℕ} (ht : 1 ≤ t) :
    ∀ (D : ℕ) (u : Fin H.size), H.deg u = D →
      ∃ L : List (List (MvPolynomial (Fin m) K)),
        (L.map List.prod).sum = H.poly u ∧
        L.length ≤ (max 1 H.size) ^ (if D ≤ t then 0 else 2 * ((D - 1) / t) - 1) ∧
        (∀ ps ∈ L, ps.length ≤ if D ≤ t then 1 else 4 * ((D - 1) / t) - 1) ∧
        (∀ ps ∈ L, ∀ q ∈ ps, q.totalDegree ≤ t ∧ VarsIn H.activeVars q) := by
  classical
  intro D
  induction D using Nat.strongRecOn with
  | ind D ih =>
    intro u hDu
    by_cases hle : D ≤ t
    · refine ⟨[[H.poly u]], by simp, by simp [hle], fun ps hps => by
        simp only [List.mem_singleton] at hps; subst hps; simp [hle],
        fun ps hps q hq => ?_⟩
      simp only [List.mem_singleton] at hps; subst hps
      simp only [List.mem_singleton] at hq; subst hq
      exact ⟨(H.poly_totalDegree_le u).trans (by omega), H.poly_varsIn u⟩
    · have hDgt : t < D := by omega
      let a : ℕ := if D ≤ 2 * t then t else D - t
      have ha1 : 1 ≤ a := by dsimp only [a]; split_ifs <;> omega
      have hlo : a < H.deg u := by dsimp only [a]; split_ifs <;> omega
      have hhi : H.deg u ≤ 2 * a := by dsimp only [a]; split_ifs <;> omega
      let F : Finset (Fin H.size) := Finset.univ.filter fun w => H.IsFrontier a w
      let F' : Finset (Fin H.size) := F.filter fun w => H.deg w ≤ D
      have hpoly_F' : H.poly u = ∑ w ∈ F', H.relPoly a w u * H.poly w := by
        rw [H.poly_eq_sum_frontier ha1 u hlo hhi]
        symm
        refine Finset.sum_subset (Finset.filter_subset _ _) fun w hw hnot => ?_
        have hgt : D < H.deg w := by
          simp only [F', Finset.mem_filter] at hnot
          by_contra hle'
          exact hnot ⟨hw, not_lt.mp hle'⟩
        rw [H.relPoly_eq_zero_of_deg_lt a w u (by omega), zero_mul]
      -- For each `w ∈ F'`, construct a list `Lw` representing `relPoly a w u * H.poly w`.
      have hterm : ∀ w ∈ F', ∃ Lw : List (List (MvPolynomial (Fin m) K)),
          (Lw.map List.prod).sum = H.relPoly a w u * H.poly w ∧
          Lw.length ≤ (max 1 H.size) ^ (2 * ((D - 1) / t) - 2) ∧
          (∀ ps ∈ Lw, ps.length ≤ 4 * ((D - 1) / t) - 1) ∧
          (∀ ps ∈ Lw, ∀ q ∈ ps, q.totalDegree ≤ t ∧ VarsIn H.activeVars q) := by
        intro w hw
        have hwF : H.IsFrontier a w := (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).2
        have hwle : H.deg w ≤ D := (Finset.mem_filter.mp hw).2
        rcases hwF with ⟨l, r, hgw, hwa, hla, hra⟩
        have hrel_deg : (H.relPoly a w u).totalDegree ≤ t := by
          have h1 := H.relPoly_totalDegree_le a w u
          dsimp only [a] at hwa; split_ifs at hwa <;> omega
        have hrel_vars : VarsIn H.activeVars (H.relPoly a w u) := H.relPoly_varsIn a w u
        by_cases h2t : D ≤ 2 * t
        · have ha_eq : a = t := by simp [a, h2t]
          have hq1 : 1 ≤ (D - 1) / t := Nat.div_pos (by omega) ht
          refine ⟨[[H.relPoly a w u, H.poly (lift l), H.poly (lift r)]], ?_, ?_, ?_, ?_⟩
          · rw [H.poly_mul hgw]; simp
          · simp [Nat.one_le_pow]
          · intro ps hps; simp only [List.mem_singleton] at hps; subst hps; simp; omega
          · intro ps hps q hq
            simp only [List.mem_singleton] at hps; subst hps
            rcases List.mem_cons.mp hq with rfl | hq'
            · exact ⟨hrel_deg, hrel_vars⟩
            · rcases List.mem_cons.mp hq' with rfl | hq''
              · exact ⟨(H.poly_totalDegree_le (lift l)).trans (by omega), H.poly_varsIn _⟩
              · simp only [List.mem_singleton] at hq''; subst hq''
                exact ⟨(H.poly_totalDegree_le (lift r)).trans (by omega), H.poly_varsIn _⟩
        · have ha_eq : a = D - t := by simp [a, h2t]
          have hsum_lr : H.deg (lift l) + H.deg (lift r) = H.deg w := H.mul_ok w l r hgw
          have hlD : H.deg (lift l) < D := by omega
          have hrD : H.deg (lift r) < D := by omega
          rcases ih (H.deg (lift l)) hlD (lift l) rfl with ⟨L₁, hs₁, hlen₁, hk₁, hq₁⟩
          rcases ih (H.deg (lift r)) hrD (lift r) rfl with ⟨L₂, hs₂, hlen₂, hk₂, hq₂⟩
          let Lw : List (List (MvPolynomial (Fin m) K)) :=
            L₁.flatMap fun p₁ => L₂.map fun p₂ => H.relPoly a w u :: (p₁ ++ p₂)
          -- Arithmetic bounds on the exponents `g` and factor counts `k`.
          set D₁ := H.deg (lift l)
          set D₂ := H.deg (lift r)
          have hD1_pos : 1 ≤ D₁ := H.deg_pos (lift l)
          have hD2_pos : 1 ≤ D₂ := H.deg_pos (lift r)
          have hq_ge2 : 2 ≤ (D - 1) / t := by
            have : 2 * t ≤ D - 1 := by omega
            calc 2 = (2 * t) / t := (Nat.mul_div_left 2 ht).symm
              _ ≤ (D - 1) / t := Nat.div_le_div_right this
          have hq_sub : ∀ X : ℕ, X + t ≤ D → (X - 1) / t ≤ (D - 1) / t - 1 := fun X hX => by
            have h2 := Nat.div_le_div_right (c := t) (show X - 1 + t ≤ D - 1 by omega)
            rw [Nat.add_div_right _ ht] at h2; omega
          have hq1_le : (D₁ - 1) / t ≤ (D - 1) / t - 1 := hq_sub D₁ (by omega)
          have hq2_le : (D₂ - 1) / t ≤ (D - 1) / t - 1 := hq_sub D₂ (by omega)
          have hq_add : (D₁ - 1) / t + (D₂ - 1) / t ≤ (D - 1) / t := by
            have h1 : ((D₁ - 1) / t) * t ≤ D₁ - 1 := Nat.div_mul_le_self _ _
            have h2 : ((D₂ - 1) / t) * t ≤ D₂ - 1 := Nat.div_mul_le_self _ _
            have h3 : (((D₁ - 1) / t) + ((D₂ - 1) / t)) * t ≤ D - 1 := by
              rw [Nat.add_mul]; omega
            calc (D₁ - 1) / t + (D₂ - 1) / t
                = (((D₁ - 1) / t) + ((D₂ - 1) / t)) * t / t := (Nat.mul_div_cancel _ ht).symm
              _ ≤ (D - 1) / t := Nat.div_le_div_right h3
          have hexp_le : (if D₁ ≤ t then 0 else 2 * ((D₁ - 1) / t) - 1) +
              (if D₂ ≤ t then 0 else 2 * ((D₂ - 1) / t) - 1) ≤ 2 * ((D - 1) / t) - 2 := by
            split_ifs with h1 h2 <;>
              (try have : 1 ≤ (D₁ - 1) / t := Nat.div_pos (by omega) ht) <;>
              (try have : 1 ≤ (D₂ - 1) / t := Nat.div_pos (by omega) ht) <;> omega
          have hk_le : 1 + (if D₁ ≤ t then 1 else 4 * ((D₁ - 1) / t) - 1) +
              (if D₂ ≤ t then 1 else 4 * ((D₂ - 1) / t) - 1) ≤ 4 * ((D - 1) / t) - 1 := by
            split_ifs with h1 h2 <;>
              (try have : 1 ≤ (D₁ - 1) / t := Nat.div_pos (by omega) ht) <;>
              (try have : 1 ≤ (D₂ - 1) / t := Nat.div_pos (by omega) ht) <;> omega
          refine ⟨Lw, ?_, ?_, ?_, ?_⟩
          · rw [H.poly_mul hgw, ← hs₁, ← hs₂]
            have hflat : ∀ (A B : List (List (MvPolynomial (Fin m) K)))
                (c : MvPolynomial (Fin m) K),
                ((A.flatMap fun p₁ => B.map fun p₂ => c :: (p₁ ++ p₂)).map List.prod).sum =
                  c * ((A.map List.prod).sum * (B.map List.prod).sum) := by
              intro A B c
              induction A with
              | nil => simp
              | cons p₁ As ihA =>
                simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
                  List.sum_cons, ihA]
                have hinner : ∀ (B' : List (List (MvPolynomial (Fin m) K))),
                    ((B'.map fun p₂ => c :: (p₁ ++ p₂)).map List.prod).sum =
                      c * (p₁.prod * (B'.map List.prod).sum) := by
                  intro B'
                  induction B' with
                  | nil => simp
                  | cons p₂ Bs ihB =>
                    rw [List.map_cons, List.map_cons, List.sum_cons, List.prod_cons,
                      List.prod_append, ihB, List.map_cons, List.sum_cons]
                    ring
                rw [hinner B]; ring
            exact hflat L₁ L₂ (H.relPoly a w u)
          · have hlen_flat : Lw.length = L₁.length * L₂.length := by
              dsimp only [Lw]
              have : ∀ (A : List (List (MvPolynomial (Fin m) K))),
                  (A.flatMap fun p₁ => L₂.map fun p₂ => H.relPoly a w u :: (p₁ ++ p₂)).length =
                    A.length * L₂.length := by
                intro A
                induction A with
                | nil => simp
                | cons _ As ihA => simp [List.flatMap_cons, ihA, Nat.succ_mul, add_comm]
              exact this L₁
            rw [hlen_flat]
            calc L₁.length * L₂.length
                ≤ (max 1 H.size) ^ (if D₁ ≤ t then 0 else 2 * ((D₁ - 1) / t) - 1) *
                  (max 1 H.size) ^ (if D₂ ≤ t then 0 else 2 * ((D₂ - 1) / t) - 1) :=
                  Nat.mul_le_mul hlen₁ hlen₂
              _ = (max 1 H.size) ^ ((if D₁ ≤ t then 0 else 2 * ((D₁ - 1) / t) - 1) +
                    (if D₂ ≤ t then 0 else 2 * ((D₂ - 1) / t) - 1)) := (pow_add _ _ _).symm
              _ ≤ (max 1 H.size) ^ (2 * ((D - 1) / t) - 2) :=
                  Nat.pow_le_pow_right (le_max_left 1 _) hexp_le
          · intro ps hps
            rcases List.mem_flatMap.mp hps with ⟨p₁, hp₁, hps'⟩
            rcases List.mem_map.mp hps' with ⟨p₂, hp₂, rfl⟩
            simp only [List.length_cons, List.length_append]
            have h1 := hk₁ p₁ hp₁; have h2 := hk₂ p₂ hp₂; omega
          · intro ps hps q hq
            rcases List.mem_flatMap.mp hps with ⟨p₁, hp₁, hps'⟩
            rcases List.mem_map.mp hps' with ⟨p₂, hp₂, rfl⟩
            rcases List.mem_cons.mp hq with rfl | hq'
            · exact ⟨hrel_deg, hrel_vars⟩
            · rcases List.mem_append.mp hq' with h1 | h2
              · exact hq₁ p₁ hp₁ q h1
              · exact hq₂ p₂ hp₂ q h2
      -- Concatenate `Lw` over all `w ∈ F'.toList`.
      choose Lw hLw_sum hLw_len hLw_k hLw_q using hterm
      let L : List (List (MvPolynomial (Fin m) K)) :=
        F'.toList.attach.flatMap fun ⟨w, hw⟩ => Lw w (Finset.mem_toList.mp hw)
      have hq_ge1 : 1 ≤ (D - 1) / t := Nat.div_pos (by omega) ht
      have hcard_F' : F'.card ≤ max 1 H.size := by
        calc F'.card ≤ (Finset.univ : Finset (Fin H.size)).card := Finset.card_le_univ F'
          _ = H.size := by simp
          _ ≤ max 1 H.size := le_max_right 1 _
      refine ⟨L, ?_, ?_, ?_, ?_⟩
      · rw [hpoly_F']
        have hsum_attach : ∀ (l : List (Fin H.size)) (hl : ∀ w ∈ l, w ∈ F'),
            ((l.attach.flatMap fun ⟨w, hw⟩ => Lw w (hl w hw)).map List.prod).sum =
              (l.map fun w => H.relPoly a w u * H.poly w).sum := by
          intro l
          induction l with
          | nil => intro _; simp
          | cons w ws ihw =>
            intro hl
            simp only [List.attach_cons, List.flatMap_cons, List.map_append, List.sum_append,
              List.map_cons, List.sum_cons, hLw_sum w (hl w List.mem_cons_self)]
            congr 1
            have heq : (ws.attach.map (fun x : {x // x ∈ ws} =>
                  (⟨x.1, List.mem_cons_of_mem w x.2⟩ : {x // x ∈ w :: ws}))).flatMap
                  (fun ⟨x, hx⟩ => Lw x (hl x hx)) =
                ws.attach.flatMap (fun ⟨x, hx⟩ => Lw x (hl x (List.mem_cons_of_mem w hx))) := by
              rw [List.flatMap_map]
            rw [heq]
            exact ihw fun x hx => hl x (List.mem_cons_of_mem w hx)
        have htoList : (F'.toList.map fun w => H.relPoly a w u * H.poly w).sum =
            ∑ w ∈ F', H.relPoly a w u * H.poly w := by
          rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]; rfl
        rw [← htoList]
        exact hsum_attach F'.toList (fun w hw => Finset.mem_toList.mp hw)
      · simp only [hle, ↓reduceIte]
        have hlen_attach : ∀ (l : List (Fin H.size)) (hl : ∀ w ∈ l, w ∈ F'),
            (l.attach.flatMap fun ⟨w, hw⟩ => Lw w (hl w hw)).length ≤
              l.length * (max 1 H.size) ^ (2 * ((D - 1) / t) - 2) := by
          intro l
          induction l with
          | nil => intro _; simp
          | cons w ws ihw =>
            intro hl
            rw [List.attach_cons, List.flatMap_cons, List.length_append, List.length_cons,
              Nat.succ_mul]
            have heq : (ws.attach.map (fun x : {x // x ∈ ws} =>
                  (⟨x.1, List.mem_cons_of_mem w x.2⟩ : {x // x ∈ w :: ws}))).flatMap
                  (fun ⟨x, hx⟩ => Lw x (hl x hx)) =
                ws.attach.flatMap (fun ⟨x, hx⟩ => Lw x (hl x (List.mem_cons_of_mem w hx))) := by
              rw [List.flatMap_map]
            rw [heq]
            have h1 := hLw_len w (hl w List.mem_cons_self)
            have h2 := ihw fun x hx => hl x (List.mem_cons_of_mem w hx)
            exact (Nat.add_le_add h1 h2).trans_eq (add_comm _ _)
        have hlenL := hlen_attach F'.toList (fun w hw => Finset.mem_toList.mp hw)
        rw [Finset.length_toList] at hlenL
        have hexp : 2 * ((D - 1) / t) - 2 + 1 = 2 * ((D - 1) / t) - 1 := by omega
        calc L.length ≤ F'.card * (max 1 H.size) ^ (2 * ((D - 1) / t) - 2) := hlenL
          _ ≤ max 1 H.size * (max 1 H.size) ^ (2 * ((D - 1) / t) - 2) :=
              Nat.mul_le_mul_right _ hcard_F'
          _ = (max 1 H.size) ^ (2 * ((D - 1) / t) - 2 + 1) := by rw [pow_succ, mul_comm]
          _ = (max 1 H.size) ^ (2 * ((D - 1) / t) - 1) := by rw [hexp]
      · intro ps hps
        simp only [hle, ↓reduceIte]
        rcases List.mem_flatMap.mp hps with ⟨⟨w, hw⟩, _, hps'⟩
        exact hLw_k w (Finset.mem_toList.mp hw) ps hps'
      · intro ps hps q hq
        rcases List.mem_flatMap.mp hps with ⟨⟨w, hw⟩, _, hps'⟩
        exact hLw_q w (Finset.mem_toList.mp hw) ps hps' q hq

end HomCircuit

end HomCircuitFrontier

/-! ### Active-Variable Homogenization of `Circuit (arithSignature K) m 1` -/

section ActiveHomogenization

variable {K : Type u} [CommSemiring K] {m : ℕ}

/-- Active input variables referenced by a `Circuit (arithSignature K) m 1`. -/
private def circuitActiveVars (c : Circuit (arithSignature K) m 1) : Finset (Fin m) :=
  let wireVar : Wire m c.size → Finset (Fin m)
    | .input v => {v}
    | .gate _ => ∅
  wireVar (c.outputs 0) ∪
    Finset.univ.biUnion fun k : Fin c.size =>
      Finset.univ.biUnion fun a : Fin ((arithSignature K).Arity (c.program.lines k).op) =>
        wireVar ((c.program.lines k).wires a)

omit [CommSemiring K] in
private lemma card_circuitActiveVars_le (c : Circuit (arithSignature K) m 1) :
    (circuitActiveVars c).card ≤ min m (2 * c.size + 1) := by
  refine le_min (Finset.card_le_univ _ |>.trans (by simp)) ?_
  dsimp only [circuitActiveVars]
  have hwire : ∀ w : Wire m c.size,
      (match w with | .input v => ({v} : Finset (Fin m)) | .gate _ => ∅).card ≤ 1 := by
    intro w; cases w <;> simp
  have hline : ∀ k : Fin c.size,
      (Finset.univ.biUnion fun a : Fin ((arithSignature K).Arity (c.program.lines k).op) =>
        match (c.program.lines k).wires a with
          | .input v => ({v} : Finset (Fin m)) | .gate _ => ∅).card
        ≤ 2 := by
    intro k
    refine (Finset.card_biUnion_le).trans ?_
    have hsum : ∑ a : Fin ((arithSignature K).Arity (c.program.lines k).op),
        (match (c.program.lines k).wires a with
          | .input v => ({v} : Finset (Fin m)) | .gate _ => ∅).card ≤
        ∑ _a : Fin ((arithSignature K).Arity (c.program.lines k).op), 1 :=
      Finset.sum_le_sum fun a _ => hwire _
    refine hsum.trans ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    cases (c.program.lines k).op <;> simp
  calc ((match c.outputs 0 with | .input v => ({v} : Finset (Fin m)) | .gate _ => ∅) ∪
          Finset.univ.biUnion fun k : Fin c.size =>
            Finset.univ.biUnion fun a : Fin ((arithSignature K).Arity (c.program.lines k).op) =>
              match (c.program.lines k).wires a with
                | .input v => ({v} : Finset (Fin m)) | .gate _ => ∅).card
      ≤ (match c.outputs 0 with | .input v => ({v} : Finset (Fin m)) | .gate _ => ∅).card +
        (Finset.univ.biUnion fun k : Fin c.size =>
          Finset.univ.biUnion fun a : Fin ((arithSignature K).Arity (c.program.lines k).op) =>
            match (c.program.lines k).wires a with
              | .input v => ({v} : Finset (Fin m)) | .gate _ => ∅).card := Finset.card_union_le _ _
    _ ≤ 1 + ∑ k : Fin c.size, 2 :=
        Nat.add_le_add (hwire _)
          ((Finset.card_biUnion_le).trans (Finset.sum_le_sum fun k _ => hline k))
    _ = 2 * c.size + 1 := by simp [mul_comm, add_comm]

/-- Snoc one gate onto a `HomCircuit`. -/
private def HomCircuit.snoc (H : HomCircuit K m) (d : ℕ) (hd : 1 ≤ d)
    (g : HomGate K m H.size)
    (hvar : ∀ v, g = .var v → d = 1 ∧ v ∈ H.activeVars)
    (hadd : ∀ ts, g = .add ts → ∀ t ∈ ts, H.deg t.2 = d)
    (hmul : ∀ l r, g = .mul l r → H.deg l + H.deg r = d) : HomCircuit K m where
  size := H.size + 1
  activeVars := H.activeVars
  deg i := Fin.lastCases d H.deg i
  deg_pos i := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hd
    · simpa using H.deg_pos j
  gates i := Fin.lastCases (motive := fun i : Fin (H.size + 1) => HomGate K m i.1) g
    (fun j => H.gates j) i
  var_ok i := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · intro v h; simp only [Fin.lastCases_last] at h ⊢; exact hvar v h
    · intro v h; simp only [Fin.lastCases_castSucc] at h ⊢; exact H.var_ok j v h
  add_ok i := by
    refine Fin.lastCases (fun ts h t ht => ?_) (fun j ts h t ht => ?_) i
    · simp only [Fin.lastCases_last] at h ⊢
      exact (Fin.lastCases_castSucc t.2).trans (hadd ts h t ht)
    · simp only [Fin.lastCases_castSucc] at h ⊢
      exact (Fin.lastCases_castSucc (⟨t.2.1, lt_trans t.2.2 j.2⟩ : Fin H.size)).trans
        (H.add_ok j ts h t ht)
  mul_ok i := by
    refine Fin.lastCases (fun l r h => ?_) (fun j l r h => ?_) i
    · simp only [Fin.lastCases_last] at h ⊢
      change Fin.lastCases d H.deg l.castSucc + Fin.lastCases d H.deg r.castSucc = d
      simp only [Fin.lastCases_castSucc]; exact hmul l r h
    · simp only [Fin.lastCases_castSucc] at h ⊢
      change Fin.lastCases d H.deg (⟨l.1, lt_trans l.2 j.2⟩ : Fin H.size).castSucc +
        Fin.lastCases d H.deg (⟨r.1, lt_trans r.2 j.2⟩ : Fin H.size).castSucc = H.deg j
      simp only [Fin.lastCases_castSucc]; exact H.mul_ok j l r h

private lemma HomCircuit.poly_snoc_castSucc (H : HomCircuit K m) (d : ℕ) (hd : 1 ≤ d)
    (g : HomGate K m H.size) (hv) (ha) (hm) (i : Fin H.size) :
    (H.snoc d hd g hv ha hm).poly i.castSucc = H.poly i := by
  induction hk : i.1 using Nat.strongRecOn generalizing i with
  | ind n ih =>
    subst hk
    have hgi : (H.snoc d hd g hv ha hm).gates i.castSucc = H.gates i := by
      simp [HomCircuit.snoc]
    cases hg : H.gates i with
    | zero => rw [(H.snoc d hd g hv ha hm).poly_zero (hgi.trans hg), H.poly_zero hg]
    | var v => rw [(H.snoc d hd g hv ha hm).poly_var (hgi.trans hg), H.poly_var hg]
    | add ts =>
      rw [(H.snoc d hd g hv ha hm).poly_add (hgi.trans hg), H.poly_add hg]
      congr 1; refine List.map_congr_left fun t _ => ?_; congr 1
      have ht : HomCircuit.lift (H := H.snoc d hd g hv ha hm) (i := i.castSucc) t.2 =
          (HomCircuit.lift (H := H) (i := i) t.2).castSucc := rfl
      rw [ht]
      exact ih t.2.1 t.2.2 (HomCircuit.lift t.2) rfl
    | mul l r =>
      have hl : HomCircuit.lift (H := H.snoc d hd g hv ha hm) (i := i.castSucc) l =
          (HomCircuit.lift (H := H) (i := i) l).castSucc := rfl
      have hr : HomCircuit.lift (H := H.snoc d hd g hv ha hm) (i := i.castSucc) r =
          (HomCircuit.lift (H := H) (i := i) r).castSucc := rfl
      rw [(H.snoc d hd g hv ha hm).poly_mul (hgi.trans hg), H.poly_mul hg, hl, hr,
        ih l.1 l.2 (HomCircuit.lift l) rfl, ih r.1 r.2 (HomCircuit.lift r) rfl]

omit [CommSemiring K] in
private lemma HomCircuit.gates_snoc_last (H : HomCircuit K m) (d : ℕ) (hd : 1 ≤ d)
    (g : HomGate K m H.size) (hv) (ha) (hm) :
    (H.snoc d hd g hv ha hm).gates (Fin.last H.size) = g := by
  simp [HomCircuit.snoc]

private lemma HomCircuit.poly_snoc_zero (H : HomCircuit K m) (d : ℕ) (hd : 1 ≤ d)
    (hv) (ha) (hm) :
    (H.snoc d hd .zero hv ha hm).poly (Fin.last H.size) = 0 :=
  (H.snoc d hd .zero hv ha hm).poly_zero (H.gates_snoc_last d hd .zero hv ha hm)

private lemma HomCircuit.poly_snoc_var (H : HomCircuit K m) (d : ℕ) (hd : 1 ≤ d) (v : Fin m)
    (hv) (ha) (hm) :
    (H.snoc d hd (.var v) hv ha hm).poly (Fin.last H.size) = X v :=
  (H.snoc d hd (.var v) hv ha hm).poly_var (H.gates_snoc_last d hd (.var v) hv ha hm)

private lemma HomCircuit.poly_snoc_add (H : HomCircuit K m) (d : ℕ) (hd : 1 ≤ d)
    (ts : List (K × Fin H.size)) (hv) (ha) (hm) :
    (H.snoc d hd (.add ts) hv ha hm).poly (Fin.last H.size) =
      (ts.map fun t => MvPolynomial.C t.1 * H.poly t.2).sum := by
  rw [(H.snoc d hd (.add ts) hv ha hm).poly_add (H.gates_snoc_last d hd (.add ts) hv ha hm)]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  congr 1
  have ht : HomCircuit.lift (H := H.snoc d hd (.add ts) hv ha hm) (i := Fin.last H.size) t.2 =
      t.2.castSucc := rfl
  rw [ht, H.poly_snoc_castSucc]

private lemma HomCircuit.poly_snoc_mul (H : HomCircuit K m) (d : ℕ) (hd : 1 ≤ d)
    (l r : Fin H.size) (hv) (ha) (hm) :
    (H.snoc d hd (.mul l r) hv ha hm).poly (Fin.last H.size) = H.poly l * H.poly r := by
  rw [(H.snoc d hd (.mul l r) hv ha hm).poly_mul (H.gates_snoc_last d hd (.mul l r) hv ha hm)]
  have hl : HomCircuit.lift (H := H.snoc d hd (.mul l r) hv ha hm) (i := Fin.last H.size) l =
      l.castSucc := rfl
  have hr : HomCircuit.lift (H := H.snoc d hd (.mul l r) hv ha hm) (i := Fin.last H.size) r =
      r.castSucc := rfl
  rw [hl, hr, H.poly_snoc_castSucc, H.poly_snoc_castSucc]

private def HomExtends (H H' : HomCircuit K m) : Prop :=
  H'.activeVars = H.activeVars ∧
  ∃ hle : H.size ≤ H'.size,
    (∀ i : Fin H.size, H'.deg ⟨i.1, lt_of_lt_of_le i.2 hle⟩ = H.deg i) ∧
    (∀ i : Fin H.size, H'.poly ⟨i.1, lt_of_lt_of_le i.2 hle⟩ = H.poly i)

private lemma homExtends_refl (H : HomCircuit K m) : HomExtends H H :=
  ⟨rfl, le_rfl, fun _ => rfl, fun _ => rfl⟩

private lemma homExtends_trans {H₁ H₂ H₃ : HomCircuit K m}
    (h12 : HomExtends H₁ H₂) (h23 : HomExtends H₂ H₃) : HomExtends H₁ H₃ := by
  rcases h12 with ⟨ha12, hle12, hd12, hp12⟩
  rcases h23 with ⟨ha23, hle23, hd23, hp23⟩
  exact ⟨ha23.trans ha12, hle12.trans hle23,
    fun i => (hd23 ⟨i.1, lt_of_lt_of_le i.2 hle12⟩).trans (hd12 i),
    fun i => (hp23 ⟨i.1, lt_of_lt_of_le i.2 hle12⟩).trans (hp12 i)⟩

private lemma homExtends_snoc (H : HomCircuit K m) (d : ℕ) (hd : 1 ≤ d)
    (g : HomGate K m H.size) (hv) (ha) (hm) : HomExtends H (H.snoc d hd g hv ha hm) :=
  ⟨rfl, Nat.le_succ _,
    fun i => by
      change Fin.lastCases d H.deg i.castSucc = H.deg i
      exact Fin.lastCases_castSucc i,
    fun i => H.poly_snoc_castSucc d hd g hv ha hm i⟩

/-- Build a homogeneous layered circuit `H` computing all positive-degree homogeneous components
`1..d` of `c.polynomial 0`, using ONLY variables in `circuitActiveVars c` and size
`≤ (c.size + 1) * d * (d + 6) + 2`. -/
private theorem circuit_to_homCircuit (c : Circuit (arithSignature K) m 1) (d : ℕ) (hd : 1 ≤ d) :
    ∃ (H : HomCircuit K m) (out : Fin d → Fin H.size),
      H.activeVars = circuitActiveVars c ∧
      H.size ≤ (c.size + 1) * d * (d + 6) + 2 ∧
      ∀ r : Fin d,
        H.deg (out r) = r.1 + 1 ∧
        H.poly (out r) = MvPolynomial.homogeneousComponent (r.1 + 1) (c.polynomial 0) := by
  let V := circuitActiveVars c
  let ev : Fin c.size → MvPolynomial (Fin m) K :=
    c.program.eval (arithInterpretationWith K MvPolynomial.C) X
  let wEval : Wire m c.size → MvPolynomial (Fin m) K := Wire.elim X ev
  -- Build homogeneous components `1..d` for every gate `k < c.size` by induction on `k`.
  have hbuild : ∀ (k : ℕ) (hk : k ≤ c.size),
      ∃ (H : HomCircuit K m) (hom : Fin k → Fin d → Fin H.size),
        H.activeVars = V ∧
        H.size ≤ k * d * (d + 6) + 1 ∧
        ∀ (g : Fin k) (r : Fin d),
          H.deg (hom g r) = r.1 + 1 ∧
          H.poly (hom g r) =
            MvPolynomial.homogeneousComponent (r.1 + 1) (ev ⟨g.1, lt_of_lt_of_le g.2 hk⟩) := by
    intro k
    induction k with
    | zero =>
      intro _
      let H0 : HomCircuit K m :=
        { size := 1
          activeVars := V
          deg := fun _ => 1
          deg_pos := fun _ => le_rfl
          gates := fun _ => .zero
          var_ok := fun _ _ h => by cases h
          add_ok := fun _ _ h => by cases h
          mul_ok := fun _ _ _ h => by cases h }
      exact ⟨H0, fun g => g.elim0, rfl, by simp [H0], fun g => g.elim0⟩
    | succ k ih =>
      intro hk
      rcases ih (Nat.le_of_succ_le hk) with ⟨H0, hom0, hV0, hsz0, hspec0⟩
      let kC : Fin c.size := ⟨k, hk⟩
      have hline := c.program.lines_eval (arithInterpretationWith K MvPolynomial.C) X kC
      -- Helper: for any wire `w` read by line `kC` (so any `.gate j` has `j < k` and any `.input v`
      -- lies in `V`), append at most 1 gate to compute `hom_{s+1}(wEval w)`.
      have hwire_hom : ∀ (H : HomCircuit K m), HomExtends H0 H →
          ∀ (a : Fin ((arithSignature K).Arity (c.program.lines kC).op)) (s : Fin d),
            ∃ (H' : HomCircuit K m) (idx : Fin H'.size),
              HomExtends H H' ∧ H'.size ≤ H.size + 1 ∧
              H'.deg idx = s.1 + 1 ∧
              H'.poly idx = MvPolynomial.homogeneousComponent (s.1 + 1)
                (wEval ((c.program.lines kC).wires a)) := by
        intro H hE a s
        rcases hE with ⟨hVH, hleH, hdH, hpH⟩
        cases hw : (c.program.lines kC).wires a with
        | gate j =>
          have hjlt : j.1 < k := c.program.lt_of_lines_wires_eq_gate kC a j hw
          let u0 := hom0 ⟨j.1, hjlt⟩ s
          refine ⟨H, ⟨u0.1, lt_of_lt_of_le u0.2 hleH⟩, homExtends_refl H, by omega,
            (hdH u0).trans (hspec0 ⟨j.1, hjlt⟩ s).1, (hpH u0).trans (hspec0 ⟨j.1, hjlt⟩ s).2⟩
        | input v =>
          have hvV : v ∈ H.activeVars := by
            rw [hVH, hV0]
            refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨kC, Finset.mem_univ _,
              Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, ?_⟩⟩)
            simp [hw]
          by_cases hs0 : s.1 = 0
          · let H' := H.snoc (s.1 + 1) (Nat.succ_pos _) (.var v)
              (fun _ h => by injection h with hv'; exact ⟨by omega, hv' ▸ hvV⟩)
              (fun _ h => by cases h) (fun _ _ h => by cases h)
            refine ⟨H', Fin.last H.size, homExtends_snoc H _ _ _ _ _ _,
              by change H.size + 1 ≤ _; omega,
              by simp [H', HomCircuit.snoc], ?_⟩
            rw [H.poly_snoc_var]
            simp [wEval, homogeneousComponent_X_eq, hs0]
          · let H' := H.snoc (s.1 + 1) (Nat.succ_pos _) .zero
              (fun _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h)
            refine ⟨H', Fin.last H.size, homExtends_snoc H _ _ _ _ _ _,
              by change H.size + 1 ≤ _; omega,
              by simp [H', HomCircuit.snoc], ?_⟩
            rw [H.poly_snoc_zero]
            simp [wEval, homogeneousComponent_X_eq, hs0]
      have hwire_lt : ∀ (a : Fin ((arithSignature K).Arity (c.program.lines kC).op))
        (j : Fin c.size),
          (c.program.lines kC).wires a = .gate j → j.1 < k :=
        fun a j hw => c.program.lt_of_lines_wires_eq_gate kC a j hw
      -- Inner induction on `s ≤ d`: build components `1..s` for line `kC`.
      have hrow : ∀ (s : ℕ) (hs : s ≤ d),
          ∃ (Hs : HomCircuit K m) (row : Fin s → Fin Hs.size),
            HomExtends H0 Hs ∧ Hs.size ≤ H0.size + s * (d + 6) ∧
            ∀ r : Fin s, Hs.deg (row r) = r.1 + 1 ∧
              Hs.poly (row r) = MvPolynomial.homogeneousComponent (r.1 + 1) (ev kC) := by
        intro s
        induction s with
        | zero =>
          intro _; exact ⟨H0, fun r => r.elim0, homExtends_refl H0, by simp, fun r => r.elim0⟩
        | succ s ihs =>
          intro hs
          rcases ihs (Nat.le_of_succ_le hs) with ⟨H1, row1, hE1, hsz1, hspec1⟩
          have hstep : ∃ (H2 : HomCircuit K m) (idx : Fin H2.size),
              HomExtends H1 H2 ∧ H2.size ≤ H1.size + (d + 6) ∧
              H2.deg idx = s + 1 ∧
              H2.poly idx = MvPolynomial.homogeneousComponent (s + 1) (ev kC) := by
            generalize hl : c.program.lines kC = line at hline hwire_hom hwire_lt
            rcases line with ⟨op, wires⟩
            cases op with
            | const a =>
              let H2 := H1.snoc (s + 1) (Nat.succ_pos s) .zero
                (fun _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h)
              refine ⟨H2, Fin.last H1.size, homExtends_snoc H1 _ _ _ _ _ _,
                by change H1.size + 1 ≤ _; omega, by simp [H2, HomCircuit.snoc], ?_⟩
              rw [H1.poly_snoc_zero]
              have hev : ev kC = MvPolynomial.C a := hline.symm
              rw [hev, homogeneousComponent_C_of_pos (Nat.succ_pos s)]
            | add =>
              rcases hwire_hom H1 hE1 0 ⟨s, hs⟩ with ⟨Ha, u0, hEa, hsza, hd0, hp0⟩
              rcases hwire_hom Ha (homExtends_trans hE1 hEa) 1 ⟨s, hs⟩ with
                ⟨Hb, u1, hEb, hszb, hd1', hp1⟩
              rcases hEb with ⟨hVb, hleb, hdb, hpb⟩
              let u0b : Fin Hb.size := ⟨u0.1, lt_of_lt_of_le u0.2 hleb⟩
              let H2 := Hb.snoc (s + 1) (Nat.succ_pos s) (.add [(1, u0b), (1, u1)])
                (fun _ h => by cases h)
                (fun _ h t ht => by
                  injection h with hts; subst hts
                  rcases List.mem_cons.mp ht with rfl | ht'
                  · exact (hdb u0).trans hd0
                  · simp only [List.mem_singleton] at ht'; subst ht'; exact hd1')
                (fun _ _ h => by cases h)
              refine ⟨H2, Fin.last Hb.size,
                homExtends_trans hEa (homExtends_trans ⟨hVb, hleb, hdb, hpb⟩
                  (homExtends_snoc Hb _ _ _ _ _ _)),
                by change Hb.size + 1 ≤ _; omega, by simp [H2, HomCircuit.snoc], ?_⟩
              rw [Hb.poly_snoc_add]
              simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, map_one, one_mul,
                add_zero]
              rw [hpb u0, hp0, hp1]
              have hev : ev kC = wEval (wires 0) + wEval (wires 1) := hline.symm
              rw [hev, map_add]
            | mul =>
              -- First handle `s = 0` (`d = 1`) and `s ≥ 1` uniformly using
              -- `homogeneousComponent_mul_pos`.
              have hev : ev kC = wEval (wires 0) * wEval (wires 1) := hline.symm
              rcases hwire_hom H1 hE1 0 ⟨s, hs⟩ with ⟨Ha, lS, hEa, hsza, hdlS, hplS⟩
              rcases hwire_hom Ha (homExtends_trans hE1 hEa) 1 ⟨s, hs⟩ with
                ⟨Hb, rS, hEb, hszb, hdrS, hprS⟩
              -- Build degree-1 wire gates once (cost `≤ 2` if `s ≥ 1`), then all `s` products.
              have hbuild_muls : ∀ (t : ℕ) (ht : t ≤ s),
                  ∃ (Ht : HomCircuit K m) (prods : List (Fin Ht.size)),
                    HomExtends Hb Ht ∧
                    Ht.size ≤ Hb.size + t + (if t = 0 then 0 else 2) ∧
                    (∀ u ∈ prods, Ht.deg u = s + 1) ∧
                    (prods.map fun u => Ht.poly u).sum =
                      ∑ j ∈ Finset.range t,
                        MvPolynomial.homogeneousComponent (j + 1) (wEval (wires 0)) *
                        MvPolynomial.homogeneousComponent (s - j) (wEval (wires 1)) := by
                intro t ht
                by_cases ht0 : t = 0
                · subst ht0
                  exact ⟨Hb, [], homExtends_refl Hb, by simp, (fun _ h => by cases h), by simp⟩
                · -- Pre-create degree-1 wire gates for `wires 0` and `wires 1` once (cost ≤ 2).
                  have hd0_lt : 0 < d := by omega
                  rcases hwire_hom Hb (homExtends_trans hE1 (homExtends_trans hEa hEb))
                      0 ⟨0, hd0_lt⟩ with ⟨Hc, l1, hEc, hszc, hdl1, hpl1⟩
                  rcases hwire_hom Hc (homExtends_trans hE1 (homExtends_trans hEa
                      (homExtends_trans hEb hEc))) 1 ⟨0, hd0_lt⟩ with
                    ⟨Hd, r1, hEd, hszd, hdr1, hpr1⟩
                  have hEbd : HomExtends Hb Hd := homExtends_trans hEc hEd
                  have hE0d : HomExtends H0 Hd := homExtends_trans hE1
                    (homExtends_trans hEa (homExtends_trans hEb hEbd))
                  have hloop : ∀ (t' : ℕ) (ht' : t' ≤ s),
                      ∃ (Ht : HomCircuit K m) (prods : List (Fin Ht.size)),
                        HomExtends Hd Ht ∧
                        Ht.size ≤ Hd.size + t' ∧
                        (∀ u ∈ prods, Ht.deg u = s + 1) ∧
                        (prods.map fun u => Ht.poly u).sum =
                          ∑ j ∈ Finset.range t',
                            MvPolynomial.homogeneousComponent (j + 1) (wEval (wires 0)) *
                            MvPolynomial.homogeneousComponent (s - j) (wEval (wires 1)) := by
                    intro t'
                    induction t' with
                    | zero =>
                      intro _
                      exact ⟨Hd, [], homExtends_refl Hd, by simp, (fun _ h => by cases h), by simp⟩
                    | succ t' iht' =>
                      intro ht'
                      rcases iht' (Nat.le_of_succ_le ht') with ⟨Ht, prods, hEt, hszt, hdegt, hsumt⟩
                      rcases homExtends_trans hE0d hEt with ⟨_, hle0t, hd0t, hp0t⟩
                      rcases homExtends_trans hEd hEt with ⟨_, hlect, hdct, hpct⟩
                      rcases hEt with ⟨hVdt, hledt, hddt, hpdt⟩
                      -- Check if either factor is a higher-degree component of an input variable
                      -- (which is identically `0`).
                      have hfindOrZero : ∀ (b : Fin 2) (r : Fin d),
                          (MvPolynomial.homogeneousComponent (r.1 + 1) (wEval (wires b)) = 0) ∨
                          ∃ u : Fin Ht.size, Ht.deg u = r.1 + 1 ∧
                            Ht.poly u = MvPolynomial.homogeneousComponent (r.1 + 1)
                              (wEval (wires b)) := by
                        intro b r
                        cases hw : wires b with
                        | gate j =>
                          have hjlt : j.1 < k := hwire_lt b j hw
                          let u0 := hom0 ⟨j.1, hjlt⟩ r
                          exact Or.inr ⟨⟨u0.1, lt_of_lt_of_le u0.2 hle0t⟩,
                            (hd0t u0).trans (hspec0 ⟨j.1, hjlt⟩ r).1,
                            (hp0t u0).trans (hspec0 ⟨j.1, hjlt⟩ r).2⟩
                        | input v =>
                          by_cases hr0 : r.1 = 0
                          · fin_cases b
                            · refine Or.inr ⟨⟨l1.1, lt_of_lt_of_le l1.2 hlect⟩,
                                (hdct l1).trans (by rw [hdl1, hr0]),
                                (hpct l1).trans ?_⟩
                              rw [hpl1, hr0]
                              exact congrArg
                                (fun w => MvPolynomial.homogeneousComponent 1 (wEval w)) hw
                            · refine Or.inr ⟨⟨r1.1, lt_of_lt_of_le r1.2 hledt⟩,
                                (hddt r1).trans (by rw [hdr1, hr0]),
                                (hpdt r1).trans ?_⟩
                              rw [hpr1, hr0]
                              exact congrArg
                                (fun w => MvPolynomial.homogeneousComponent 1 (wEval w)) hw
                          · left
                            simp [wEval, homogeneousComponent_X_eq, hr0]
                      have hsub_eq : s - 1 - t' + 1 = s - t' := by omega
                      rcases hfindOrZero 0 ⟨t', by omega⟩ with hz0 | ⟨uA, hdA, hpA⟩
                      · refine ⟨Ht, prods, ⟨hVdt, hledt, hddt, hpdt⟩, by omega, hdegt, ?_⟩
                        rw [hsumt, Finset.sum_range_succ, hz0, zero_mul, add_zero]
                      · rcases hfindOrZero 1 ⟨s - 1 - t', by omega⟩ with hz1 | ⟨uB, hdB, hpB⟩
                        · refine ⟨Ht, prods, ⟨hVdt, hledt, hddt, hpdt⟩, by omega, hdegt, ?_⟩
                          rw [hsub_eq] at hz1
                          rw [hsumt, Finset.sum_range_succ, hz1, mul_zero, add_zero]
                        · let Ht' := Ht.snoc (s + 1) (Nat.succ_pos s) (.mul uA uB)
                            (fun _ h => by cases h) (fun _ h => by cases h)
                            (fun l' r' h => by
                              injection h with hl' hr'; subst hl'; subst hr'
                              dsimp only at hdA hdB; rw [hdA, hdB]; omega)
                          refine ⟨Ht', Fin.last Ht.size :: prods.map Fin.castSucc,
                            homExtends_trans ⟨hVdt, hledt, hddt, hpdt⟩
                              (homExtends_snoc Ht _ _ _ _ _ _),
                            by change Ht.size + 1 ≤ _; omega, ?_, ?_⟩
                          · intro u hu
                            rcases List.mem_cons.mp hu with rfl | hu'
                            · simp [Ht', HomCircuit.snoc]
                            · rcases List.mem_map.mp hu' with ⟨w, hw, rfl⟩
                              simp [Ht', HomCircuit.snoc, hdegt w hw]
                          · change ((Fin.last Ht.size :: prods.map Fin.castSucc).map
                                fun u : Fin (Ht.size + 1) => Ht'.poly u).sum = _
                            rw [List.map_cons, List.sum_cons, List.map_map]
                            have hrest : (prods.map ((fun u : Fin (Ht.size + 1) => Ht'.poly u) ∘
                                Fin.castSucc)).sum = (prods.map fun u => Ht.poly u).sum := by
                              congr 1
                              exact List.map_congr_left fun u _ =>
                                Ht.poly_snoc_castSucc _ _ _ _ _ _ u
                            rw [hrest, hsumt, Finset.sum_range_succ, add_comm]
                            congr 1
                            rw [Ht.poly_snoc_mul, hpA, hpB, hsub_eq]
                  rcases hloop t ht with ⟨Ht, prods, hEdt, hszdt, hdegt, hsumt⟩
                  refine ⟨Ht, prods, homExtends_trans hEbd hEdt, ?_, hdegt, hsumt⟩
                  simp only [ht0, ↓reduceIte]
                  omega
              rcases hbuild_muls s le_rfl with ⟨Hm, prods, hEm, hszm, hdegm, hsumm⟩
              rcases homExtends_trans hEb hEm with ⟨_, hleam, hdam, hpam⟩
              rcases hEm with ⟨hVm, hlem, hdm, hpm⟩
              let lSm : Fin Hm.size := ⟨lS.1, lt_of_lt_of_le lS.2 hleam⟩
              let rSm : Fin Hm.size := ⟨rS.1, lt_of_lt_of_le rS.2 hlem⟩
              let terms : List (K × Fin Hm.size) :=
                ((wEval (wires 0)).coeff 0, rSm) :: ((wEval (wires 1)).coeff 0, lSm) ::
                  prods.map fun u => (1, u)
              let H2 := Hm.snoc (s + 1) (Nat.succ_pos s) (.add terms)
                (fun _ h => by cases h)
                (fun _ h t ht => by
                  injection h with hts; subst hts
                  rcases List.mem_cons.mp ht with rfl | ht'
                  · exact (hdm rS).trans hdrS
                  · rcases List.mem_cons.mp ht' with rfl | ht''
                    · exact (hdam lS).trans hdlS
                    · rcases List.mem_map.mp ht'' with ⟨u, hu, rfl⟩; exact hdegm u hu)
                (fun _ _ h => by cases h)
              refine ⟨H2, Fin.last Hm.size,
                homExtends_trans hEa (homExtends_trans hEb
                  (homExtends_trans ⟨hVm, hlem, hdm, hpm⟩ (homExtends_snoc Hm _ _ _ _ _ _))),
                ?_, by simp [H2, HomCircuit.snoc], ?_⟩
              · change Hm.size + 1 ≤ H1.size + (d + 6)
                have hif : (if s = 0 then 0 else 2) ≤ 2 := by split_ifs <;> omega
                omega
              · rw [Hm.poly_snoc_add]
                dsimp only [terms]
                rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, List.map_map]
                have hrest : (prods.map ((fun t : K × Fin Hm.size =>
                    MvPolynomial.C t.1 * Hm.poly t.2) ∘ fun u => (1, u))).sum =
                    (prods.map fun u => Hm.poly u).sum := by
                  congr 1
                  refine List.map_congr_left fun u _ => ?_
                  dsimp only [Function.comp_apply]
                  rw [map_one, one_mul]
                rw [hrest, hsumm, hpm rS, hpam lS, hprS, hplS,
                  hev, homogeneousComponent_mul_pos (Nat.succ_pos s) (wEval (wires 0))
                    (wEval (wires 1))]
                simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]; ring
          rcases hstep with ⟨H2, idx2, hE12, hsz2, hdeg2, hpoly2⟩
          rcases hE12 with ⟨hV12, hle12, hd12, hp12⟩
          let row2 : Fin (s + 1) → Fin H2.size := fun r =>
            if hr : r.1 < s then ⟨(row1 ⟨r.1, hr⟩).1, lt_of_lt_of_le (row1 ⟨r.1, hr⟩).2 hle12⟩
            else idx2
          refine ⟨H2, row2, homExtends_trans hE1 ⟨hV12, hle12, hd12, hp12⟩, ?_, fun r => ?_⟩
          · rw [Nat.succ_mul]; omega
          · by_cases hr : r.1 < s
            · have hrr : row2 r =
                  ⟨(row1 ⟨r.1, hr⟩).1, lt_of_lt_of_le (row1 ⟨r.1, hr⟩).2 hle12⟩ := by
                dsimp only [row2]; split_ifs; rfl
              rw [hrr, hd12, hp12]; exact hspec1 ⟨r.1, hr⟩
            · have hrs : r.1 = s := by have := r.2; omega
              have hrr : row2 r = idx2 := by
                dsimp only [row2]; split_ifs; rfl
              rw [hrr, hrs]; exact ⟨hdeg2, hpoly2⟩
      rcases hrow d le_rfl with ⟨H1, row1, hE01, hsz1, hspec1⟩
      rcases hE01 with ⟨hV01, hle01, hd01, hp01⟩
      let hom1 : Fin (k + 1) → Fin d → Fin H1.size := fun g r =>
        if hg : g.1 < k then ⟨(hom0 ⟨g.1, hg⟩ r).1, lt_of_lt_of_le (hom0 ⟨g.1, hg⟩ r).2 hle01⟩
        else row1 r
      refine ⟨H1, hom1, hV01.trans hV0, ?_, fun g r => ?_⟩
      · calc H1.size ≤ H0.size + d * (d + 6) := hsz1
          _ ≤ k * d * (d + 6) + 1 + d * (d + 6) := Nat.add_le_add_right hsz0 _
          _ = (k + 1) * d * (d + 6) + 1 := by ring
      · by_cases hgk : g.1 < k
        · have hgg : hom1 g r =
              ⟨(hom0 ⟨g.1, hgk⟩ r).1, lt_of_lt_of_le (hom0 ⟨g.1, hgk⟩ r).2 hle01⟩ := by
            dsimp only [hom1]; split_ifs; rfl
          rw [hgg, hd01, hp01]; exact hspec0 ⟨g.1, hgk⟩ r
        · have hgeq : g.1 = k := by have := g.2; omega
          have hgg : hom1 g r = row1 r := by
            dsimp only [hom1]; split_ifs; rfl
          rw [hgg]
          have hidx_eq : (⟨g.1, lt_of_lt_of_le g.2 hk⟩ : Fin c.size) = kC := Fin.ext hgeq
          rw [hidx_eq]; exact hspec1 r
  rcases hbuild c.size le_rfl with ⟨H0, hom0, hV0, hsz0, hspec0⟩
  cases hout : c.outputs 0 with
  | gate j =>
    refine ⟨H0, fun r => hom0 j r, hV0, by nlinarith, fun r => ?_⟩
    rcases hspec0 j r with ⟨hdj, hpj⟩
    refine ⟨hdj, hpj.trans ?_⟩
    congr 1
    rw [Circuit.polynomial, Circuit.eval, Function.comp_apply, Program.trace, hout]; rfl
  | input v =>
    have hvV : v ∈ H0.activeVars := by
      rw [hV0]; exact Finset.mem_union_left _ (by simp [hout])
    -- Append one `.var v` gate (deg 1) and one `.zero` gate for each `r ≥ 1`.
    have hout_build : ∀ (s : ℕ) (hs : s ≤ d),
        ∃ (Hs : HomCircuit K m) (out : Fin s → Fin Hs.size),
          Hs.activeVars = V ∧ Hs.size ≤ H0.size + s ∧
          ∀ r : Fin s, Hs.deg (out r) = r.1 + 1 ∧
            Hs.poly (out r) = MvPolynomial.homogeneousComponent (r.1 + 1) (X v) := by
      intro s
      induction s with
      | zero => intro _; exact ⟨H0, fun r => r.elim0, hV0, by simp, fun r => r.elim0⟩
      | succ s ihs =>
        intro hs
        rcases ihs (Nat.le_of_succ_le hs) with ⟨H1, out1, hV1, hsz1, hspec1⟩
        by_cases hs0 : s = 0
        · let H2 := H1.snoc (s + 1) (Nat.succ_pos s) (.var v)
            (fun _ h => by injection h with hv'; exact ⟨by omega, hv' ▸ (hV1.symm ▸ (hV0 ▸ hvV))⟩)
            (fun _ h => by cases h) (fun _ _ h => by cases h)
          let out2 : Fin (s + 1) → Fin H2.size := fun r =>
            if hr : r.1 < s then (out1 ⟨r.1, hr⟩).castSucc else Fin.last H1.size
          refine ⟨H2, out2, hV1, by change H1.size + 1 ≤ _; omega, fun r => ?_⟩
          by_cases hr : r.1 < s
          · omega
          · have hrs : r.1 = s := by have := r.2; omega
            have hrr : out2 r = Fin.last H1.size := by
              dsimp only [out2]; exact dite_eq_right_of_eq_false (eq_false hr)
            rw [hrr, hrs]
            exact ⟨by simp [H2, HomCircuit.snoc], by
              rw [H1.poly_snoc_var, homogeneousComponent_X_eq, hs0]; simp⟩
        · let H2 := H1.snoc (s + 1) (Nat.succ_pos s) .zero
            (fun _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h)
          let out2 : Fin (s + 1) → Fin H2.size := fun r =>
            if hr : r.1 < s then (out1 ⟨r.1, hr⟩).castSucc else Fin.last H1.size
          refine ⟨H2, out2, hV1, by change H1.size + 1 ≤ _; omega, fun r => ?_⟩
          by_cases hr : r.1 < s
          · have hrr : out2 r = (out1 ⟨r.1, hr⟩).castSucc := by
              dsimp only [out2]; exact dite_eq_left_of_eq_true (eq_true hr)
            rw [hrr, show H2.deg (out1 ⟨r.1, hr⟩).castSucc = H1.deg (out1 ⟨r.1, hr⟩) from
              by simp [H2, HomCircuit.snoc], H1.poly_snoc_castSucc]
            exact hspec1 ⟨r.1, hr⟩
          · have hrs : r.1 = s := by have := r.2; omega
            have hrr : out2 r = Fin.last H1.size := by
              dsimp only [out2]; exact dite_eq_right_of_eq_false (eq_false hr)
            rw [hrr, hrs]
            exact ⟨by simp [H2, HomCircuit.snoc], by
              rw [H1.poly_snoc_zero, homogeneousComponent_X_eq]
              simp [hs0]⟩
    rcases hout_build d le_rfl with ⟨H1, out1, hV1, hsz1, hspec1⟩
    refine ⟨H1, out1, hV1, by
      calc H1.size ≤ H0.size + d := hsz1
        _ ≤ c.size * d * (d + 6) + 1 + d := Nat.add_le_add_right hsz0 d
        _ ≤ (c.size + 1) * d * (d + 6) + 2 := by nlinarith, fun r => ?_⟩
    rcases hspec1 r with ⟨hdr, hpr⟩
    refine ⟨hdr, hpr.trans ?_⟩
    congr 1
    rw [Circuit.polynomial, Circuit.eval, Function.comp_apply, Program.trace, hout]; rfl

private lemma list_finRange_map_sum {α : Type*} [AddCommMonoid α] (n : ℕ) (f : ℕ → α) :
    ((List.finRange n).map fun r : Fin n => f r.1).sum = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.finRange_succ_last, List.map_append, List.sum_append, List.map_map,
      List.map_singleton, List.sum_singleton, Finset.sum_range_succ, ← ih]
    rfl

/-- Active-variable frontier sum-of-products decomposition of any arithmetic circuit `c` of degree
at most `d` (`d ≥ 1`) at threshold `t ≥ 1`. -/
theorem circuit_to_sum_of_prods (c : Circuit (arithSignature K) m 1) (d t : ℕ)
    (hd : 1 ≤ d) (ht : 1 ≤ t) (hdeg : (c.polynomial 0).totalDegree ≤ d) :
    ∃ (V : Finset (Fin m)) (L : List (List (MvPolynomial (Fin m) K))),
      V.card ≤ min m (2 * c.size + 1) ∧
      MvPolynomial.C ((c.polynomial 0).coeff 0) + (L.map List.prod).sum = c.polynomial 0 ∧
      L.length ≤ d * ((c.size + 1) * d * (d + 6) + 2) ^ (2 * d / t) ∧
      (∀ ps ∈ L, ps.length ≤ 4 * d / t + 1) ∧
      (∀ ps ∈ L, ∀ q ∈ ps, q.totalDegree ≤ t ∧ ∀ μ ∈ q.support, ∀ v, μ v ≠ 0 → v ∈ V) := by
  rcases circuit_to_homCircuit c d hd with ⟨H, out, hHV, hHsz, hHout⟩
  have hcomp : ∀ r : Fin d, ∃ Lr : List (List (MvPolynomial (Fin m) K)),
      (Lr.map List.prod).sum = MvPolynomial.homogeneousComponent (r.1 + 1) (c.polynomial 0) ∧
      Lr.length ≤ ((c.size + 1) * d * (d + 6) + 2) ^ (2 * d / t) ∧
      (∀ ps ∈ Lr, ps.length ≤ 4 * d / t + 1) ∧
      (∀ ps ∈ Lr, ∀ q ∈ ps, q.totalDegree ≤ t ∧ HomCircuit.VarsIn H.activeVars q) := by
    intro r
    rcases H.frontier_sum_of_prods ht (r.1 + 1) (out r) (hHout r).1 with ⟨Lr, hsum, hlen, hk, hq⟩
    have hbase : max 1 H.size ≤ (c.size + 1) * d * (d + 6) + 2 :=
      max_le (by omega) hHsz
    have hq_le : r.1 / t ≤ d / t := Nat.div_le_div_right (le_of_lt r.2)
    have h2_le : 2 * (d / t) ≤ 2 * d / t :=
      (Nat.mul_div_cancel _ ht).symm.trans_le (Nat.div_le_div_right (by
        have := Nat.div_mul_le_self d t; nlinarith))
    have h4_le : 4 * (d / t) ≤ 4 * d / t :=
      (Nat.mul_div_cancel _ ht).symm.trans_le (Nat.div_le_div_right (by
        have := Nat.div_mul_le_self d t; nlinarith))
    have hexp : (if r.1 + 1 ≤ t then 0 else 2 * ((r.1 + 1 - 1) / t) - 1) ≤ 2 * d / t := by
      split_ifs <;> (try simp only [Nat.add_sub_cancel]) <;> omega
    have hkl : (if r.1 + 1 ≤ t then 1 else 4 * ((r.1 + 1 - 1) / t) - 1) ≤ 4 * d / t + 1 := by
      split_ifs <;> (try simp only [Nat.add_sub_cancel]) <;> omega
    refine ⟨Lr, hsum.trans (hHout r).2, ?_, fun ps hps => (hk ps hps).trans hkl, hq⟩
    calc Lr.length
        ≤ (max 1 H.size) ^ (if r.1 + 1 ≤ t then 0 else 2 * ((r.1 + 1 - 1) / t) - 1) := hlen
      _ ≤ (max 1 H.size) ^ (2 * d / t) := Nat.pow_le_pow_right (le_max_left 1 _) hexp
      _ ≤ ((c.size + 1) * d * (d + 6) + 2) ^ (2 * d / t) := Nat.pow_le_pow_left hbase _
  choose Lr hLr_sum hLr_len hLr_k hLr_q using hcomp
  let L : List (List (MvPolynomial (Fin m) K)) := (List.finRange d).flatMap Lr
  refine ⟨circuitActiveVars c, L, card_circuitActiveVars_le c, ?_, ?_, ?_, ?_⟩
  · have hflat_sum : (L.map List.prod).sum =
        ((List.finRange d).map fun r : Fin d => (Lr r |>.map List.prod).sum).sum := by
      dsimp only [L]
      have : ∀ (l : List (Fin d)), ((l.flatMap Lr).map List.prod).sum =
          (l.map fun r => (Lr r |>.map List.prod).sum).sum := by
        intro l; induction l with
        | nil => simp
        | cons r rs ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]
      exact this (List.finRange d)
    rw [hflat_sum]
    have hmap : ((List.finRange d).map fun r : Fin d => (Lr r |>.map List.prod).sum) =
        (List.finRange d).map fun r : Fin d =>
          MvPolynomial.homogeneousComponent (r.1 + 1) (c.polynomial 0) :=
      List.map_congr_left fun r _ => hLr_sum r
    rw [hmap, list_finRange_map_sum d (fun k => MvPolynomial.homogeneousComponent (k + 1)
      (c.polynomial 0))]
    exact sum_homogeneousComponent_pos_add_const (c.polynomial 0) hdeg
  · have hflat_len : ∀ (l : List (Fin d)),
        (l.flatMap Lr).length ≤ l.length * ((c.size + 1) * d * (d + 6) + 2) ^ (2 * d / t) := by
      intro l; induction l with
      | nil => simp
      | cons r rs ih =>
        rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
        exact (Nat.add_le_add (hLr_len r) ih).trans_eq (add_comm _ _)
    simpa [L] using hflat_len (List.finRange d)
  · intro ps hps
    rcases List.mem_flatMap.mp hps with ⟨r, _, hr⟩
    exact hLr_k r ps hr
  · intro ps hps q hq
    rcases List.mem_flatMap.mp hps with ⟨r, _, hr⟩
    rcases hLr_q r ps hr q hq with ⟨hdq, hvq⟩
    exact ⟨hdq, hHV ▸ hvq⟩

end ActiveHomogenization

end CslibFrontier.Computability.Circuit.Arithmetic
