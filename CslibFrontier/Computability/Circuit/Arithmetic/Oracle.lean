/-
Copyright (c) 2026 Google DeepMind. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Google DeepMind
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Computability.Circuit.Simulation
public import CslibFrontier.Computability.Circuit.Arithmetic.VNP
public import CslibFrontier.Computability.Circuit.MapOp
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure

/-!
# Oracle arithmetic circuits and Valiant's c-reductions

Extends `Cslib.Circuits.arithSignature` with a single `m`-ary oracle gate (`arithOracleSignature`)
evaluating a formal oracle polynomial `Q : MvPolynomial (Fin m) K` by substitution, and develops
Valiant's algebraic Turing reductions (`PolynomialFamily.IsCReducible`, written `f ≤_c g`) together
with `VNP`-completeness under `c`-reductions [Valiant1979Algebra; Burgisser2000].

## Main definitions

* `Cslib.Circuits.ArithOracleOp`, `Cslib.Circuits.arithOracleSignature`,
  `Cslib.Circuits.arithOracleInterpretationWith`: the arithmetic signature augmented with an `m`-ary
  oracle gate and its interpretations.
* `Cslib.Circuits.Circuit.oraclePolynomial`: the formal polynomial computed by an oracle arithmetic
  circuit relative to an oracle polynomial `Q`.
* `Cslib.Circuits.Arithmetic.HasOracleCircuit`: existence of an oracle arithmetic circuit of bounded
  gate count computing `P` from `Q`.
* `Cslib.Circuits.Arithmetic.PolynomialFamily.IsCReducible`: Valiant's polynomial-size oracle
  (`c`-)reduction between polynomial families.
* `Cslib.Circuits.Arithmetic.IsVNPHardUnderC`, `Cslib.Circuits.Arithmetic.IsVNPCompleteUnderC`:
  `VNP`-hardness and `VNP`-completeness under `c`-reductions.

## Main results

* `Cslib.Circuits.Circuit.aeval_oraclePolynomial`: algebra evaluation commutes with formal oracle
  polynomial evaluation.
* `Cslib.Circuits.Circuit.exists_oracleComposition`,
  `Cslib.Circuits.Circuit.exists_arith_of_oracle`: simulation of oracle gates by oracle or standard
  arithmetic circuits with multiplicative gate-count bound `(c₂.size + 1) * c₁.size`.
* `Cslib.Circuits.Arithmetic.PolynomialFamily.IsPProjection.isCReducible`: every `p`-projection to a
  family with polynomially bounded variable counts is a `c`-reduction.
* `Cslib.Circuits.Arithmetic.PolynomialFamily.IsCReducible.trans`: `c`-reductions are transitive.
* `Cslib.Circuits.Arithmetic.VP.of_isCReducible`: `VP` is closed under `c`-reductions among
  `p`-families.
* `Cslib.Circuits.Arithmetic.IsVNPComplete.isVNPCompleteUnderC`,
  `Cslib.Circuits.Arithmetic.IsVNPCompleteUnderC.mem_VP_iff`: `p`-projection completeness implies
  `c`-reduction completeness, and any `c`-complete family characterizes `VNP ⊆ VP`.
-/

public section

namespace Cslib.Circuits

open MvPolynomial

universe u

/-- Operations of an arithmetic circuit with an `m`-ary oracle gate over `K`. -/
inductive ArithOracleOp (K : Type u) : Type u
  /-- Standard arithmetic gate (`+`, `*`, or scalar constant). -/
  | arith (op : ArithOp K)
  /-- Multi-input oracle gate. -/
  | oracle

/-- Arity of an `ArithOracleOp K` when the oracle gate has arity `m`. -/
abbrev ArithOracleOp.arity (K : Type u) (m : ℕ) : ArithOracleOp K → ℕ
  | .arith op => ArithOp.arity K op
  | .oracle => m

/-- The *oracle arithmetic signature* over `K` with `m`-ary oracle gate. -/
abbrev arithOracleSignature (K : Type u) (m : ℕ) : Signature.{u} where
  Op := ArithOracleOp K
  Arity := ArithOracleOp.arity K m

/-- Interpret `arithOracleSignature K m` in `R` using `constant` for scalar constants and `ora` for
the `m`-ary oracle gate. -/
@[expose] def arithOracleInterpretationWith (K : Type u) (m : ℕ) {R : Type*} [Add R] [Mul R]
    (constant : K → R) (ora : (Fin m → R) → R) :
    Interpretation (arithOracleSignature K m) R
  | .arith op, x => arithInterpretationWith K constant op x
  | .oracle, x => ora x

@[simp] theorem arithOracleInterpretationWith_arith {K : Type u} (m : ℕ) {R : Type*} [Add R] [Mul R]
    (constant : K → R) (ora : (Fin m → R) → R) (op : ArithOp K) (x : Fin (ArithOp.arity K op) → R) :
    arithOracleInterpretationWith K m constant ora (.arith op) x =
      arithInterpretationWith K constant op x :=
  rfl

@[simp] theorem arithOracleInterpretationWith_oracle {K : Type u} (m : ℕ) {R : Type*} [Add R]
    [Mul R] (constant : K → R) (ora : (Fin m → R) → R) (x : Fin m → R) :
    arithOracleInterpretationWith K m constant ora .oracle x = ora x :=
  rfl

/-- Inclusion of the standard arithmetic signature into the `m`-ary oracle arithmetic signature. -/
@[expose] def ArithOp.toOracle (K : Type u) (m : ℕ) :
    (arithSignature K).Hom (arithOracleSignature K m) where
  toFun := ArithOracleOp.arith
  arity_eq _ := rfl

instance ArithOp.toOracle_preserves (K : Type u) (m : ℕ) {R : Type*} [Add R] [Mul R]
    (constant : K → R) (ora : (Fin m → R) → R) :
    (ArithOp.toOracle K m).Preserves (arithInterpretationWith K constant)
      (arithOracleInterpretationWith K m constant ora) :=
  ⟨fun _ _ => rfl⟩

section FormalPolynomial

variable {K : Type u} [CommSemiring K] {n m p q : ℕ}

/-- The formal polynomial computed at output `j` of an oracle arithmetic circuit relative to the
oracle polynomial `Q : MvPolynomial (Fin m) K`. -/
noncomputable def Circuit.oraclePolynomial (c : Circuit (arithOracleSignature K m) n p)
    (Q : MvPolynomial (Fin m) K) (j : Fin p) : MvPolynomial (Fin n) K :=
  c.eval (arithOracleInterpretationWith K m C (fun args => aeval args Q)) X j

/-- Evaluating the formal polynomial computed by an oracle circuit in a commutative `K`-algebra `R`
agrees with evaluating the circuit directly in `R`. -/
theorem Circuit.aeval_oraclePolynomial {R : Type*} [CommSemiring R] [Algebra K R]
    (c : Circuit (arithOracleSignature K m) n p) (Q : MvPolynomial (Fin m) K)
    (x : Fin n → R) (j : Fin p) :
    aeval x (c.oraclePolynomial Q j) =
      c.eval (arithOracleInterpretationWith K m (algebraMap K R)
        (fun args => aeval args Q)) x j := by
  let h : Homomorphism
      (arithOracleInterpretationWith K m (C : K →
        MvPolynomial (Fin n) K) (fun args => aeval args Q))
      (arithOracleInterpretationWith K m (algebraMap K R) (fun args => aeval args Q)) :=
    ⟨aeval x, fun op args => by
      cases op with
      | arith aop => cases aop <;> simp [arithInterpretationWith]
      | oracle =>
        simp only [arithOracleInterpretationWith_oracle]
        change ((aeval x).comp (aeval args)) Q = aeval (aeval x ∘ args) Q
        congr 1
        exact algHom_ext fun i => by simp⟩
  refine (congrFun (c.map_eval h X) j).trans ?_
  congr 1 with i : 1
  exact aeval_X x i

/-- Substituting polynomials for the variables of `c.oraclePolynomial Q j` evaluates `c` at those
polynomials. -/
theorem Circuit.aeval_oraclePolynomial_mvPolynomial {σ : Type*}
    (c : Circuit (arithOracleSignature K m) n p) (Q : MvPolynomial (Fin m) K)
    (x : Fin n → MvPolynomial σ K) (j : Fin p) :
    aeval x (c.oraclePolynomial Q j) =
      c.eval (arithOracleInterpretationWith K m C (fun args => aeval args Q)) x j := by
  rw [c.aeval_oraclePolynomial, algebraMap_eq]

/-- Lifting a standard arithmetic circuit to `arithOracleSignature K m` preserves its formal output
polynomials and gate count. -/
theorem Circuit.oraclePolynomial_mapOp_toOracle (c : Circuit (arithSignature K) n p)
    (Q : MvPolynomial (Fin m) K) (j : Fin p) :
    (c.mapOp (ArithOp.toOracle K m)).oraclePolynomial Q j = c.polynomial j := by
  unfold Circuit.oraclePolynomial Circuit.polynomial
  rw [Circuit.eval_mapOp (I := arithInterpretationWith K C)]

/-- **Oracle circuit composition**: if `c₁` computes polynomials using an `m`-ary oracle `Q`, and
`c₂` computes `Q` using a `q`-ary oracle `R`, then replacing every oracle gate of `c₁` by `c₂`
yields a `q`-ary oracle circuit of size at most `(c₂.size + 1) * c₁.size` computing the same formal
polynomials. -/
theorem Circuit.exists_oracleComposition (c₁ : Circuit (arithOracleSignature K m) n p)
    {Q : MvPolynomial (Fin m) K} {R : MvPolynomial (Fin q) K}
    (c₂ : Circuit (arithOracleSignature K q) m 1) (hc₂ : c₂.oraclePolynomial R 0 = Q) :
    ∃ d : Circuit (arithOracleSignature K q) n p,
      (∀ j, d.oraclePolynomial R j = c₁.oraclePolynomial Q j) ∧
        d.size ≤ (c₂.size + 1) * c₁.size := by
  let I := arithOracleInterpretationWith K m (C : K → MvPolynomial (Fin n) K)
    (fun args => aeval args Q)
  let J := arithOracleInterpretationWith K q (C : K → MvPolynomial (Fin n) K)
    (fun args => aeval args R)
  have hsim : J.SimulatesWithCost I (fun _ => c₂.size + 1) := by
    intro op
    cases op with
    | arith aop =>
      refine ⟨Circuit.oneGate (σ := arithOracleSignature K q) (.arith aop) id,
        fun args => ?_, by simp only [Circuit.size_oneGate]; omega⟩
      funext j
      fin_cases j
      rfl
    | oracle =>
      refine ⟨c₂, fun args => ?_, Nat.le_succ _⟩
      funext j
      fin_cases j
      change c₂.eval J args 0 = aeval args Q
      rw [← hc₂, c₂.aeval_oraclePolynomial_mvPolynomial]
  obtain ⟨d, hd_eval, hd_size⟩ := c₁.exists_simulation_le hsim
  exact ⟨d, fun j => congrFun (congrFun hd_eval X) j, hd_size⟩

/-- **Eliminating an oracle computed by an arithmetic circuit**: if `c₁` computes polynomials using
oracle `Q` and `c₂` is a standard arithmetic circuit computing `Q`, then `c₁` is simulated by a
standard arithmetic circuit of size at most `(c₂.size + 1) * c₁.size`. -/
theorem Circuit.exists_arith_of_oracle (c₁ : Circuit (arithOracleSignature K m) n p)
    {Q : MvPolynomial (Fin m) K} (c₂ : Circuit (arithSignature K) m 1)
    (hc₂ : c₂.polynomial 0 = Q) :
    ∃ d : Circuit (arithSignature K) n p,
      (∀ j, d.polynomial j = c₁.oraclePolynomial Q j) ∧
        d.size ≤ (c₂.size + 1) * c₁.size := by
  let I := arithOracleInterpretationWith K m (C : K → MvPolynomial (Fin n) K)
    (fun args => aeval args Q)
  let J := arithInterpretationWith K (C : K → MvPolynomial (Fin n) K)
  have hsim : J.SimulatesWithCost I (fun _ => c₂.size + 1) := by
    intro op
    cases op with
    | arith aop =>
      refine ⟨Circuit.oneGate (σ := arithSignature K) aop id,
        fun args => ?_, by simp only [Circuit.size_oneGate]; omega⟩
      funext j
      fin_cases j
      rfl
    | oracle =>
      refine ⟨c₂, fun args => ?_, Nat.le_succ _⟩
      funext j
      fin_cases j
      change c₂.eval J args 0 = aeval args Q
      rw [← hc₂, c₂.aeval_polynomial_mvPolynomial]
  obtain ⟨d, hd_eval, hd_size⟩ := c₁.exists_simulation_le hsim
  exact ⟨d, fun j => congrFun (congrFun hd_eval X) j, hd_size⟩

end FormalPolynomial

namespace Arithmetic

variable {K : Type u} [CommSemiring K] {n m p : ℕ}

/-- `HasOracleCircuit P Q s` means that `P` is computed as a formal polynomial by an oracle
arithmetic circuit with oracle `Q` and at most `s` gates. -/
def HasOracleCircuit (P : MvPolynomial (Fin n) K) (Q : MvPolynomial (Fin m) K) (s : ℕ) : Prop :=
  ∃ c : Circuit (arithOracleSignature K m) n 1, c.oraclePolynomial Q 0 = P ∧ c.size ≤ s

theorem HasOracleCircuit.mono {P : MvPolynomial (Fin n) K} {Q : MvPolynomial (Fin m) K} {s t : ℕ}
    (h : HasOracleCircuit P Q s) (hst : s ≤ t) : HasOracleCircuit P Q t :=
  let ⟨c, hc, hs⟩ := h
  ⟨c, hc, hs.trans hst⟩

/-- Every polynomial `Q` in `m` variables has a `1`-gate `Q`-oracle circuit. -/
theorem HasOracleCircuit.self (Q : MvPolynomial (Fin m) K) : HasOracleCircuit Q Q 1 :=
  ⟨Circuit.oneGate (σ := arithOracleSignature K m) .oracle id,
    by
      unfold Circuit.oraclePolynomial
      rw [Circuit.eval_oneGate]
      simp only [arithOracleInterpretationWith_oracle, id_eq]
      exact aeval_X_left_apply Q,
    by simp only [Circuit.size_oneGate, le_rfl]⟩

/-- A projection of `Q : MvPolynomial (Fin m) K` is computed by a `Q`-oracle circuit with at most
`m + 1` gates: `m` gates for the projection substitution and one oracle call. -/
theorem IsProjection.hasOracleCircuit {P : MvPolynomial (Fin n) K} {Q : MvPolynomial (Fin m) K}
    (h : IsProjection P Q) : HasOracleCircuit P Q (m + 1) := by
  obtain ⟨ρ, rfl⟩ := h
  let sub := (projectionCircuit ρ).mapOp (ArithOp.toOracle K m)
  let top := Circuit.oneGate (σ := arithOracleSignature K m) .oracle id
  refine ⟨top.comp sub, ?_, ?_⟩
  · unfold Circuit.oraclePolynomial
    rw [Circuit.eval_comp, Circuit.eval_oneGate]
    simp only [arithOracleInterpretationWith_oracle, id_eq, sub]
    rw [Circuit.eval_mapOp (I := arithInterpretationWith K C)]
    unfold projection
    congr 1
    apply algHom_ext
    intro i
    rw [aeval_X, aeval_X]
    exact eval_projectionCircuit C ρ X i
  · rw [Circuit.size_comp, Circuit.size_oneGate]
    exact Nat.add_le_add_right (size_projectionCircuit_le ρ) 1

/-- Transitivity of oracle circuit bounds via gate-by-gate oracle simulation. -/
theorem HasOracleCircuit.trans {P : MvPolynomial (Fin n) K} {Q : MvPolynomial (Fin m) K}
    {R : MvPolynomial (Fin p) K} {s₁ s₂ : ℕ}
    (hPQ : HasOracleCircuit P Q s₁) (hQR : HasOracleCircuit Q R s₂) :
    HasOracleCircuit P R ((s₂ + 1) * s₁) := by
  obtain ⟨c₁, hc₁, hs₁⟩ := hPQ
  obtain ⟨c₂, hc₂, hs₂⟩ := hQR
  obtain ⟨d, hd, hsize⟩ := c₁.exists_oracleComposition c₂ hc₂
  exact ⟨d, (hd 0).trans hc₁, hsize.trans (Nat.mul_le_mul (Nat.add_le_add_right hs₂ 1) hs₁)⟩

namespace PolynomialFamily

/-- `f` *c-reduces* to `g` (`f ≤_c g`) when there
are polynomially bounded `t` and `s` such that each `f.poly n` is computed by a
`g.poly (t n)`-oracle arithmetic circuit of size at most `s n`.
-/
def IsCReducible (f g : PolynomialFamily K) : Prop :=
  ∃ t s : ℕ → ℕ, PolynomiallyBounded t ∧ PolynomiallyBounded s ∧
    ∀ n, HasOracleCircuit (f.poly n) (g.poly (t n)) (s n)

/-- Every `p`-projection to a family with polynomially bounded variable count is a `c`-reduction. -/
theorem IsPProjection.isCReducible {f g : PolynomialFamily K} (hfg : f.IsPProjection g)
    (hvars : PolynomiallyBounded g.vars) : f.IsCReducible g := by
  obtain ⟨t, ht, hproj⟩ := hfg
  exact ⟨t, fun n => g.vars (t n) + 1, ht, (hvars.comp ht).add (PolynomiallyBounded.const 1),
    fun n => (hproj n).hasOracleCircuit⟩

/-- Every family with polynomially bounded variable count `c`-reduces to itself. -/
theorem IsCReducible.refl {f : PolynomialFamily K} (hvars : PolynomiallyBounded f.vars) :
    f.IsCReducible f :=
  (IsPProjection.refl f).isCReducible hvars

/-- **Transitivity of algebraic `c`-reductions**: composing
polynomial-size oracle circuits yields a polynomial-size oracle circuit.
-/
theorem IsCReducible.trans {f g h : PolynomialFamily K}
    (hfg : f.IsCReducible g) (hgh : g.IsCReducible h) : f.IsCReducible h := by
  obtain ⟨t₁, s₁, ht₁, hs₁, hc₁⟩ := hfg
  obtain ⟨t₂, s₂, ht₂, hs₂, hc₂⟩ := hgh
  exact ⟨fun n => t₂ (t₁ n), fun n => (s₂ (t₁ n) + 1) * s₁ n, ht₂.comp ht₁,
    ((hs₂.comp ht₁).add (PolynomiallyBounded.const 1)).mul hs₁,
    fun n => (hc₁ n).trans (hc₂ (t₁ n))⟩

end PolynomialFamily

/-- **`VP` is closed under `c`-reductions** among `p`-families
. An oracle circuit can square repeatedly and raise the degree
exponentially, so `f.IsPFamily` is part of the hypothesis.
-/
theorem VP.of_isCReducible {f g : PolynomialFamily K} (hg : g ∈ VP K)
    (hfg : f.IsCReducible g) (hf : f.IsPFamily) : f ∈ VP K := by
  obtain ⟨_, cg, hcg_size, hcg_poly⟩ := hg
  obtain ⟨t, s, ht, hs, horacle⟩ := hfg
  have hsim : ∀ n, ∃ d : Circuit (arithSignature K) (f.vars n) 1,
      d.polynomial 0 = f.poly n ∧ d.size ≤ ((cg (t n)).size + 1) * s n := by
    intro n
    obtain ⟨c₁, hc₁_poly, hc₁_size⟩ := horacle n
    obtain ⟨d, hd_poly, hd_size⟩ := c₁.exists_arith_of_oracle (cg (t n)) (hcg_poly (t n))
    exact ⟨d, (hd_poly 0).trans hc₁_poly,
      hd_size.trans (Nat.mul_le_mul_left _ hc₁_size)⟩
  choose d hd_poly hd_size using hsim
  exact ⟨hf, d, (((hcg_size.comp ht).add (PolynomiallyBounded.const 1)).mul hs).mono_of_le hd_size,
    hd_poly⟩

/-- A family `f` is *VNP-hard under c-reductions* when every family in `VNP K` `c`-reduces to `f`.
-/
def IsVNPHardUnderC (f : PolynomialFamily K) : Prop :=
  ∀ g ∈ VNP K, g.IsCReducible f

/-- A family `f` is *VNP-complete under c-reductions* when `f ∈ VNP K` and every family in `VNP K`
`c`-reduces to `f`. -/
def IsVNPCompleteUnderC (f : PolynomialFamily K) : Prop :=
  f ∈ VNP K ∧ IsVNPHardUnderC f

/-- `VNP`-hardness under `c`-reductions transfers along `c`-reductions. -/
theorem IsVNPHardUnderC.of_isCReducible {f g : PolynomialFamily K}
    (hf : IsVNPHardUnderC f) (hfg : f.IsCReducible g) : IsVNPHardUnderC g :=
  fun h hh => (hf h hh).trans hfg

/-- Every `VNP`-complete family under `p`-projections is `VNP`-complete under `c`-reductions. -/
theorem IsVNPComplete.isVNPCompleteUnderC {f : PolynomialFamily K} (hf : IsVNPComplete f) :
    IsVNPCompleteUnderC f :=
  ⟨hf.1, fun g hg => (hf.2 g hg).isCReducible (VNP.isPFamily hf.1).1⟩

/-- If a `c`-complete family for `VNP` belongs to `VP`, then `VNP ⊆ VP`. -/
theorem IsVNPCompleteUnderC.VNP_subset_VP {f : PolynomialFamily K}
    (hf : IsVNPCompleteUnderC f) (hVP : f ∈ VP K) : VNP K ⊆ VP K :=
  fun g hg => VP.of_isCReducible hVP (hf.2 g hg) (VNP.isPFamily hg)

/-- A `VNP`-complete family under `c`-reductions belongs to `VP` if and only if `VNP ⊆ VP`. -/
theorem IsVNPCompleteUnderC.mem_VP_iff {f : PolynomialFamily K} (hf : IsVNPCompleteUnderC f) :
    f ∈ VP K ↔ VNP K ⊆ VP K :=
  ⟨hf.VNP_subset_VP, fun h => h hf.1⟩

end Arithmetic

end Cslib.Circuits
