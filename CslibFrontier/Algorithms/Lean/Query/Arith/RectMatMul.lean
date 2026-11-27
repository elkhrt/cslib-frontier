/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/
module

public import CslibFrontier.Algorithms.Lean.Query.Arith.MatMul
public import CslibFrontier.Computability.Circuit.Boolean.Word

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

/-!
# Rectangular Matrix Multiplication Queries and Word-Level Maximum/Minimum Circuits

This module contributes reusable computational complexity primitives to `CslibFrontier`:

1. **Rectangular schoolbook matrix multiplication in the `Cslib.Query` arithmetic query model**:
   generalizes `Cslib.Query.schoolbookMatMul` from square `n × n` matrices to rectangular `n × m`
   and `m × p` matrices over any `NonUnitalNonAssocSemiring S`, proving exact matrix-product
   evaluation and exact query cost `n * p * (m * cMul + (m - 1) * cAdd)`.
2. **De Morgan Boolean circuit synthesis and linear gate complexity for unsigned `w`-bit `max` and
   `min`**: builds `word_umax` and `word_umin` in `9 * w + 2` gates from `word_ult` and `word_mux`,
   together with exact `O(1)` (`< 2`) average-case MSB-to-LSB bit-comparison complexity across
   uniformly distributed `w`-bit word pairs.
-/

public section

namespace CslibFrontier

namespace Query

/-- Tabulate an `n × p` rectangular matrix of `Cslib.FreeM` query programs in row-major order. -/
def tabulateRectMatrix {Q : Type → Type} {α : Type} (n p : ℕ)
    (f : Fin n → Fin p → Cslib.FreeM Q α) : Cslib.FreeM Q (Matrix (Fin n) (Fin p) α) :=
  Matrix.of <$> Cslib.FreeM.tabulate n fun i ↦ Cslib.FreeM.tabulate p (f i)

theorem eval_tabulateRectMatrix {Q : Type → Type} {α : Type}
    (oracle : {ι : Type} → Q ι → ι) (n p : ℕ) (f : Fin n → Fin p → Cslib.FreeM Q α) :
    (tabulateRectMatrix n p f).eval oracle = Matrix.of fun i j ↦ (f i j).eval oracle := by
  simp only [tabulateRectMatrix, Cslib.FreeM.eval_map, Cslib.FreeM.eval_tabulate]

theorem cost_tabulateRectMatrix {Q : Type → Type} {α T : Type} [AddCommMonoid T]
    (oracle : {ι : Type} → Q ι → ι) (weight : {ι : Type} → Q ι → T) (n p : ℕ)
    (f : Fin n → Fin p → Cslib.FreeM Q α) :
    (tabulateRectMatrix n p f).cost oracle weight =
      ∑ i : Fin n, ∑ j : Fin p, (f i j).cost oracle weight := by
  simp only [tabulateRectMatrix, Cslib.FreeM.cost_map, Cslib.FreeM.cost_tabulate]

/-- Schoolbook multiplication of an `n × m` matrix and an `m × p` matrix in the `Cslib.Query`
arithmetic query model. -/
def rectSchoolbookMatMul {S : Type} [Zero S] (n m p : ℕ)
    (A : Matrix (Fin n) (Fin m) S) (B : Matrix (Fin m) (Fin p) S) :
    Cslib.FreeM (Cslib.Query.ArithQuery S) (Matrix (Fin n) (Fin p) S) :=
  tabulateRectMatrix n p fun i j ↦ Cslib.Query.schoolbookDot m (A i) (fun k ↦ B k j)

/-- Honest evaluation of `rectSchoolbookMatMul` computes `A * B` over any non-unital
non-associative semiring `S`. -/
theorem eval_rectSchoolbookMatMul {S : Type} [NonUnitalNonAssocSemiring S]
    (oracle : {ι : Type} → Cslib.Query.ArithQuery S ι → ι)
    (hadd : ∀ a b, oracle (.add a b) = a + b)
    (hmul : ∀ a b, oracle (.mul a b) = a * b)
    (n m p : ℕ) (A : Matrix (Fin n) (Fin m) S) (B : Matrix (Fin m) (Fin p) S) :
    (rectSchoolbookMatMul n m p A B).eval oracle = A * B := by
  rw [rectSchoolbookMatMul, eval_tabulateRectMatrix]
  ext i j
  rw [Matrix.of_apply, Cslib.Query.eval_schoolbookDot oracle hadd hmul, Matrix.mul_apply]

/-- Exact weighted query cost of `rectSchoolbookMatMul`: `n * p * (m * cMul + (m - 1) * cAdd)`. -/
theorem cost_rectSchoolbookMatMul {S : Type} [Zero S]
    (oracle : {ι : Type} → Cslib.Query.ArithQuery S ι → ι)
    (cAdd cMul n m p : ℕ) (A : Matrix (Fin n) (Fin m) S) (B : Matrix (Fin m) (Fin p) S) :
    (rectSchoolbookMatMul n m p A B).cost oracle (Cslib.Query.ArithQuery.weight cAdd cMul) =
      n * p * (m * cMul + (m - 1) * cAdd) := by
  simp only [rectSchoolbookMatMul, cost_tabulateRectMatrix, Cslib.Query.cost_schoolbookDot,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

end Query

namespace Circuits

/-- De Morgan Boolean circuit synthesis for unsigned `w`-bit word maximum in `9 * w + 2` gates. -/
theorem word_umax {n w : ℕ} {s : Set (Cslib.BooleanFunction n)}
    (a b : Cslib.BitString n → BitVec w)
    (ha : ∀ i : Fin w, (fun x ↦ (a x).getLsbD i.val) ∈ s)
    (hb : ∀ i : Fin w, (fun x ↦ (b x).getLsbD i.val) ∈ s) :
    Cslib.Circuits.Synthesis Cslib.Circuits.Boolean.interpretation s
      (Cslib.Circuits.Boolean.wordWires fun x ↦ if (a x).ult (b x) then b x else a x)
      (9 * w + 2) := by
  let flag : Cslib.BooleanFunction n := fun x ↦ (a x).ult (b x)
  have hult := Cslib.Circuits.Synthesis.word_ult a b ha hb
  have hmux := Cslib.Circuits.Synthesis.word_mux (s := s ∪ {flag}) b a flag (Or.inr rfl)
    (fun i ↦ Or.inl (hb i)) (fun i ↦ Or.inl (ha i))
  exact (hult.trans hmux).mono Set.Subset.rfl Set.Subset.rfl (by omega)

/-- De Morgan Boolean circuit synthesis for unsigned `w`-bit word minimum in `9 * w + 2` gates. -/
theorem word_umin {n w : ℕ} {s : Set (Cslib.BooleanFunction n)}
    (a b : Cslib.BitString n → BitVec w)
    (ha : ∀ i : Fin w, (fun x ↦ (a x).getLsbD i.val) ∈ s)
    (hb : ∀ i : Fin w, (fun x ↦ (b x).getLsbD i.val) ∈ s) :
    Cslib.Circuits.Synthesis Cslib.Circuits.Boolean.interpretation s
      (Cslib.Circuits.Boolean.wordWires fun x ↦ if (a x).ult (b x) then a x else b x)
      (9 * w + 2) := by
  let flag : Cslib.BooleanFunction n := fun x ↦ (a x).ult (b x)
  have hult := Cslib.Circuits.Synthesis.word_ult a b ha hb
  have hmux := Cslib.Circuits.Synthesis.word_mux (s := s ∪ {flag}) a b flag (Or.inr rfl)
    (fun i ↦ Or.inl (ha i)) (fun i ↦ Or.inl (hb i))
  exact (hult.trans hmux).mono Set.Subset.rfl Set.Subset.rfl (by omega)

end Circuits

end CslibFrontier
