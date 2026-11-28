module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Permanent.HomCircuit
import Mathlib.Algebra.BigOperators.Fin

/-!
# Interval-Tree Clause-Sum Encoding for Arithmetic Parse Trees

Defines a finite-domain interval-tree clause-sum encoding (`TreeDom`, `TreeVal`, `TreeCheck`,
`TreeWeight`, `treeLits`, `treeWeights`) for bounded-degree binary parse trees of arithmetic
circuits, proves that checking clauses characterize semantic validity (`check_prod_eq_ite`), and
proves that weighting clauses reproduce parse-tree evaluations (`weight_prod_eq_assignWeight`).
-/

public section

namespace CslibFrontier.Computability.Circuit.Arithmetic.Permanent

open Cslib Cslib.Circuits Cslib.Circuits.Arithmetic MvPolynomial Finset

universe u

/-! ### Domain and value types for the interval-tree clause sum -/

/-- Parent-pointer values for intervals in a degree-`≤ d` binary parse tree. -/
public inductive ParKind (d : ℕ) where
  /-- Inactive interval. -/
  | none
  /-- Root interval `[0, rootDeg - 1]`. -/
  | root
  /-- Left child of interval `[l, r']`. -/
  | leftOf (r' : Fin d)
  /-- Right child of interval `[l', r]`. -/
  | rightOf (l' : Fin d)
  deriving DecidableEq

/-- Equivalence classifying `ParKind d`. -/
public def parKindEquiv (d : ℕ) : ParKind d ≃ Unit ⊕ Unit ⊕ Fin d ⊕ Fin d where
  toFun
    | .none => .inl ()
    | .root => .inr (.inl ())
    | .leftOf r' => .inr (.inr (.inl r'))
    | .rightOf l' => .inr (.inr (.inr l'))
  invFun
    | .inl () => .none
    | .inr (.inl ()) => .root
    | .inr (.inr (.inl r')) => .leftOf r'
    | .inr (.inr (.inr l')) => .rightOf l'
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with ⟨⟩ | ⟨⟩ | _ | _ <;> rfl

/-- `Fintype` instance for `ParKind d`. -/
public instance instFintypeParKind (d : ℕ) : Fintype (ParKind d) :=
  Fintype.ofEquiv _ (parKindEquiv d).symm

/-- `Nonempty` instance for `ParKind d`. -/
public instance instNonemptyParKind (d : ℕ) : Nonempty (ParKind d) := ⟨.none⟩

/-- Finite domain of the interval-tree clause sum. -/
public inductive TreeDom (m d : ℕ) where
  /-- Boolean summation variable `e_b`. -/
  | boolVar (b : Fin m)
  /-- Chosen homogeneous degree `k ∈ {0, ..., d}`. -/
  | rootDeg
  /-- Parent pointer of interval `(l, r)`. -/
  | par (l r : Fin d)
  /-- Assigned circuit wire of interval `(l, r)`. -/
  | wire (l r : Fin d)
  /-- Split index of internal interval `(l, r)`. -/
  | split (l r : Fin d)
  /-- Multiplication gate of internal interval `(l, r)`. -/
  | gate (l r : Fin d)
  /-- Leaf variable index at leaf `(l, l)`. -/
  | leafVar (l : Fin d)
  deriving DecidableEq

/-- Equivalence classifying `TreeDom m d`. -/
public def treeDomEquiv (m d : ℕ) :
    TreeDom m d ≃
      Fin m ⊕ Unit ⊕ (Fin d × Fin d) ⊕ (Fin d × Fin d) ⊕ (Fin d × Fin d) ⊕
        (Fin d × Fin d) ⊕ Fin d where
  toFun
    | .boolVar b => .inl b
    | .rootDeg => .inr (.inl ())
    | .par l r => .inr (.inr (.inl (l, r)))
    | .wire l r => .inr (.inr (.inr (.inl (l, r))))
    | .split l r => .inr (.inr (.inr (.inr (.inl (l, r)))))
    | .gate l r => .inr (.inr (.inr (.inr (.inr (.inl (l, r))))))
    | .leafVar l => .inr (.inr (.inr (.inr (.inr (.inr l)))))
  invFun
    | .inl b => .boolVar b
    | .inr (.inl ()) => .rootDeg
    | .inr (.inr (.inl (l, r))) => .par l r
    | .inr (.inr (.inr (.inl (l, r)))) => .wire l r
    | .inr (.inr (.inr (.inr (.inl (l, r))))) => .split l r
    | .inr (.inr (.inr (.inr (.inr (.inl (l, r)))))) => .gate l r
    | .inr (.inr (.inr (.inr (.inr (.inr l))))) => .leafVar l
  left_inv x := by cases x <;> rfl
  right_inv x := by
    rcases x with _ | ⟨⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | _ <;> rfl

/-- `Fintype` instance for `TreeDom m d`. -/
public instance instFintypeTreeDom (m d : ℕ) : Fintype (TreeDom m d) :=
  Fintype.ofEquiv _ (treeDomEquiv m d).symm

/-- Reducible value fiber over each point of `TreeDom m d`. -/
public abbrev TreeVal (N s d : ℕ) {m : ℕ} : TreeDom m d → Type
  | .boolVar _ => Bool
  | .rootDeg => Fin (d + 1)
  | .par _ _ => ParKind d
  | .wire _ _ => Option (Wire N s)
  | .split _ _ => Option (Fin d)
  | .gate _ _ => Option (Fin s)
  | .leafVar _ => Option (Fin N)

/-- `DecidableEq` instance for `TreeVal N s d x`. -/
public instance instDecidableEqTreeVal (N s d m : ℕ) (x : TreeDom m d) :
    DecidableEq (TreeVal N s d x) := by
  cases x <;> dsimp [TreeVal] <;> infer_instance

/-- `Fintype` instance for `TreeVal N s d x`. -/
public instance instFintypeTreeVal (N s d m : ℕ) (x : TreeDom m d) :
    Fintype (TreeVal N s d x) := by
  cases x <;> dsimp [TreeVal] <;> infer_instance

/-- `Nonempty` instance for `TreeVal N s d x`. -/
public instance instNonemptyTreeVal (N s d m : ℕ) (x : TreeDom m d) :
    Nonempty (TreeVal N s d x) := by
  cases x with
  | boolVar _ => exact ⟨false⟩
  | rootDeg => exact ⟨0⟩
  | par _ _ => exact ⟨.none⟩
  | wire _ _ => exact ⟨none⟩
  | split _ _ => exact ⟨none⟩
  | gate _ _ => exact ⟨none⟩
  | leafVar _ => exact ⟨none⟩

/-- Explicit upper bound on the number of one-hot bits in the interval-tree domain. -/
public theorem card_sigma_treeVal (N s d m : ℕ) :
    Fintype.card (Σ x : TreeDom m d, TreeVal N s d x) ≤
      2 * m + (d + 1) + d * d * (5 + 3 * d + N + 2 * s) + d * (1 + N) := by
  have hpar : Fintype.card (ParKind d) = 2 + 2 * d := by
    rw [Fintype.card_congr (parKindEquiv d)]
    simp only [Fintype.card_sum, Fintype.card_unique, Fintype.card_fin]
    omega
  have hcard : ∀ x : TreeDom m d, Fintype.card (TreeVal N s d x) =
      match x with
      | .boolVar _ => 2
      | .rootDeg => d + 1
      | .par _ _ => 2 + 2 * d
      | .wire _ _ => N + s + 1
      | .split _ _ => d + 1
      | .gate _ _ => s + 1
      | .leafVar _ => N + 1 := by
    intro x
    cases x <;> dsimp only [TreeVal]
    · exact (Fintype.card_congr (Equiv.refl Bool)).trans Fintype.card_bool
    · exact (Fintype.card_congr (Equiv.refl (Fin (d + 1)))).trans (Fintype.card_fin (d + 1))
    · exact (Fintype.card_congr (Equiv.refl (ParKind d))).trans hpar
    · exact (Fintype.card_congr (Equiv.refl _)).trans (by simp [Fintype.card_option, Wire.card])
    · exact (Fintype.card_congr (Equiv.refl _)).trans
        (by simp [Fintype.card_option, Fintype.card_fin])
    · exact (Fintype.card_congr (Equiv.refl _)).trans
        (by simp [Fintype.card_option, Fintype.card_fin])
    · exact (Fintype.card_congr (Equiv.refl _)).trans
        (by simp [Fintype.card_option, Fintype.card_fin])
  rw [Fintype.card_sigma]
  simp_rw [hcard]
  rw [← (treeDomEquiv m d).symm.sum_comp]
  simp only [Fintype.sum_sum_type, treeDomEquiv, Equiv.coe_fn_symm_mk, Finset.sum_const,
    Finset.card_univ, Fintype.card_unique, Fintype.card_prod, Fintype.card_fin, smul_eq_mul]
  have : d * d * (2 + 2 * d) + (d * d * (N + s + 1) +
      (d * d * (d + 1) + (d * d * (s + 1) + d * (N + 1)))) =
      d * d * (5 + 3 * d + N + 2 * s) + d * (1 + N) := by ring
  linarith

/-! ### Clauses for the interval-tree domain clause sum -/

section TreeClauses

variable {K : Type u} [CommSemiring K] {n m s d : ℕ}

/-- Checking clauses (all weight `0`) enforcing interval-tree validity. -/
public inductive TreeCheck (n m s d : ℕ) where
  /-- `rootDeg = r + 1 → par (0, r) = .root`. -/
  | rootDegToPar (r : Fin d)
  /-- `par (l, r) = .root → l = 0 ∧ rootDeg = r + 1`. -/
  | parRootToDeg (l r : Fin d)
  /-- `par (l, r) = .root → wire (l, r) = some v_out`. -/
  | parRootToWire (l r : Fin d)
  /-- `par = .none → wire = none`. -/
  | parNoneToWire (l r : Fin d)
  /-- `wire = none → par = .none`. -/
  | wireNoneToPar (l r : Fin d)
  /-- `par = .none → split = none` (and always `none` for `¬ l < r`). -/
  | parNoneToSplit (l r : Fin d)
  /-- `split = none → par = .none` for `l < r`. -/
  | splitNoneToPar (l r : Fin d)
  /-- `par = .none → gate = none` (and always `none` for `¬ l < r`). -/
  | parNoneToGate (l r : Fin d)
  /-- `gate = none → par = .none` for `l < r`. -/
  | gateNoneToPar (l r : Fin d)
  /-- `par (l, l) = .none → leafVar l = none`. -/
  | parNoneToLeaf (l : Fin d)
  /-- `leafVar l = none → par (l, l) = .none`. -/
  | leafNoneToPar (l : Fin d)
  /-- `r < l → par (l, r) = .none`. -/
  | badOrder (l r : Fin d)
  /-- `par (l, r) = .leftOf r' → r < r'`. -/
  | badLeftPar (l r r' : Fin d)
  /-- `par (l, r) = .rightOf l' → l' < l`. -/
  | badRightPar (l r l' : Fin d)
  /-- `split (l, r) = some q → l ≤ q < r`. -/
  | badSplit (l r q : Fin d)
  /-- `split (l, r) = some q → par (l, q) = .leftOf r`. -/
  | splitToLeftPar (l r q : Fin d)
  /-- `par (l, q) = .leftOf r → split (l, r) = some q`. -/
  | leftParToSplit (l r q : Fin d)
  /-- `split (l, r) = some q → par (q + 1, r) = .rightOf l`. -/
  | splitToRightPar (l r q : Fin d)
  /-- `par (q + 1, r) = .rightOf l → split (l, r) = some q`. -/
  | rightParToSplit (l r q : Fin d)
  /-- `gate (l, r) = some g → isMulGate p g`. -/
  | badGate (l r : Fin d) (g : Fin s)
  /-- Left child wire propagation from `gate` and `split`. -/
  | gateLeftWire (l r q : Fin d) (g : Fin s)
  /-- Right child wire propagation from `gate` and `split`. -/
  | gateRightWire (l r q : Fin d) (g : Fin s)
  /-- Boolean variable consistency at leaves. -/
  | leafBool (l : Fin d) (b : Fin m)

/-- Weighting clauses contributing `C (wireConst)`, `C (linCoeff)`, or `X i`. -/
public inductive TreeWeight (n m s d : ℕ) where
  /-- Degree-0 constant contribution. -/
  | degZero
  /-- Internal multiplication-node coefficient. -/
  | internalCoeff (l r : Fin d) (w : Wire (n + m) s) (g : Fin s)
  /-- Leaf variable linear coefficient. -/
  | leafCoeff (l : Fin d) (w : Wire (n + m) s) (j : Fin (n + m))
  /-- Leaf indeterminate `X i`. -/
  | leafInput (l : Fin d) (i : Fin n)

/-- Equivalence classifying `TreeCheck n m s d`. -/
public def treeCheckEquiv (n m s d : ℕ) :
    TreeCheck n m s d ≃
      Fin d ⊕ (Fin d × Fin d) ⊕ (Fin d × Fin d) ⊕ (Fin d × Fin d) ⊕ (Fin d × Fin d) ⊕
      (Fin d × Fin d) ⊕ (Fin d × Fin d) ⊕ (Fin d × Fin d) ⊕ (Fin d × Fin d) ⊕
      Fin d ⊕ Fin d ⊕ (Fin d × Fin d) ⊕ (Fin d × Fin d × Fin d) ⊕
      (Fin d × Fin d × Fin d) ⊕ (Fin d × Fin d × Fin d) ⊕ (Fin d × Fin d × Fin d) ⊕
      (Fin d × Fin d × Fin d) ⊕ (Fin d × Fin d × Fin d) ⊕ (Fin d × Fin d × Fin d) ⊕
      (Fin d × Fin d × Fin s) ⊕ (Fin d × Fin d × Fin d × Fin s) ⊕
      (Fin d × Fin d × Fin d × Fin s) ⊕ (Fin d × Fin m) where
  toFun
    | .rootDegToPar r => .inl r
    | .parRootToDeg l r => .inr (.inl (l, r))
    | .parRootToWire l r => .inr (.inr (.inl (l, r)))
    | .parNoneToWire l r => .inr (.inr (.inr (.inl (l, r))))
    | .wireNoneToPar l r => .inr (.inr (.inr (.inr (.inl (l, r)))))
    | .parNoneToSplit l r => .inr (.inr (.inr (.inr (.inr (.inl (l, r))))))
    | .splitNoneToPar l r => .inr (.inr (.inr (.inr (.inr (.inr (.inl (l, r)))))))
    | .parNoneToGate l r => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (l, r))))))))
    | .gateNoneToPar l r => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (l, r)))))))))
    | .parNoneToLeaf l => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl l)))))))))
    | .leafNoneToPar l =>
        .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl l))))))))))
    | .badOrder l r =>
        .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (l, r))))))))))))
    | .badLeftPar l r r' =>
        .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
          (.inl (l, r, r')))))))))))))
    | .badRightPar l r l' =>
        .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
          (.inr (.inl (l, r, l'))))))))))))))
    | .badSplit l r q =>
        .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
          (.inr (.inr (.inl (l, r, q)))))))))))))))
    | .splitToLeftPar l r q =>
        .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
          (.inr (.inr (.inr (.inl (l, r, q))))))))))))))))
    | .leftParToSplit l r q =>
        .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
          (.inr (.inr (.inr (.inr (.inl (l, r, q)))))))))))))))))
    | .splitToRightPar l r q =>
        .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
          (.inr (.inr (.inr (.inr (.inr (.inl (l, r, q))))))))))))))))))
    | .rightParToSplit l r q =>
        .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
          (.inr (.inr (.inr (.inr (.inr (.inr (.inl (l, r, q)))))))))))))))))))
    | .badGate l r g =>
        .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
          (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (l, r, g))))))))))))))))))))
    | .gateLeftWire l r q g =>
        .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
          (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (l, r, q, g)))))))))))))))))))))
    | .gateRightWire l r q g =>
        .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
          (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
            (.inl (l, r, q, g))))))))))))))))))))))
    | .leafBool l b =>
        .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
          (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
            (.inr (l, b))))))))))))))))))))))
  invFun
    | .inl r => .rootDegToPar r
    | .inr (.inl (l, r)) => .parRootToDeg l r
    | .inr (.inr (.inl (l, r))) => .parRootToWire l r
    | .inr (.inr (.inr (.inl (l, r)))) => .parNoneToWire l r
    | .inr (.inr (.inr (.inr (.inl (l, r))))) => .wireNoneToPar l r
    | .inr (.inr (.inr (.inr (.inr (.inl (l, r)))))) => .parNoneToSplit l r
    | .inr (.inr (.inr (.inr (.inr (.inr (.inl (l, r))))))) => .splitNoneToPar l r
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (l, r)))))))) => .parNoneToGate l r
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (l, r))))))))) => .gateNoneToPar l r
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl l))))))))) => .parNoneToLeaf l
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl l)))))))))) =>
        .leafNoneToPar l
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (l, r)))))))))))) =>
        .badOrder l r
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
        (.inl (l, r, r'))))))))))))) => .badLeftPar l r r'
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
        (.inr (.inl (l, r, l')))))))))))))) => .badRightPar l r l'
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
        (.inr (.inr (.inl (l, r, q))))))))))))))) => .badSplit l r q
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
        (.inr (.inr (.inr (.inl (l, r, q)))))))))))))))) => .splitToLeftPar l r q
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
        (.inr (.inr (.inr (.inr (.inl (l, r, q))))))))))))))))) => .leftParToSplit l r q
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
        (.inr (.inr (.inr (.inr (.inr (.inl (l, r, q)))))))))))))))))) => .splitToRightPar l r q
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
        (.inr (.inr (.inr (.inr (.inr (.inr (.inl (l, r, q))))))))))))))))))) =>
        .rightParToSplit l r q
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
        (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (l, r, g)))))))))))))))))))) =>
        .badGate l r g
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
        (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (l, r, q, g))))))))))))))))))))) =>
        .gateLeftWire l r q g
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
        (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
          (.inl (l, r, q, g)))))))))))))))))))))) => .gateRightWire l r q g
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
        (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
          (.inr (l, b)))))))))))))))))))))) => .leafBool l b
  left_inv x := by cases x <;> rfl
  right_inv x := by
    rcases x with _ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ |
      _ | _ | ⟨_, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ |
      ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;> rfl

/-- `Fintype` instance for `TreeCheck n m s d`. -/
public instance instFintypeTreeCheck (n m s d : ℕ) : Fintype (TreeCheck n m s d) :=
  Fintype.ofEquiv _ (treeCheckEquiv n m s d).symm

/-- Exact cardinality of `TreeCheck n m s d`. -/
public theorem card_treeCheck (n m s d : ℕ) :
    Fintype.card (TreeCheck n m s d) =
      3 * d + 9 * d * d + 7 * d * d * d + d * d * s + 2 * d * d * d * s + d * m := by
  rw [Fintype.card_congr (treeCheckEquiv n m s d)]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  ring

/-- Equivalence classifying `TreeWeight n m s d`. -/
public def treeWeightEquiv (n m s d : ℕ) :
    TreeWeight n m s d ≃
      Unit ⊕ (Fin d × Fin d × Wire (n + m) s × Fin s) ⊕
        (Fin d × Wire (n + m) s × Fin (n + m)) ⊕ (Fin d × Fin n) where
  toFun
    | .degZero => .inl ()
    | .internalCoeff l r w g => .inr (.inl (l, r, w, g))
    | .leafCoeff l w j => .inr (.inr (.inl (l, w, j)))
    | .leafInput l i => .inr (.inr (.inr (l, i)))
  invFun
    | .inl () => .degZero
    | .inr (.inl (l, r, w, g)) => .internalCoeff l r w g
    | .inr (.inr (.inl (l, w, j))) => .leafCoeff l w j
    | .inr (.inr (.inr (l, i))) => .leafInput l i
  left_inv x := by cases x <;> rfl
  right_inv x := by
    rcases x with ⟨⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _⟩ <;> rfl

/-- `Fintype` instance for `TreeWeight n m s d`. -/
public instance instFintypeTreeWeight (n m s d : ℕ) : Fintype (TreeWeight n m s d) :=
  Fintype.ofEquiv _ (treeWeightEquiv n m s d).symm

/-- Exact cardinality of `TreeWeight n m s d`. -/
public theorem card_treeWeight (n m s d : ℕ) :
    Fintype.card (TreeWeight n m s d) =
      1 + d * d * ((n + m) + s) * s + d * ((n + m) + s) * (n + m) + d * n := by
  rw [Fintype.card_congr (treeWeightEquiv n m s d)]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_unique, Fintype.card_fin, Wire.card]
  ring

/-- A literal in the interval-tree domain clause sum (`ι = Empty`). -/
public abbrev TreeLit (n m s d : ℕ) :=
  (Empty ⊕ Σ x : TreeDom m d, TreeVal (n + m) s d x) × Bool

/-- Construct a domain literal `(x = v)` (if `b = true`) or `(x ≠ v)` (if `b = false`). -/
public abbrev mkLit {n m s d : ℕ} (x : TreeDom m d) (v : TreeVal (n + m) s d x) (b : Bool) :
    TreeLit n m s d :=
  (.inr ⟨x, v⟩, b)

/-- Literals of each checking clause (every list has length 1, 2, or 3). -/
@[expose] public def checkLits (p : Program (arithSignature K) (n + m) s) (v_out : Wire (n + m) s) :
    TreeCheck n m s d → List (TreeLit n m s d)
  | .rootDegToPar r =>
      [mkLit .rootDeg (⟨r.1 + 1, by omega⟩ : Fin (d + 1)) true,
        mkLit (.par ⟨0, Nat.zero_lt_of_lt r.isLt⟩ r) .root false]
  | .parRootToDeg l r =>
      if l.1 = 0 then
        [mkLit (.par l r) .root true,
          mkLit .rootDeg (⟨r.1 + 1, by omega⟩ : Fin (d + 1)) false]
      else
        [mkLit (.par l r) .root true]
  | .parRootToWire l r =>
      [mkLit (.par l r) .root true, mkLit (.wire l r) (some v_out) false]
  | .parNoneToWire l r =>
      [mkLit (.par l r) .none true, mkLit (.wire l r) none false]
  | .wireNoneToPar l r =>
      [mkLit (.par l r) .none false, mkLit (.wire l r) none true]
  | .parNoneToSplit l r =>
      if l.1 < r.1 then [mkLit (.par l r) .none true, mkLit (.split l r) none false]
      else [mkLit (.split l r) none false]
  | .splitNoneToPar l r =>
      if l.1 < r.1 then [mkLit (.par l r) .none false, mkLit (.split l r) none true]
      else [mkLit (.split l r) none false]
  | .parNoneToGate l r =>
      if l.1 < r.1 then [mkLit (.par l r) .none true, mkLit (.gate l r) none false]
      else [mkLit (.gate l r) none false]
  | .gateNoneToPar l r =>
      if l.1 < r.1 then [mkLit (.par l r) .none false, mkLit (.gate l r) none true]
      else [mkLit (.gate l r) none false]
  | .parNoneToLeaf l =>
      [mkLit (.par l l) .none true, mkLit (.leafVar l) none false]
  | .leafNoneToPar l =>
      [mkLit (.par l l) .none false, mkLit (.leafVar l) none true]
  | .badOrder l r =>
      if r.1 < l.1 then [mkLit (.par l r) .none false]
      else [mkLit .rootDeg (0 : Fin (d + 1)) true, mkLit .rootDeg (0 : Fin (d + 1)) false]
  | .badLeftPar l r r' =>
      if ¬ (r.1 < r'.1) then [mkLit (.par l r) (.leftOf r') true]
      else [mkLit .rootDeg (0 : Fin (d + 1)) true, mkLit .rootDeg (0 : Fin (d + 1)) false]
  | .badRightPar l r l' =>
      if ¬ (l'.1 < l.1) then [mkLit (.par l r) (.rightOf l') true]
      else [mkLit .rootDeg (0 : Fin (d + 1)) true, mkLit .rootDeg (0 : Fin (d + 1)) false]
  | .badSplit l r q =>
      if ¬ (l.1 ≤ q.1 ∧ q.1 < r.1) then [mkLit (.split l r) (some q) true]
      else [mkLit .rootDeg (0 : Fin (d + 1)) true, mkLit .rootDeg (0 : Fin (d + 1)) false]
  | .splitToLeftPar l r q =>
      if l.1 ≤ q.1 ∧ q.1 < r.1 then
        [mkLit (.split l r) (some q) true, mkLit (.par l q) (.leftOf r) false]
      else [mkLit .rootDeg (0 : Fin (d + 1)) true, mkLit .rootDeg (0 : Fin (d + 1)) false]
  | .leftParToSplit l r q =>
      if l.1 ≤ q.1 ∧ q.1 < r.1 then
        [mkLit (.par l q) (.leftOf r) true, mkLit (.split l r) (some q) false]
      else [mkLit .rootDeg (0 : Fin (d + 1)) true, mkLit .rootDeg (0 : Fin (d + 1)) false]
  | .splitToRightPar l r q =>
      if h : l.1 ≤ q.1 ∧ q.1 < r.1 then
        [mkLit (.split l r) (some q) true,
          mkLit (.par ⟨q.1 + 1, by have := r.isLt; omega⟩ r) (.rightOf l) false]
      else [mkLit .rootDeg (0 : Fin (d + 1)) true, mkLit .rootDeg (0 : Fin (d + 1)) false]
  | .rightParToSplit l r q =>
      if h : l.1 ≤ q.1 ∧ q.1 < r.1 then
        [mkLit (.par ⟨q.1 + 1, by have := r.isLt; omega⟩ r) (.rightOf l) true,
          mkLit (.split l r) (some q) false]
      else [mkLit .rootDeg (0 : Fin (d + 1)) true, mkLit .rootDeg (0 : Fin (d + 1)) false]
  | .badGate l r g =>
      if isMulGate p g = false then [mkLit (.gate l r) (some g) true]
      else [mkLit .rootDeg (0 : Fin (d + 1)) true, mkLit .rootDeg (0 : Fin (d + 1)) false]
  | .gateLeftWire l r q g =>
      if h : l.1 ≤ q.1 ∧ q.1 < r.1 then
        match mulLeftWire p g with
        | some u =>
            [mkLit (.split l r) (some q) true, mkLit (.gate l r) (some g) true,
              mkLit (.wire l q) (some u) false]
        | none => [mkLit (.gate l r) (some g) true]
      else [mkLit .rootDeg (0 : Fin (d + 1)) true, mkLit .rootDeg (0 : Fin (d + 1)) false]
  | .gateRightWire l r q g =>
      if h : l.1 ≤ q.1 ∧ q.1 < r.1 then
        match mulRightWire p g with
        | some v =>
            [mkLit (.split l r) (some q) true, mkLit (.gate l r) (some g) true,
              mkLit (.wire ⟨q.1 + 1, by have := r.isLt; omega⟩ r) (some v) false]
        | none => [mkLit (.gate l r) (some g) true]
      else [mkLit .rootDeg (0 : Fin (d + 1)) true, mkLit .rootDeg (0 : Fin (d + 1)) false]
  | .leafBool l b =>
      [mkLit (.leafVar l) (some (Fin.natAdd n b)) true, mkLit (.boolVar b) false true]

/-- Literals of each weighting clause (every list has length 1 or 2). -/
@[expose] public def weightLits : TreeWeight n m s d → List (TreeLit n m s d)
  | .degZero => [mkLit .rootDeg (0 : Fin (d + 1)) true]
  | .internalCoeff l r w g =>
      [mkLit (.wire l r) (some w) true, mkLit (.gate l r) (some g) true]
  | .leafCoeff l w j =>
      [mkLit (.wire l l) (some w) true, mkLit (.leafVar l) (some j) true]
  | .leafInput l i =>
      [mkLit (.leafVar l) (some (Fin.castAdd m i)) true]

/-- Weights of weighting clauses (each is `C a` or `X i`). -/
@[expose] public noncomputable def weightVals (p : Program (arithSignature K) (n + m) s)
    (v_out : Wire (n + m) s) : TreeWeight n m s d → MvPolynomial (Fin n) K
  | .degZero => C (wireConst p v_out)
  | .internalCoeff _ _ w g => C (linCoeff p w (.gate g))
  | .leafCoeff _ w j => C (linCoeff p w (.input j))
  | .leafInput _ i => X i

/-- Combined literals for the interval-tree domain clause sum. -/
@[expose] public def treeLits (p : Program (arithSignature K) (n + m) s) (v_out : Wire (n + m) s) :
    TreeCheck n m s d ⊕ TreeWeight n m s d → List (TreeLit n m s d) :=
  Sum.elim (checkLits p v_out) weightLits

omit [CommSemiring K] in
/-- `treeLits` on a checking clause. -/
@[simp] public theorem treeLits_inl (p : Program (arithSignature K) (n + m) s)
    (v_out : Wire (n + m) s) (κ : TreeCheck n m s d) :
    treeLits p v_out (.inl κ) = checkLits p v_out κ := rfl

omit [CommSemiring K] in
/-- `treeLits` on a weighting clause. -/
@[simp] public theorem treeLits_inr (p : Program (arithSignature K) (n + m) s)
    (v_out : Wire (n + m) s) (κ : TreeWeight n m s d) :
    treeLits p v_out (.inr κ) = weightLits κ := rfl

/-- Combined weights for the interval-tree domain clause sum. -/
@[expose] public noncomputable def treeWeights (p : Program (arithSignature K) (n + m) s)
    (v_out : Wire (n + m) s) :
    TreeCheck n m s d ⊕ TreeWeight n m s d → MvPolynomial (Fin n) K :=
  Sum.elim (fun _ => 0) (weightVals p v_out)

omit [CommSemiring K] in
/-- Every checking clause is nonempty. -/
public theorem checkLits_ne_nil (p : Program (arithSignature K) (n + m) s)
    (v_out : Wire (n + m) s) (κ : TreeCheck n m s d) :
    checkLits p v_out κ ≠ [] := by
  cases κ <;> dsimp [checkLits] <;> (try split_ifs) <;> (try split) <;> simp

omit [CommSemiring K] in
/-- Every checking clause has length at most `3`. -/
public theorem checkLits_length_le (p : Program (arithSignature K) (n + m) s)
    (v_out : Wire (n + m) s) (κ : TreeCheck n m s d) :
    (checkLits p v_out κ).length ≤ 3 := by
  cases κ <;> dsimp [checkLits] <;> (try split_ifs) <;> (try split) <;> simp

/-- Every weighting clause is nonempty. -/
public theorem weightLits_ne_nil (κ : TreeWeight n m s d) :
    (weightLits (n := n) (m := m) (s := s) (d := d) κ) ≠ [] := by
  cases κ <;> simp [weightLits]

/-- Every weighting clause has length at most `2`. -/
public theorem weightLits_length_le (κ : TreeWeight n m s d) :
    (weightLits (n := n) (m := m) (s := s) (d := d) κ).length ≤ 2 := by
  cases κ <;> simp [weightLits]

/-- Every weight in `treeWeights` is either a variable `X i` or a constant `C a`. -/
public theorem treeWeights_var_or_const (p : Program (arithSignature K) (n + m) s)
    (v_out : Wire (n + m) s) (κ : TreeCheck n m s d ⊕ TreeWeight n m s d) :
    (∃ i, treeWeights p v_out κ = X i) ∨ ∃ a, treeWeights p v_out κ = C a := by
  rcases κ with c | w
  · exact Or.inr ⟨0, map_zero C |>.symm⟩
  · cases w with
    | degZero => exact Or.inr ⟨_, rfl⟩
    | internalCoeff _ _ _ _ => exact Or.inr ⟨_, rfl⟩
    | leafCoeff _ _ _ => exact Or.inr ⟨_, rfl⟩
    | leafInput _ i => exact Or.inl ⟨i, rfl⟩

/-- Semantic validity predicate for an interval-tree assignment `F`. -/
@[expose] public def IsValidAssign (p : Program (arithSignature K) (n + m) s)
    (v_out : Wire (n + m) s) (F : ∀ x : TreeDom m d, TreeVal (n + m) s d x) : Prop :=
  (∀ l r : Fin d, F (.par l r) = .root ↔ l.1 = 0 ∧ (F .rootDeg).1 = r.1 + 1) ∧
  (∀ l r : Fin d, F (.par l r) = .root → F (.wire l r) = some v_out) ∧
  (∀ l r : Fin d, F (.par l r) = .none ↔ F (.wire l r) = none) ∧
  (∀ l r : Fin d, l.1 < r.1 → (F (.par l r) = .none ↔ F (.split l r) = none)) ∧
  (∀ l r : Fin d, ¬ (l.1 < r.1) → F (.split l r) = none) ∧
  (∀ l r : Fin d, l.1 < r.1 → (F (.par l r) = .none ↔ F (.gate l r) = none)) ∧
  (∀ l r : Fin d, ¬ (l.1 < r.1) → F (.gate l r) = none) ∧
  (∀ l : Fin d, F (.par l l) = .none ↔ F (.leafVar l) = none) ∧
  (∀ l r : Fin d, r.1 < l.1 → F (.par l r) = .none) ∧
  (∀ l r r' : Fin d, F (.par l r) = .leftOf r' → r.1 < r'.1) ∧
  (∀ l r l' : Fin d, F (.par l r) = .rightOf l' → l'.1 < l.1) ∧
  (∀ l r q : Fin d, F (.split l r) = some q → l.1 ≤ q.1 ∧ q.1 < r.1) ∧
  (∀ l r q : Fin d, l.1 ≤ q.1 → q.1 < r.1 →
    (F (.split l r) = some q ↔ F (.par l q) = .leftOf r)) ∧
  (∀ l r q : Fin d, ∀ hq : q.1 < r.1, l.1 ≤ q.1 →
    (F (.split l r) = some q ↔ F (.par ⟨q.1 + 1, by omega⟩ r) = .rightOf l)) ∧
  (∀ l r : Fin d, ∀ g : Fin s, F (.gate l r) = some g → isMulGate p g = true) ∧
  (∀ l r q : Fin d, ∀ g : Fin s, l.1 ≤ q.1 → q.1 < r.1 →
    F (.split l r) = some q → F (.gate l r) = some g →
    F (.wire l q) = mulLeftWire p g) ∧
  (∀ l r q : Fin d, ∀ g : Fin s, ∀ hq : q.1 < r.1, l.1 ≤ q.1 →
    F (.split l r) = some q → F (.gate l r) = some g →
    F (.wire ⟨q.1 + 1, by omega⟩ r) = mulRightWire p g) ∧
  (∀ l : Fin d, ∀ b : Fin m, F (.leafVar l) = some (Fin.natAdd n b) → F (.boolVar b) = true)

private theorem lit_true_iff (F : ∀ x : TreeDom m d, TreeVal (n + m) s d x)
    (x : TreeDom m d) (v : TreeVal (n + m) s d x) :
    (Sum.elim Empty.elim (Pi.oneHot F) (.inr ⟨x, v⟩) = true) ↔ F x = v := by
  simp [Pi.oneHot]

private theorem lit_false_iff (F : ∀ x : TreeDom m d, TreeVal (n + m) s d x)
    (x : TreeDom m d) (v : TreeVal (n + m) s d x) :
    (Sum.elim Empty.elim (Pi.oneHot F) (.inr ⟨x, v⟩) = false) ↔ F x ≠ v := by
  simp [Pi.oneHot]

/-- The product of all checking clauses is `1` on semantically valid assignments and `0`
otherwise. -/
public theorem check_prod_eq_ite (p : Program (arithSignature K) (n + m) s)
    (v_out : Wire (n + m) s) (F : ∀ x : TreeDom m d, TreeVal (n + m) s d x)
    [Decidable (IsValidAssign p v_out F)] :
    (∏ κ : TreeCheck n m s d,
      if ∀ l ∈ checkLits p v_out κ, Sum.elim Empty.elim (Pi.oneHot F) l.1 = l.2 then
        (0 : MvPolynomial (Fin n) K)
      else 1) =
    if IsValidAssign p v_out F then 1 else 0 := by
  classical
  have hiff : (∀ κ : TreeCheck n m s d,
      ¬ ∀ l ∈ checkLits p v_out κ, Sum.elim Empty.elim (Pi.oneHot F) l.1 = l.2) ↔
      IsValidAssign p v_out F := by
    have hmul_some : ∀ g : Fin s, isMulGate p g = true →
        (∃ u, mulLeftWire p g = some u) ∧ (∃ v, mulRightWire p g = some v) := fun g hg => by
      rw [isMulGate_eq_isSome] at hg
      rw [mulLeftWire_eq_map, mulRightWire_eq_map]
      cases hmw : mulWires (p.lines g) with
      | none => simp [hmw] at hg
      | some uv => exact ⟨⟨uv.1, rfl⟩, ⟨uv.2, rfl⟩⟩
    constructor
    · intro h
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro l r
        constructor
        · intro hpar
          have hc := h (.parRootToDeg l r)
          simp only [checkLits] at hc
          split_ifs at hc with hl
          · simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
              and_true, lit_true_iff, lit_false_iff, not_and, not_not] at hc
            exact ⟨hl, by rw [hc hpar]⟩
          · simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
              and_true, lit_true_iff] at hc
            exact absurd hpar hc
        · rintro ⟨hl, hdeg⟩
          have hc := h (.rootDegToPar r)
          simp only [checkLits, List.forall_mem_cons, List.not_mem_nil, false_implies,
            implies_true, and_true, lit_true_iff, lit_false_iff, not_and, not_not] at hc
          have hl0 : l = ⟨0, Nat.zero_lt_of_lt l.isLt⟩ := Fin.ext hl
          rw [hl0]
          exact hc (Fin.ext hdeg)
      · intro l r hpar
        have hc := h (.parRootToWire l r)
        simp only [checkLits, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
          and_true, lit_true_iff, lit_false_iff, not_and, not_not] at hc
        exact hc hpar
      · intro l r
        constructor
        · intro hpar
          have hc := h (.parNoneToWire l r)
          simp only [checkLits, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
            and_true, lit_true_iff, lit_false_iff, not_and, not_not] at hc
          exact hc hpar
        · intro hw
          have hc := h (.wireNoneToPar l r)
          simp only [checkLits, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
            and_true, lit_true_iff, lit_false_iff, not_and] at hc
          by_contra hne
          exact hc hne hw
      · intro l r hlr
        constructor
        · intro hpar
          have hc := h (.parNoneToSplit l r)
          simp only [checkLits, hlr, ↓reduceIte, List.forall_mem_cons, List.not_mem_nil,
            false_implies, implies_true, and_true, lit_true_iff, lit_false_iff, not_and,
            not_not] at hc
          exact hc hpar
        · intro hs
          have hc := h (.splitNoneToPar l r)
          simp only [checkLits, hlr, ↓reduceIte, List.forall_mem_cons, List.not_mem_nil,
            false_implies, implies_true, and_true, lit_true_iff, lit_false_iff, not_and] at hc
          by_contra hne
          exact hc hne hs
      · intro l r hlr
        have hc := h (.parNoneToSplit l r)
        simp only [checkLits, hlr, ↓reduceIte, List.forall_mem_cons, List.not_mem_nil,
          false_implies, implies_true, and_true, lit_false_iff, not_not] at hc
        exact hc
      · intro l r hlr
        constructor
        · intro hpar
          have hc := h (.parNoneToGate l r)
          simp only [checkLits, hlr, ↓reduceIte, List.forall_mem_cons, List.not_mem_nil,
            false_implies, implies_true, and_true, lit_true_iff, lit_false_iff, not_and,
            not_not] at hc
          exact hc hpar
        · intro hg
          have hc := h (.gateNoneToPar l r)
          simp only [checkLits, hlr, ↓reduceIte, List.forall_mem_cons, List.not_mem_nil,
            false_implies, implies_true, and_true, lit_true_iff, lit_false_iff, not_and] at hc
          by_contra hne
          exact hc hne hg
      · intro l r hlr
        have hc := h (.parNoneToGate l r)
        simp only [checkLits, hlr, ↓reduceIte, List.forall_mem_cons, List.not_mem_nil,
          false_implies, implies_true, and_true, lit_false_iff, not_not] at hc
        exact hc
      · intro l
        constructor
        · intro hpar
          have hc := h (.parNoneToLeaf l)
          simp only [checkLits, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
            and_true, lit_true_iff, lit_false_iff, not_and, not_not] at hc
          exact hc hpar
        · intro hl
          have hc := h (.leafNoneToPar l)
          simp only [checkLits, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
            and_true, lit_true_iff, lit_false_iff, not_and] at hc
          by_contra hne
          exact hc hne hl
      · intro l r hrl
        have hc := h (.badOrder l r)
        simp only [checkLits, hrl, ↓reduceIte, List.forall_mem_cons, List.not_mem_nil,
          false_implies, implies_true, and_true, lit_false_iff, not_not] at hc
        exact hc
      · intro l r r' hpar
        by_contra hlt
        have hc := h (.badLeftPar l r r')
        simp only [checkLits, hlt, not_false_eq_true, ↓reduceIte, List.forall_mem_cons,
          List.not_mem_nil, false_implies, implies_true, and_true, lit_true_iff] at hc
        exact hc hpar
      · intro l r l' hpar
        by_contra hlt
        have hc := h (.badRightPar l r l')
        simp only [checkLits, hlt, not_false_eq_true, ↓reduceIte, List.forall_mem_cons,
          List.not_mem_nil, false_implies, implies_true, and_true, lit_true_iff] at hc
        exact hc hpar
      · intro l r q hs
        by_contra hq
        have hc := h (.badSplit l r q)
        simp only [checkLits, hq, not_false_eq_true, ↓reduceIte, List.forall_mem_cons,
          List.not_mem_nil, false_implies, implies_true, and_true, lit_true_iff] at hc
        exact hc hs
      · intro l r q h1 h2
        constructor
        · intro hs
          have hc := h (.splitToLeftPar l r q)
          simp only [checkLits, h1, h2, and_self, ↓reduceIte, List.forall_mem_cons,
            List.not_mem_nil, false_implies, implies_true, and_true, lit_true_iff, lit_false_iff,
            not_and, not_not] at hc
          exact hc hs
        · intro hp
          have hc := h (.leftParToSplit l r q)
          simp only [checkLits, h1, h2, and_self, ↓reduceIte, List.forall_mem_cons,
            List.not_mem_nil, false_implies, implies_true, and_true, lit_true_iff, lit_false_iff,
            not_and, not_not] at hc
          exact hc hp
      · intro l r q h2 h1
        constructor
        · intro hs
          have hc := h (.splitToRightPar l r q)
          simp only [checkLits, h1, h2, and_self, ↓reduceDIte, List.forall_mem_cons,
            List.not_mem_nil, false_implies, implies_true, and_true, lit_true_iff, lit_false_iff,
            not_and, not_not] at hc
          exact hc hs
        · intro hp
          have hc := h (.rightParToSplit l r q)
          simp only [checkLits, h1, h2, and_self, ↓reduceDIte, List.forall_mem_cons,
            List.not_mem_nil, false_implies, implies_true, and_true, lit_true_iff, lit_false_iff,
            not_and, not_not] at hc
          exact hc hp
      · intro l r g hg
        by_contra hnm
        have hfalse : isMulGate p g = false := Bool.eq_false_iff.2 hnm
        have hc := h (.badGate l r g)
        simp only [checkLits, hfalse, ↓reduceIte, List.forall_mem_cons, List.not_mem_nil,
          false_implies, implies_true, and_true, lit_true_iff] at hc
        exact hc hg
      · intro l r q g h1 h2 hs hg
        have hc := h (.gateLeftWire l r q g)
        simp only [checkLits, h1, h2, and_self, ↓reduceDIte] at hc
        cases hml : mulLeftWire p g with
        | none =>
            simp only [hml, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
              and_true, lit_true_iff] at hc
            exact absurd hg hc
        | some u =>
            simp only [hml, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
              and_true, lit_true_iff, lit_false_iff, not_and, not_not] at hc
            exact hc hs hg
      · intro l r q g h2 h1 hs hg
        have hc := h (.gateRightWire l r q g)
        simp only [checkLits, h1, h2, and_self, ↓reduceDIte] at hc
        cases hmr : mulRightWire p g with
        | none =>
            simp only [hmr, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
              and_true, lit_true_iff] at hc
            exact absurd hg hc
        | some v =>
            simp only [hmr, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
              and_true, lit_true_iff, lit_false_iff, not_and, not_not] at hc
            exact hc hs hg
      · intro l b hl
        have hc := h (.leafBool l b)
        simp only [checkLits, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
          and_true, lit_true_iff, not_and] at hc
        cases hb : F (.boolVar b)
        · exact absurd hb (hc hl)
        · rfl
    · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ κ
      cases κ with
      | rootDegToPar r =>
          simp only [checkLits, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
            and_true, lit_true_iff, lit_false_iff, not_and, not_not]
          intro hdeg
          exact (h1 ⟨0, Nat.zero_lt_of_lt r.isLt⟩ r).2 ⟨rfl, by rw [hdeg]⟩
      | parRootToDeg l r =>
          simp only [checkLits]
          split_ifs with hl
          · simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
              and_true, lit_true_iff, lit_false_iff, not_and, not_not]
            intro hp
            exact Fin.ext ((h1 l r).1 hp).2
          · simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
              and_true, lit_true_iff]
            intro hp
            exact hl ((h1 l r).1 hp).1
      | parRootToWire l r =>
          simp only [checkLits, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
            and_true, lit_true_iff, lit_false_iff, not_and, not_not]
          exact h2 l r
      | parNoneToWire l r =>
          simp only [checkLits, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
            and_true, lit_true_iff, lit_false_iff, not_and, not_not]
          exact (h3 l r).1
      | wireNoneToPar l r =>
          simp only [checkLits, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
            and_true, lit_true_iff, lit_false_iff, not_and]
          intro hne hw
          exact hne ((h3 l r).2 hw)
      | parNoneToSplit l r =>
          simp only [checkLits]
          split_ifs with hlr
          · simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
              and_true, lit_true_iff, lit_false_iff, not_and, not_not]
            exact (h4 l r hlr).1
          · simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
              and_true, lit_false_iff, not_not]
            exact h5 l r hlr
      | splitNoneToPar l r =>
          simp only [checkLits]
          split_ifs with hlr
          · simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
              and_true, lit_true_iff, lit_false_iff, not_and]
            intro hne hs
            exact hne ((h4 l r hlr).2 hs)
          · simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
              and_true, lit_false_iff, not_not]
            exact h5 l r hlr
      | parNoneToGate l r =>
          simp only [checkLits]
          split_ifs with hlr
          · simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
              and_true, lit_true_iff, lit_false_iff, not_and, not_not]
            exact (h6 l r hlr).1
          · simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
              and_true, lit_false_iff, not_not]
            exact h7 l r hlr
      | gateNoneToPar l r =>
          simp only [checkLits]
          split_ifs with hlr
          · simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
              and_true, lit_true_iff, lit_false_iff, not_and]
            intro hne hg
            exact hne ((h6 l r hlr).2 hg)
          · simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
              and_true, lit_false_iff, not_not]
            exact h7 l r hlr
      | parNoneToLeaf l =>
          simp only [checkLits, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
            and_true, lit_true_iff, lit_false_iff, not_and, not_not]
          exact (h8 l).1
      | leafNoneToPar l =>
          simp only [checkLits, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
            and_true, lit_true_iff, lit_false_iff, not_and]
          intro hne hl
          exact hne ((h8 l).2 hl)
      | badOrder l r =>
          simp only [checkLits]
          split_ifs with hrl
          · simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
              and_true, lit_false_iff, not_not]
            exact h9 l r hrl
          · simp
      | badLeftPar l r r' =>
          simp only [checkLits]
          split_ifs with hlt
          · simp
          · simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
              and_true, lit_true_iff]
            intro hp; exact hlt (h10 l r r' hp)
      | badRightPar l r l' =>
          simp only [checkLits]
          split_ifs with hlt
          · simp
          · simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
              and_true, lit_true_iff]
            intro hp; exact hlt (h11 l r l' hp)
      | badSplit l r q =>
          simp only [checkLits]
          split_ifs with hq
          · simp
          · simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
              and_true, lit_true_iff]
            intro hs; exact hq (h12 l r q hs)
      | splitToLeftPar l r q =>
          simp only [checkLits]
          split_ifs with hq
          · simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
              and_true, lit_true_iff, lit_false_iff, not_and, not_not]
            exact (h13 l r q hq.1 hq.2).1
          · simp
      | leftParToSplit l r q =>
          simp only [checkLits]
          split_ifs with hq
          · simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
              and_true, lit_true_iff, lit_false_iff, not_and, not_not]
            exact (h13 l r q hq.1 hq.2).2
          · simp
      | splitToRightPar l r q =>
          simp only [checkLits]
          split_ifs with hq
          · simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
              and_true, lit_true_iff, lit_false_iff, not_and, not_not]
            exact (h14 l r q hq.2 hq.1).1
          · simp
      | rightParToSplit l r q =>
          simp only [checkLits]
          split_ifs with hq
          · simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
              and_true, lit_true_iff, lit_false_iff, not_and, not_not]
            exact (h14 l r q hq.2 hq.1).2
          · simp
      | badGate l r g =>
          simp only [checkLits]
          split_ifs with hnm
          · simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
              and_true, lit_true_iff]
            intro hg
            have := h15 l r g hg
            simp [hnm] at this
          · simp
      | gateLeftWire l r q g =>
          simp only [checkLits]
          split_ifs with hq
          · cases hml : mulLeftWire p g with
            | none =>
                simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
                  and_true, lit_true_iff]
                intro hg
                obtain ⟨⟨u, hu⟩, -⟩ := hmul_some g (h15 l r g hg)
                simp [hml] at hu
            | some u =>
                simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
                  and_true, lit_true_iff, lit_false_iff, not_and, not_not]
                intro hs hg
                simpa [hml] using h16 l r q g hq.1 hq.2 hs hg
          · simp
      | gateRightWire l r q g =>
          simp only [checkLits]
          split_ifs with hq
          · cases hmr : mulRightWire p g with
            | none =>
                simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
                  and_true, lit_true_iff]
                intro hg
                obtain ⟨-, ⟨v, hv⟩⟩ := hmul_some g (h15 l r g hg)
                simp [hmr] at hv
            | some v =>
                simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
                  and_true, lit_true_iff, lit_false_iff, not_and, not_not]
                intro hs hg
                simpa [hmr] using h17 l r q g hq.2 hq.1 hs hg
          · simp
      | leafBool l b =>
          simp only [checkLits, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
            and_true, lit_true_iff, not_and]
          intro hl hb
          have := h18 l b hl
          simp [hb] at this
  by_cases hv : IsValidAssign p v_out F
  · rw [ite_eq_left hv]
    refine Finset.prod_eq_one fun κ _ => ?_
    exact ite_eq_right (hiff.2 hv κ)
  · rw [ite_eq_right hv]
    have hnot : ∃ κ, ∀ l ∈ checkLits p v_out κ,
        Sum.elim Empty.elim (Pi.oneHot F) l.1 = l.2 := by
      by_contra hall
      exact hv (hiff.1 fun κ hκ => hall ⟨κ, hκ⟩)
    obtain ⟨κ, hκ⟩ := hnot
    exact Finset.prod_eq_zero (Finset.mem_univ κ) (ite_eq_left hκ)

/-- Simplified formula for the product of all weighting clauses on a valid assignment `F`. -/
@[expose] public noncomputable def assignWeight (p : Program (arithSignature K) (n + m) s)
    (v_out : Wire (n + m) s) (F : ∀ x : TreeDom m d, TreeVal (n + m) s d x) :
    MvPolynomial (Fin n) K :=
  (if F .rootDeg = 0 then C (wireConst p v_out) else 1) *
  (∏ l : Fin d, ∏ r : Fin d,
    match F (.wire l r), F (.gate l r) with
    | some w, some g => C (linCoeff p w (.gate g))
    | _, _ => 1) *
  (∏ l : Fin d,
    match F (.wire l l), F (.leafVar l) with
    | some w, some j => C (linCoeff p w (.input j))
    | _, _ => 1) *
  (∏ l : Fin d,
    match F (.leafVar l) with
    | some j => varVal (fun b => F (.boolVar b)) j
    | none => 1)

/-- Product expansion of `assignWeight`. -/
public theorem assignWeight_eq_prod (p : Program (arithSignature K) (n + m) s)
    (v_out : Wire (n + m) s) (F : ∀ x : TreeDom m d, TreeVal (n + m) s d x) :
    assignWeight p v_out F =
      (if F .rootDeg = 0 then C (wireConst p v_out) else 1) *
      (∏ l : Fin d, ∏ r : Fin d,
        match F (.wire l r), F (.gate l r) with
        | some w, some g => C (linCoeff p w (.gate g))
        | _, _ => 1) *
      (∏ l : Fin d,
        match F (.wire l l), F (.leafVar l) with
        | some w, some j => C (linCoeff p w (.input j))
        | _, _ => 1) *
      (∏ l : Fin d,
        match F (.leafVar l) with
        | some j => varVal (fun b => F (.boolVar b)) j
        | none => 1) := rfl

/-- On any valid assignment `F`, the product of weighting clauses equals `assignWeight`. -/
public theorem weight_prod_eq_assignWeight (p : Program (arithSignature K) (n + m) s)
    (v_out : Wire (n + m) s) (F : ∀ x : TreeDom m d, TreeVal (n + m) s d x)
    (hF : IsValidAssign p v_out F) :
    (∏ κ : TreeWeight n m s d,
      if ∀ l ∈ weightLits κ, Sum.elim Empty.elim (Pi.oneHot F) l.1 = l.2 then
        weightVals p v_out κ
      else 1) = assignWeight p v_out F := by
  rw [← (treeWeightEquiv n m s d).symm.prod_comp]
  simp only [Fintype.prod_sum_type, Fintype.prod_unique, Fintype.prod_prod_type,
    treeWeightEquiv, Equiv.coe_fn_symm_mk, assignWeight, ← mul_assoc]
  congr 1
  · congr 1
    · congr 1
      · simp [weightLits, weightVals]
      · refine Finset.prod_congr rfl fun l _ => Finset.prod_congr rfl fun r _ => ?_
        cases hw : F (.wire l r) with
        | none =>
            refine Finset.prod_eq_one fun w _ => Finset.prod_eq_one fun g _ => ?_
            simp [weightLits, hw]
        | some w₀ =>
            cases hg : F (.gate l r) with
            | none =>
                refine Finset.prod_eq_one fun w _ => Finset.prod_eq_one fun g _ => ?_
                simp [weightLits, hg]
            | some g₀ =>
                rw [Finset.prod_eq_single w₀]
                · rw [Finset.prod_eq_single g₀]
                  · simp [weightLits, weightVals, hw, hg]
                  · intro g _ hne; simp [weightLits, hg, Ne.symm hne]
                  · intro h; exact absurd (Finset.mem_univ g₀) h
                · intro w _ hne
                  refine Finset.prod_eq_one fun g _ => ?_
                  simp [weightLits, hw, Ne.symm hne]
                · intro h; exact absurd (Finset.mem_univ w₀) h
    · refine Finset.prod_congr rfl fun l _ => ?_
      cases hw : F (.wire l l) with
      | none =>
          refine Finset.prod_eq_one fun w _ => Finset.prod_eq_one fun j _ => ?_
          simp [weightLits, hw]
      | some w₀ =>
          cases hj : F (.leafVar l) with
          | none =>
              refine Finset.prod_eq_one fun w _ => Finset.prod_eq_one fun j _ => ?_
              simp [weightLits, hj]
          | some j₀ =>
              rw [Finset.prod_eq_single w₀]
              · rw [Finset.prod_eq_single j₀]
                · simp [weightLits, weightVals, hw, hj]
                · intro j _ hne; simp [weightLits, hj, Ne.symm hne]
                · intro h; exact absurd (Finset.mem_univ j₀) h
              · intro w _ hne
                refine Finset.prod_eq_one fun j _ => ?_
                simp [weightLits, hw, Ne.symm hne]
              · intro h; exact absurd (Finset.mem_univ w₀) h
  · refine Finset.prod_congr rfl fun l _ => ?_
    cases hj : F (.leafVar l) with
    | none =>
        refine Finset.prod_eq_one fun i _ => ?_
        simp [weightLits, hj]
    | some j₀ =>
        revert hj
        refine Fin.addCases ?_ ?_ j₀
        · intro i₀ hj
          rw [Finset.prod_eq_single i₀]
          · simp [weightLits, weightVals, hj]
          · intro i _ hne
            have hne' : Fin.castAdd m i₀ ≠ Fin.castAdd m i := fun h =>
              hne (Fin.ext (by simpa using congrArg Fin.val h)).symm
            simp [weightLits, hj, hne']
          · intro h; exact absurd (Finset.mem_univ i₀) h
        · intro b₀ hj
          have htrue : F (.boolVar b₀) = true := hF.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 l b₀ hj
          have hval : (match some (Fin.natAdd n b₀) with
              | some j => varVal (K := K) (fun b => F (.boolVar b)) j
              | none => 1) = 1 := by
            simp [htrue]
          refine Eq.trans ?_ hval.symm
          refine Finset.prod_eq_one fun i _ => ?_
          have hne : Fin.natAdd n b₀ ≠ Fin.castAdd m i := by
            intro h; have := congrArg Fin.val h; simp at this; omega
          simp [weightLits, hj, hne]

end TreeClauses

end CslibFrontier.Computability.Circuit.Arithmetic.Permanent
