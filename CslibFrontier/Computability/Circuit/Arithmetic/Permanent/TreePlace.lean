module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Permanent.TreeEncode
import Mathlib.Algebra.BigOperators.Fin

/-!
# Forward Placement of Binary Parse Trees into Interval-Tree Assignments

Constructs the canonical embedding `assignOfPTree` of legal binary parse trees (`PTree`) into valid
interval-tree assignments (`isValidAssign_assignOfPTree`) and proves that the weighting-clause
product reproduces parse-tree evaluation (`assignWeight_assignOfPTree`).
-/

public section

namespace CslibFrontier.Computability.Circuit.Arithmetic.Permanent

open Cslib Cslib.Circuits Cslib.Circuits.Arithmetic MvPolynomial Finset

universe u

section TreePlace

variable {K : Type u} [CommSemiring K] {n m s d : ℕ}
/-! ### Forward placement of a `PTree` onto intervals -/

/-- Parent-pointer placement of a `PTree` on `[lo, lo + k]`. -/
@[expose] public def placePar (p : Program (arithSignature K) (n + m) s) (d : ℕ) :
    ∀ {k : ℕ} (lo : ℕ) (_ : lo + k < d), ParKind d → PTree (n + m) s k →
      Fin d → Fin d → ParKind d
  | 0, lo, _, pk, .leaf _, l, r =>
      if l.1 = lo ∧ r.1 = lo then pk else .none
  | k + 1, lo, hhi, pk, .node _ a L R, l, r =>
      if l.1 = lo ∧ r.1 = lo + k + 1 then pk
      else if r.1 ≤ lo + a.1 then
        placePar p d lo (by omega) (.leftOf ⟨lo + k + 1, by omega⟩) L l r
      else if lo + a.1 + 1 ≤ l.1 then
        placePar p d (lo + a.1 + 1) (by omega) (.rightOf ⟨lo, by omega⟩) R l r
      else .none

/-- Wire placement of a `PTree` on `[lo, lo + k]`. -/
@[expose] public def placeWire (p : Program (arithSignature K) (n + m) s) (d : ℕ) :
    ∀ {k : ℕ} (lo : ℕ) (_ : lo + k < d), Wire (n + m) s → PTree (n + m) s k →
      Fin d → Fin d → Option (Wire (n + m) s)
  | 0, lo, _, w, .leaf _, l, r =>
      if l.1 = lo ∧ r.1 = lo then some w else none
  | k + 1, lo, hhi, w, .node g a L R, l, r =>
      if l.1 = lo ∧ r.1 = lo + k + 1 then some w
      else if r.1 ≤ lo + a.1 then
        match mulLeftWire p g with
        | some u => placeWire p d lo (by omega) u L l r
        | none => none
      else if lo + a.1 + 1 ≤ l.1 then
        match mulRightWire p g with
        | some v => placeWire p d (lo + a.1 + 1) (by omega) v R l r
        | none => none
      else none

/-- Split-point placement of a `PTree` on `[lo, lo + k]`. -/
@[expose] public def placeSplit (d : ℕ) :
    ∀ {k : ℕ} (lo : ℕ) (_ : lo + k < d), PTree (n + m) s k →
      Fin d → Fin d → Option (Fin d)
  | 0, _, _, .leaf _, _, _ => none
  | k + 1, lo, hhi, .node _ a L R, l, r =>
      if l.1 = lo ∧ r.1 = lo + k + 1 then some ⟨lo + a.1, by omega⟩
      else if r.1 ≤ lo + a.1 then placeSplit d lo (by omega) L l r
      else if lo + a.1 + 1 ≤ l.1 then placeSplit d (lo + a.1 + 1) (by omega) R l r
      else none

/-- Gate placement of a `PTree` on `[lo, lo + k]`. -/
@[expose] public def placeGate (d : ℕ) :
    ∀ {k : ℕ} (lo : ℕ) (_ : lo + k < d), PTree (n + m) s k →
      Fin d → Fin d → Option (Fin s)
  | 0, _, _, .leaf _, _, _ => none
  | k + 1, lo, hhi, .node g a L R, l, r =>
      if l.1 = lo ∧ r.1 = lo + k + 1 then some g
      else if r.1 ≤ lo + a.1 then placeGate d lo (by omega) L l r
      else if lo + a.1 + 1 ≤ l.1 then placeGate d (lo + a.1 + 1) (by omega) R l r
      else none

/-- Leaf-variable placement of a `PTree` on `[lo, lo + k]`. -/
@[expose] public def placeLeaf (d : ℕ) :
    ∀ {k : ℕ} (lo : ℕ) (_ : lo + k < d), PTree (n + m) s k →
      Fin d → Option (Fin (n + m))
  | 0, lo, _, .leaf j, l => if l.1 = lo then some j else none
  | k + 1, lo, hhi, .node _ a L R, l =>
      if l.1 ≤ lo + a.1 then placeLeaf d lo (by omega) L l
      else placeLeaf d (lo + a.1 + 1) (by omega) R l

omit [CommSemiring K] in
/-- `placePar` on a leaf tree. -/
@[simp] public theorem placePar_leaf (p : Program (arithSignature K) (n + m) s) {d lo : ℕ}
    (hhi : lo + 0 < d) (pk : ParKind d) (j : Fin (n + m)) (l r : Fin d) :
    placePar p d lo hhi pk (.leaf j) l r = if l.1 = lo ∧ r.1 = lo then pk else .none := rfl

omit [CommSemiring K] in
/-- `placePar` on an internal node tree. -/
@[simp] public theorem placePar_node (p : Program (arithSignature K) (n + m) s) {d k lo : ℕ}
    (hhi : lo + (k + 1) < d) (pk : ParKind d) (g : Fin s) (a : Fin (k + 1))
    (L : PTree (n + m) s a.1) (R : PTree (n + m) s (k - a.1)) (l r : Fin d) :
    placePar p d lo hhi pk (.node g a L R) l r =
      if l.1 = lo ∧ r.1 = lo + k + 1 then pk
      else if r.1 ≤ lo + a.1 then
        placePar p d lo (by omega) (.leftOf ⟨lo + k + 1, by omega⟩) L l r
      else if lo + a.1 + 1 ≤ l.1 then
        placePar p d (lo + a.1 + 1) (by omega) (.rightOf ⟨lo, by omega⟩) R l r
      else .none := rfl

omit [CommSemiring K] in
/-- `placeWire` on a leaf tree. -/
@[simp] public theorem placeWire_leaf (p : Program (arithSignature K) (n + m) s) {d lo : ℕ}
    (hhi : lo + 0 < d) (w : Wire (n + m) s) (j : Fin (n + m)) (l r : Fin d) :
    placeWire p d lo hhi w (.leaf j) l r = if l.1 = lo ∧ r.1 = lo then some w else none := rfl

omit [CommSemiring K] in
/-- `placeWire` on an internal node tree. -/
@[simp] public theorem placeWire_node (p : Program (arithSignature K) (n + m) s) {d k lo : ℕ}
    (hhi : lo + (k + 1) < d) (w : Wire (n + m) s) (g : Fin s) (a : Fin (k + 1))
    (L : PTree (n + m) s a.1) (R : PTree (n + m) s (k - a.1)) (l r : Fin d) :
    placeWire p d lo hhi w (.node g a L R) l r =
      if l.1 = lo ∧ r.1 = lo + k + 1 then some w
      else if r.1 ≤ lo + a.1 then
        match mulLeftWire p g with | some u => placeWire p d lo (by omega) u L l r | none => none
      else if lo + a.1 + 1 ≤ l.1 then
        match mulRightWire p g with
        | some v => placeWire p d (lo + a.1 + 1) (by omega) v R l r
        | none => none
      else none := rfl

/-- `placeSplit` on a leaf tree. -/
@[simp] public theorem placeSplit_leaf {d lo : ℕ} (hhi : lo + 0 < d) (j : Fin (n + m))
    (l r : Fin d) : placeSplit (s := s) d lo hhi (.leaf j) l r = none := rfl

/-- `placeSplit` on an internal node tree. -/
@[simp] public theorem placeSplit_node {d k lo : ℕ} (hhi : lo + (k + 1) < d) (g : Fin s)
    (a : Fin (k + 1)) (L : PTree (n + m) s a.1) (R : PTree (n + m) s (k - a.1)) (l r : Fin d) :
    placeSplit d lo hhi (.node g a L R) l r =
      if l.1 = lo ∧ r.1 = lo + k + 1 then some ⟨lo + a.1, by omega⟩
      else if r.1 ≤ lo + a.1 then placeSplit d lo (by omega) L l r
      else if lo + a.1 + 1 ≤ l.1 then placeSplit d (lo + a.1 + 1) (by omega) R l r
      else none := rfl

/-- `placeGate` on a leaf tree. -/
@[simp] public theorem placeGate_leaf {d lo : ℕ} (hhi : lo + 0 < d) (j : Fin (n + m))
    (l r : Fin d) : placeGate (s := s) d lo hhi (.leaf j) l r = none := rfl

/-- `placeGate` on an internal node tree. -/
@[simp] public theorem placeGate_node {d k lo : ℕ} (hhi : lo + (k + 1) < d) (g : Fin s)
    (a : Fin (k + 1)) (L : PTree (n + m) s a.1) (R : PTree (n + m) s (k - a.1)) (l r : Fin d) :
    placeGate d lo hhi (.node g a L R) l r =
      if l.1 = lo ∧ r.1 = lo + k + 1 then some g
      else if r.1 ≤ lo + a.1 then placeGate d lo (by omega) L l r
      else if lo + a.1 + 1 ≤ l.1 then placeGate d (lo + a.1 + 1) (by omega) R l r
      else none := rfl

/-- `placeLeaf` on a leaf tree. -/
@[simp] public theorem placeLeaf_leaf {d lo : ℕ} (hhi : lo + 0 < d) (j : Fin (n + m)) (l : Fin d) :
    placeLeaf (s := s) d lo hhi (.leaf j) l = if l.1 = lo then some j else none := rfl

/-- `placeLeaf` on an internal node tree. -/
@[simp] public theorem placeLeaf_node {d k lo : ℕ} (hhi : lo + (k + 1) < d) (g : Fin s)
    (a : Fin (k + 1)) (L : PTree (n + m) s a.1) (R : PTree (n + m) s (k - a.1)) (l : Fin d) :
    placeLeaf d lo hhi (.node g a L R) l =
      if l.1 ≤ lo + a.1 then placeLeaf d lo (by omega) L l
      else placeLeaf d (lo + a.1 + 1) (by omega) R l := rfl

omit [CommSemiring K] in
/-- `placePar` vanishes outside `[lo, lo + k]`. -/
public theorem placePar_outside (p : Program (arithSignature K) (n + m) s) {d k lo : ℕ}
    (hhi : lo + k < d) (pk : ParKind d) (T : PTree (n + m) s k) (l r : Fin d)
    (hout : l.1 < lo ∨ lo + k < r.1) :
    placePar p d lo hhi pk T l r = .none := by
  induction T generalizing lo pk with
  | leaf j =>
      simp only [placePar]; split_ifs <;> [omega; rfl]
  | @node g k' a L R ihL ihR =>
      simp only [placePar]
      split_ifs with h1 h2 h3
      · omega
      · exact ihL (by omega) _ (by omega)
      · exact ihR (by omega) _ (by omega)
      · rfl

omit [CommSemiring K] in
/-- `placeWire` vanishes outside `[lo, lo + k]`. -/
public theorem placeWire_outside (p : Program (arithSignature K) (n + m) s) {d k lo : ℕ}
    (hhi : lo + k < d) (w : Wire (n + m) s) (T : PTree (n + m) s k) (l r : Fin d)
    (hout : l.1 < lo ∨ lo + k < r.1) :
    placeWire p d lo hhi w T l r = none := by
  induction T generalizing lo w with
  | leaf j =>
      simp only [placeWire]; split_ifs <;> [omega; rfl]
  | @node g k' a L R ihL ihR =>
      simp only [placeWire]
      split_ifs with h1 h2 h3
      · omega
      · cases mulLeftWire p g with
        | none => rfl
        | some u => exact ihL (by omega) _ (by omega)
      · cases mulRightWire p g with
        | none => rfl
        | some v => exact ihR (by omega) _ (by omega)
      · rfl

/-- `placeSplit` vanishes outside `[lo, lo + k]`. -/
public theorem placeSplit_outside {d k lo : ℕ} (hhi : lo + k < d) (T : PTree (n + m) s k)
    (l r : Fin d) (hout : l.1 < lo ∨ lo + k < r.1) :
    placeSplit d lo hhi T l r = none := by
  induction T generalizing lo with
  | leaf j => rfl
  | @node g k' a L R ihL ihR =>
      simp only [placeSplit]
      split_ifs with h1 h2 h3
      · omega
      · exact ihL (by omega) (by omega)
      · exact ihR (by omega) (by omega)
      · rfl

/-- `placeGate` vanishes outside `[lo, lo + k]`. -/
public theorem placeGate_outside {d k lo : ℕ} (hhi : lo + k < d) (T : PTree (n + m) s k)
    (l r : Fin d) (hout : l.1 < lo ∨ lo + k < r.1) :
    placeGate d lo hhi T l r = none := by
  induction T generalizing lo with
  | leaf j => rfl
  | @node g k' a L R ihL ihR =>
      simp only [placeGate]
      split_ifs with h1 h2 h3
      · omega
      · exact ihL (by omega) (by omega)
      · exact ihR (by omega) (by omega)
      · rfl

/-- `placeLeaf` vanishes outside `[lo, lo + k]`. -/
public theorem placeLeaf_outside {d k lo : ℕ} (hhi : lo + k < d) (T : PTree (n + m) s k)
    (l : Fin d) (hout : l.1 < lo ∨ lo + k < l.1) :
    placeLeaf d lo hhi T l = none := by
  induction T generalizing lo with
  | leaf j =>
      simp only [placeLeaf]; split_ifs <;> [omega; rfl]
  | @node g k' a L R ihL ihR =>
      simp only [placeLeaf]
      split_ifs with h1
      · exact ihL (by omega) (by omega)
      · exact ihR (by omega) (by omega)

omit [CommSemiring K] in
/-- Value of `placePar` on the root interval `[lo, lo + k]`. -/
private theorem placePar_self (p : Program (arithSignature K) (n + m) s) {d k lo : ℕ}
    (hhi : lo + k < d) (pk : ParKind d) (T : PTree (n + m) s k) (l r : Fin d)
    (hl : l.1 = lo) (hr : r.1 = lo + k) :
    placePar p d lo hhi pk T l r = pk := by
  cases T <;> simp [hl, hr, Nat.add_assoc]

omit [CommSemiring K] in
/-- Value of `placeWire` on the root interval `[lo, lo + k]`. -/
private theorem placeWire_self (p : Program (arithSignature K) (n + m) s) {d k lo : ℕ}
    (hhi : lo + k < d) (w : Wire (n + m) s) (T : PTree (n + m) s k) (l r : Fin d)
    (hl : l.1 = lo) (hr : r.1 = lo + k) :
    placeWire p d lo hhi w T l r = some w := by
  cases T <;> simp [hl, hr, Nat.add_assoc]

omit [CommSemiring K] in
/-- If `placePar` returns `.leftOf r`, either it is the root `pk` or `[l, r] ⊆ [lo, lo + k]`. -/
private theorem placePar_leftOf_bound (p : Program (arithSignature K) (n + m) s) {d k lo : ℕ}
    (hhi : lo + k < d) (pk : ParKind d) (T : PTree (n + m) s k) (l q r : Fin d)
    (hp : placePar p d lo hhi pk T l q = .leftOf r) :
    (l.1 = lo ∧ q.1 = lo + k ∧ pk = .leftOf r) ∨ (lo ≤ l.1 ∧ r.1 ≤ lo + k) := by
  induction T generalizing lo pk with
  | leaf j =>
      simp only [placePar] at hp
      split_ifs at hp with h
      exact Or.inl ⟨h.1, h.2, hp⟩
  | @node g k' a L R ihL ihR =>
      simp only [placePar] at hp
      split_ifs at hp with h1 h2 h3
      · exact Or.inl ⟨h1.1, h1.2, hp⟩
      · rcases ihL (by omega) _ hp with ⟨hl, hq, heq⟩ | ⟨hl, hr⟩
        · injection heq with hr
          exact Or.inr ⟨by omega, by rw [← hr]; dsimp; omega⟩
        · exact Or.inr ⟨hl, by omega⟩
      · rcases ihR (by omega) _ hp with ⟨_, _, heq⟩ | ⟨hl, hr⟩
        · cases heq
        · exact Or.inr ⟨by omega, by omega⟩

omit [CommSemiring K] in
/-- If `placePar` returns `.rightOf l`, either it is the root `pk` or `[l, r] ⊆ [lo, lo + k]`. -/
private theorem placePar_rightOf_bound (p : Program (arithSignature K) (n + m) s) {d k lo : ℕ}
    (hhi : lo + k < d) (pk : ParKind d) (T : PTree (n + m) s k) (q' r l : Fin d)
    (hp : placePar p d lo hhi pk T q' r = .rightOf l) :
    (q'.1 = lo ∧ r.1 = lo + k ∧ pk = .rightOf l) ∨ (lo ≤ l.1 ∧ r.1 ≤ lo + k) := by
  induction T generalizing lo pk with
  | leaf j =>
      simp only [placePar] at hp
      split_ifs at hp with h
      exact Or.inl ⟨h.1, h.2, hp⟩
  | @node g k' a L R ihL ihR =>
      simp only [placePar] at hp
      split_ifs at hp with h1 h2 h3
      · exact Or.inl ⟨h1.1, h1.2, hp⟩
      · rcases ihL (by omega) _ hp with ⟨_, _, heq⟩ | ⟨hl, hr⟩
        · cases heq
        · exact Or.inr ⟨hl, by omega⟩
      · rcases ihR (by omega) _ hp with ⟨hq', hr, heq⟩ | ⟨hl, hr⟩
        · injection heq with hl
          exact Or.inr ⟨by rw [← hl], by omega⟩
        · exact Or.inr ⟨by omega, by omega⟩

/-- The unique degree-0 valid assignment for Boolean inputs `e`. -/
@[expose] public def assignZero (e : Fin m → Bool) :
    ∀ x : TreeDom m d, TreeVal (n + m) s d x
  | .boolVar b => e b
  | .rootDeg => 0
  | .par _ _ => .none
  | .wire _ _ => none
  | .split _ _ => none
  | .gate _ _ => none
  | .leafVar _ => none

/-- `assignZero` on `.boolVar`. -/
@[simp] public theorem assignZero_boolVar (e : Fin m → Bool) (b : Fin m) :
    assignZero (n := n) (s := s) (d := d) e (.boolVar b) = e b := rfl
/-- `assignZero` on `.rootDeg`. -/
@[simp] public theorem assignZero_rootDeg (e : Fin m → Bool) :
    assignZero (n := n) (s := s) (d := d) e .rootDeg = 0 := rfl
/-- `assignZero` on `.par`. -/
@[simp] public theorem assignZero_par (e : Fin m → Bool) (l r : Fin d) :
    assignZero (n := n) (s := s) (d := d) e (.par l r) = .none := rfl
/-- `assignZero` on `.wire`. -/
@[simp] public theorem assignZero_wire (e : Fin m → Bool) (l r : Fin d) :
    assignZero (n := n) (s := s) (d := d) e (.wire l r) = none := rfl
/-- `assignZero` on `.split`. -/
@[simp] public theorem assignZero_split (e : Fin m → Bool) (l r : Fin d) :
    assignZero (n := n) (s := s) (d := d) e (.split l r) = none := rfl
/-- `assignZero` on `.gate`. -/
@[simp] public theorem assignZero_gate (e : Fin m → Bool) (l r : Fin d) :
    assignZero (n := n) (s := s) (d := d) e (.gate l r) = none := rfl
/-- `assignZero` on `.leafVar`. -/
@[simp] public theorem assignZero_leafVar (e : Fin m → Bool) (l : Fin d) :
    assignZero (n := n) (s := s) (d := d) e (.leafVar l) = none := rfl

omit [CommSemiring K] in
/-- `assignZero e` is semantically valid. -/
public theorem isValidAssign_assignZero (p : Program (arithSignature K) (n + m) s)
    (v_out : Wire (n + m) s) (e : Fin m → Bool) :
    IsValidAssign p v_out (assignZero (n := n) (s := s) (d := d) e) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp

/-- Build the degree-`(k + 1)` assignment from Boolean inputs `e` and `T : PTree (n + m) s k`. -/
@[expose] public def assignOfPTree (p : Program (arithSignature K) (n + m) s)
    (v_out : Wire (n + m) s) (e : Fin m → Bool) {k : ℕ} (hk : k < d) (T : PTree (n + m) s k) :
    ∀ x : TreeDom m d, TreeVal (n + m) s d x
  | .boolVar b => e b
  | .rootDeg => ⟨k + 1, by omega⟩
  | .par l r => placePar p d 0 (by omega) .root T l r
  | .wire l r => placeWire p d 0 (by omega) v_out T l r
  | .split l r => placeSplit d 0 (by omega) T l r
  | .gate l r => placeGate d 0 (by omega) T l r
  | .leafVar l => placeLeaf d 0 (by omega) T l

omit [CommSemiring K] in
/-- `assignOfPTree` on `.boolVar`. -/
@[simp] public theorem assignOfPTree_boolVar (p : Program (arithSignature K) (n + m) s)
    (v_out : Wire (n + m) s) (e : Fin m → Bool) {k : ℕ} (hk : k < d) (T : PTree (n + m) s k)
    (b : Fin m) : assignOfPTree p v_out e hk T (.boolVar b) = e b := rfl
omit [CommSemiring K] in
/-- `assignOfPTree` on `.rootDeg`. -/
@[simp] public theorem assignOfPTree_rootDeg (p : Program (arithSignature K) (n + m) s)
    (v_out : Wire (n + m) s) (e : Fin m → Bool) {k : ℕ} (hk : k < d) (T : PTree (n + m) s k) :
    assignOfPTree p v_out e hk T .rootDeg = ⟨k + 1, by omega⟩ := rfl
omit [CommSemiring K] in
/-- `assignOfPTree` on `.par`. -/
@[simp] public theorem assignOfPTree_par (p : Program (arithSignature K) (n + m) s)
    (v_out : Wire (n + m) s) (e : Fin m → Bool) {k : ℕ} (hk : k < d) (T : PTree (n + m) s k)
    (l r : Fin d) :
    assignOfPTree p v_out e hk T (.par l r) = placePar p d 0 (by omega) .root T l r := rfl
omit [CommSemiring K] in
/-- `assignOfPTree` on `.wire`. -/
@[simp] public theorem assignOfPTree_wire (p : Program (arithSignature K) (n + m) s)
    (v_out : Wire (n + m) s) (e : Fin m → Bool) {k : ℕ} (hk : k < d) (T : PTree (n + m) s k)
    (l r : Fin d) :
    assignOfPTree p v_out e hk T (.wire l r) = placeWire p d 0 (by omega) v_out T l r := rfl
omit [CommSemiring K] in
/-- `assignOfPTree` on `.split`. -/
@[simp] public theorem assignOfPTree_split (p : Program (arithSignature K) (n + m) s)
    (v_out : Wire (n + m) s) (e : Fin m → Bool) {k : ℕ} (hk : k < d) (T : PTree (n + m) s k)
    (l r : Fin d) :
    assignOfPTree p v_out e hk T (.split l r) = placeSplit d 0 (by omega) T l r := rfl
omit [CommSemiring K] in
/-- `assignOfPTree` on `.gate`. -/
@[simp] public theorem assignOfPTree_gate (p : Program (arithSignature K) (n + m) s)
    (v_out : Wire (n + m) s) (e : Fin m → Bool) {k : ℕ} (hk : k < d) (T : PTree (n + m) s k)
    (l r : Fin d) :
    assignOfPTree p v_out e hk T (.gate l r) = placeGate d 0 (by omega) T l r := rfl
omit [CommSemiring K] in
/-- `assignOfPTree` on `.leafVar`. -/
@[simp] public theorem assignOfPTree_leafVar (p : Program (arithSignature K) (n + m) s)
    (v_out : Wire (n + m) s) (e : Fin m → Bool) {k : ℕ} (hk : k < d) (T : PTree (n + m) s k)
    (l : Fin d) :
    assignOfPTree p v_out e hk T (.leafVar l) = placeLeaf d 0 (by omega) T l := rfl

omit [CommSemiring K] in
private theorem place_invariants (p : Program (arithSignature K) (n + m) s) (e : Fin m → Bool)
    {d k lo : ℕ} (hhi : lo + k < d) (pk : ParKind d) (hpk : pk ≠ .none)
    (hpk_l : ∀ r', pk = .leftOf r' → lo + k < r'.1)
    (hpk_r : ∀ l', pk = .rightOf l' → l'.1 < lo)
    (w : Wire (n + m) s) (T : PTree (n + m) s k) (hT : T.IsLegal p e) :
    (∀ l r : Fin d, placePar p d lo hhi pk T l r = .none ↔
        placeWire p d lo hhi w T l r = none) ∧
    (∀ l r : Fin d, l.1 < r.1 →
        (placePar p d lo hhi pk T l r = .none ↔ placeSplit d lo hhi T l r = none)) ∧
    (∀ l r : Fin d, ¬ (l.1 < r.1) → placeSplit d lo hhi T l r = none) ∧
    (∀ l r : Fin d, l.1 < r.1 →
        (placePar p d lo hhi pk T l r = .none ↔ placeGate d lo hhi T l r = none)) ∧
    (∀ l r : Fin d, ¬ (l.1 < r.1) → placeGate d lo hhi T l r = none) ∧
    (∀ l : Fin d, placePar p d lo hhi pk T l l = .none ↔ placeLeaf d lo hhi T l = none) ∧
    (∀ l r : Fin d, r.1 < l.1 → placePar p d lo hhi pk T l r = .none) ∧
    (∀ l r r' : Fin d, placePar p d lo hhi pk T l r = .leftOf r' → r.1 < r'.1) ∧
    (∀ l r l' : Fin d, placePar p d lo hhi pk T l r = .rightOf l' → l'.1 < l.1) ∧
    (∀ l r q : Fin d, placeSplit d lo hhi T l r = some q → l.1 ≤ q.1 ∧ q.1 < r.1) ∧
    (∀ l r q : Fin d, l.1 ≤ q.1 → q.1 < r.1 →
        ((r.1 ≤ lo + k ∨ pk ≠ .leftOf r) →
          (placeSplit d lo hhi T l r = some q ↔
            placePar p d lo hhi pk T l q = .leftOf r)) ∧
        ((lo ≤ l.1 ∨ pk ≠ .rightOf l) → ∀ hq : q.1 < r.1,
          placeSplit d lo hhi T l r = some q ↔
            placePar p d lo hhi pk T ⟨q.1 + 1, by omega⟩ r = .rightOf l)) ∧
    (∀ l r : Fin d, ∀ g : Fin s, placeGate d lo hhi T l r = some g → isMulGate p g = true) ∧
    (∀ l r q : Fin d, ∀ g : Fin s, l.1 ≤ q.1 → q.1 < r.1 →
        placeSplit d lo hhi T l r = some q → placeGate d lo hhi T l r = some g →
        placeWire p d lo hhi w T l q = mulLeftWire p g ∧
        ∀ hq : q.1 < r.1,
          placeWire p d lo hhi w T ⟨q.1 + 1, by omega⟩ r = mulRightWire p g) ∧
    (∀ l : Fin d, ∀ b : Fin m, placeLeaf d lo hhi T l = some (Fin.natAdd n b) → e b = true) := by
  induction T generalizing lo pk w with
  | leaf j =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro l r; simp only [placePar, placeWire]; split_ifs <;> simp [hpk]
      · intro l r hlr; simp only [placePar, placeSplit]; split_ifs <;> [omega; simp]
      · intro l r _; rfl
      · intro l r hlr; simp only [placePar, placeGate]; split_ifs <;> [omega; simp]
      · intro l r _; rfl
      · intro l; simp only [placePar, placeLeaf]; split_ifs <;> simp_all
      · intro l r hrl; simp only [placePar]; split_ifs <;> [omega; rfl]
      · intro l r r' hp
        simp only [placePar] at hp; split_ifs at hp with h
        exact h.2 ▸ hpk_l r' hp
      · intro l r l' hp
        simp only [placePar] at hp; split_ifs at hp with h
        exact h.1 ▸ hpk_r l' hp
      · intro l r q hs; simp at hs
      · intro l r q h1 h2
        refine ⟨fun hguard => ?_, fun hguard _ => ?_⟩
        · simp only [placeSplit, placePar, reduceCtorEq, false_iff]
          split_ifs with h
          · intro hp
            have hlt := hpk_l r hp
            rcases hguard with hle | hne
            · omega
            · exact hne hp
          · simp
        · simp only [placeSplit, placePar, reduceCtorEq, false_iff]
          split_ifs with h
          · intro hp
            have hlt := hpk_r l hp
            rcases hguard with hle | hne
            · omega
            · exact hne hp
          · simp
      · intro l r g hg; simp at hg
      · intro l r q g _ _ hs _; simp at hs
      · intro l b hl
        simp only [placeLeaf] at hl; split_ifs at hl
        injection hl with hj; exact hT b hj
  | @node g k' a L R ihL ihR =>
      obtain ⟨hgmul, hL, hR⟩ := hT
      cases hmw : mulWires (p.lines g) with
      | none => rw [isMulGate_eq_isSome, hmw] at hgmul; simp at hgmul
      | some uv =>
          have hu : mulLeftWire p g = some uv.1 := by rw [mulLeftWire_eq_map, hmw]; rfl
          have hv : mulRightWire p g = some uv.2 := by rw [mulRightWire_eq_map, hmw]; rfl
          have hIHL := ihL (lo := lo) (by omega) (.leftOf ⟨lo + k' + 1, by omega⟩) (by simp)
            (fun r' h => by injection h with h'; subst h'; dsimp; omega)
            (fun _ h => by cases h) uv.1 hL
          have hIHR := ihR (lo := lo + a.1 + 1) (by omega) (.rightOf ⟨lo, by omega⟩) (by simp)
            (fun _ h => by cases h)
            (fun l' h => by injection h with h'; subst h'; dsimp; omega) uv.2 hR
          obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14⟩ := hIHL
          obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14⟩ := hIHR
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro l r
            simp only [placePar, placeWire, hu, hv]
            split_ifs <;> [simp [hpk]; exact l1 l r; exact r1 l r; simp]
          · intro l r hlr
            simp only [placePar, placeSplit]
            split_ifs <;> [simp [hpk]; exact l2 l r hlr; exact r2 l r hlr; simp]
          · intro l r hlr
            simp only [placeSplit]
            split_ifs with h1 h2 h3
            · omega
            · exact l3 l r hlr
            · exact r3 l r hlr
            · rfl
          · intro l r hlr
            simp only [placePar, placeGate]
            split_ifs <;> [simp [hpk]; exact l4 l r hlr; exact r4 l r hlr; simp]
          · intro l r hlr
            simp only [placeGate]
            split_ifs with h1 h2 h3
            · omega
            · exact l5 l r hlr
            · exact r5 l r hlr
            · rfl
          · intro l
            have hnt : ¬ (l.1 = lo ∧ l.1 = lo + k' + 1) := by omega
            by_cases hle : l.1 ≤ lo + a.1
            · simp only [placePar, placeLeaf, hnt, hle, ↓reduceIte]
              exact l6 l
            · simp only [placePar, placeLeaf, hnt, hle, show lo + a.1 + 1 ≤ l.1 by omega,
                ↓reduceIte]
              exact r6 l
          · intro l r hrl
            simp only [placePar]
            split_ifs with h1 h2 h3
            · omega
            · exact l7 l r hrl
            · exact r7 l r hrl
            · rfl
          · intro l r r' hp
            simp only [placePar] at hp
            split_ifs at hp with h1 h2 h3
            · exact h1.2 ▸ hpk_l r' hp
            · exact l8 l r r' hp
            · exact r8 l r r' hp
          · intro l r l' hp
            simp only [placePar] at hp
            split_ifs at hp with h1 h2 h3
            · exact h1.1 ▸ hpk_r l' hp
            · exact l9 l r l' hp
            · exact r9 l r l' hp
          · intro l r q hs
            simp only [placeSplit] at hs
            split_ifs at hs with h1 h2 h3
            · injection hs with hq; subst hq; dsimp; omega
            · exact l10 l r q hs
            · exact r10 l r q hs
          · intro l r q h1 h2
            constructor
            · intro hguard
              by_cases htop : l.1 = lo ∧ r.1 = lo + k' + 1
              · simp only [placeSplit, htop, and_self, ↓reduceIte, Option.some.injEq]
                have hq_not_top : ¬ (l.1 = lo ∧ q.1 = lo + k' + 1) := by omega
                simp only [placePar, hq_not_top, ↓reduceIte]
                by_cases hqa : q.1 ≤ lo + a.1
                · rw [ite_eq_left hqa]
                  by_cases hqeq : q.1 = lo + a.1
                  · have hqfin : (⟨lo + a.1, by omega⟩ : Fin d) = q := Fin.ext hqeq.symm
                    rw [hqfin, eq_self, true_iff]
                    rw [placePar_self p (by omega) _ L l q htop.1 hqeq]
                    congr 1; exact Fin.ext htop.2.symm
                  · have hqne : (⟨lo + a.1, by omega⟩ : Fin d) ≠ q := fun h =>
                      hqeq (congrArg Fin.val h).symm
                    rw [iff_false_left hqne]
                    intro hp
                    rcases placePar_leftOf_bound p (by omega) _ L l q r hp with
                      ⟨_, hq', _⟩ | ⟨_, hr'⟩
                    · exact hqeq hq'
                    · omega
                · rw [ite_eq_right hqa]
                  have hqne : (⟨lo + a.1, by omega⟩ : Fin d) ≠ q := fun h =>
                    hqa (by rw [← congrArg Fin.val h])
                  rw [iff_false_left hqne]
                  split_ifs with h3
                  · omega
                  · simp
              · simp only [placeSplit, htop, ↓reduceIte]
                by_cases hr1 : r.1 ≤ lo + a.1
                · rw [ite_eq_left hr1]
                  have hq1 : q.1 ≤ lo + a.1 := by omega
                  have hnt : ¬ (l.1 = lo ∧ q.1 = lo + k' + 1) := by omega
                  simp only [placePar, hnt, hq1, ↓reduceIte]
                  exact (l11 l r q h1 h2).1 (Or.inl hr1)
                · rw [ite_eq_right hr1]
                  by_cases hl1 : lo + a.1 + 1 ≤ l.1
                  · rw [ite_eq_left hl1]
                    have hq1 : ¬ (q.1 ≤ lo + a.1) := by omega
                    have hnt : ¬ (l.1 = lo ∧ q.1 = lo + k' + 1) := by omega
                    simp only [placePar, hnt, hq1, hl1, ↓reduceIte]
                    exact (r11 l r q h1 h2).1 (Or.inr (by simp))
                  · rw [ite_eq_right hl1]
                    simp only [reduceCtorEq, false_iff, placePar]
                    split_ifs with ha1 ha2
                    · intro hp
                      have hlt := hpk_l r hp
                      rcases hguard with hle | hne
                      · omega
                      · exact hne hp
                    · intro hp
                      rcases placePar_leftOf_bound p (by omega) _ L l q r hp with
                        ⟨hleq, _, heq⟩ | ⟨_, hr'⟩
                      · injection heq with hreq
                        exact htop ⟨hleq, by rw [← hreq]⟩
                      · omega
                    · simp
            · intro hguard hq
              by_cases htop : l.1 = lo ∧ r.1 = lo + k' + 1
              · simp only [placeSplit, htop, and_self, ↓reduceIte, Option.some.injEq]
                have hq_not_top : ¬ (q.1 + 1 = lo ∧ r.1 = lo + k' + 1) := by omega
                have hnotr : ¬ (r.1 ≤ lo + a.1) := by omega
                simp only [placePar, hq_not_top, hnotr, ↓reduceIte]
                by_cases hqa : lo + a.1 + 1 ≤ q.1 + 1
                · rw [ite_eq_left hqa]
                  by_cases hqeq : q.1 = lo + a.1
                  · have hqfin : (⟨lo + a.1, by omega⟩ : Fin d) = q := Fin.ext hqeq.symm
                    rw [hqfin, eq_self, true_iff]
                    rw [placePar_self p (by omega) _ R ⟨q.1 + 1, by omega⟩ r (by dsimp; omega)
                      (by omega)]
                    congr 1; exact Fin.ext htop.1.symm
                  · have hqne : (⟨lo + a.1, by omega⟩ : Fin d) ≠ q := fun h =>
                      hqeq (congrArg Fin.val h).symm
                    rw [iff_false_left hqne]
                    intro hp
                    rcases placePar_rightOf_bound p (by omega) _ R ⟨q.1 + 1, by omega⟩ r l hp with
                      ⟨hq', _, _⟩ | ⟨hl', _⟩
                    · dsimp at hq'; omega
                    · omega
                · rw [ite_eq_right hqa]
                  have hqne : (⟨lo + a.1, by omega⟩ : Fin d) ≠ q := fun h =>
                    hqa (by rw [← congrArg Fin.val h])
                  simp [hqne]
              · simp only [placeSplit, htop, ↓reduceIte]
                by_cases hr1 : r.1 ≤ lo + a.1
                · rw [ite_eq_left hr1]
                  have hnt : ¬ (q.1 + 1 = lo ∧ r.1 = lo + k' + 1) := by omega
                  simp only [placePar, hnt, hr1, ↓reduceIte]
                  exact (l11 l r q h1 h2).2 (Or.inr (by simp)) hq
                · rw [ite_eq_right hr1]
                  by_cases hl1 : lo + a.1 + 1 ≤ l.1
                  · rw [ite_eq_left hl1]
                    have hnt : ¬ (q.1 + 1 = lo ∧ r.1 = lo + k' + 1) := by omega
                    have hq1 : lo + a.1 + 1 ≤ q.1 + 1 := by omega
                    simp only [placePar, hnt, hr1, hq1, ↓reduceIte]
                    exact (r11 l r q h1 h2).2 (Or.inl hl1) hq
                  · rw [ite_eq_right hl1]
                    simp only [reduceCtorEq, false_iff, placePar]
                    split_ifs with ha1 ha2
                    · intro hp
                      have hlt := hpk_r l hp
                      rcases hguard with hle | hne
                      · omega
                      · exact hne hp
                    · intro hp
                      rcases placePar_rightOf_bound p (by omega) _ R ⟨q.1 + 1, by omega⟩ r l hp with
                        ⟨_, hreq, heq⟩ | ⟨hl', _⟩
                      · injection heq with hleq
                        exact htop ⟨by rw [← hleq], by omega⟩
                      · omega
                    · simp
          · intro l r g' hg'
            simp only [placeGate] at hg'
            split_ifs at hg' with h1 h2 h3
            · injection hg' with h; subst h; exact hgmul
            · exact l12 l r g' hg'
            · exact r12 l r g' hg'
          · intro l r q g' h1 h2 hs hg'
            by_cases htop : l.1 = lo ∧ r.1 = lo + k' + 1
            · simp only [placeSplit, placeGate, htop, and_self, ↓reduceIte,
                Option.some.injEq] at hs hg'
              subst hg'
              have hqa : q.1 = lo + a.1 := by rw [← hs]
              constructor
              · have hnt : ¬ (l.1 = lo ∧ q.1 = lo + k' + 1) := by omega
                simp only [placeWire, hnt, show q.1 ≤ lo + a.1 by omega, ↓reduceIte, hu]
                exact placeWire_self p (by omega) uv.1 L l q htop.1 hqa
              · intro hq
                have hnt : ¬ (q.1 + 1 = lo ∧ r.1 = lo + k' + 1) := by omega
                simp only [placeWire, hnt, show ¬ (r.1 ≤ lo + a.1) by omega,
                  show lo + a.1 + 1 ≤ q.1 + 1 by omega, ↓reduceIte, hv]
                exact placeWire_self p (by omega) uv.2 R ⟨q.1 + 1, by omega⟩ r (by dsimp; omega)
                  (by omega)
            · simp only [placeSplit, placeGate, htop, ↓reduceIte] at hs hg'
              by_cases hr1 : r.1 ≤ lo + a.1
              · rw [ite_eq_left hr1] at hs hg'
                have hq1 : q.1 ≤ lo + a.1 := by omega
                have hntL : ¬ (l.1 = lo ∧ q.1 = lo + k' + 1) := by omega
                have hntR : ¬ (q.1 + 1 = lo ∧ r.1 = lo + k' + 1) := by omega
                simp only [placeWire, hntL, hntR, hq1, hr1, ↓reduceIte, hu]
                exact l13 l r q g' h1 h2 hs hg'
              · rw [ite_eq_right hr1] at hs hg'
                by_cases hl1 : lo + a.1 + 1 ≤ l.1
                · rw [ite_eq_left hl1] at hs hg'
                  have hq1 : ¬ (q.1 ≤ lo + a.1) := by omega
                  have hq2 : lo + a.1 + 1 ≤ q.1 + 1 := by omega
                  have hntL : ¬ (l.1 = lo ∧ q.1 = lo + k' + 1) := by omega
                  have hntR : ¬ (q.1 + 1 = lo ∧ r.1 = lo + k' + 1) := by omega
                  simp only [placeWire, hntL, hntR, hq1, hr1, hl1, hq2, ↓reduceIte, hv]
                  exact r13 l r q g' h1 h2 hs hg'
                · rw [ite_eq_right hl1] at hs; cases hs
          · intro l b hl
            simp only [placeLeaf] at hl
            split_ifs at hl
            · exact l14 l b hl
            · exact r14 l b hl

omit [CommSemiring K] in
/-- Every legal `PTree` embeds into a semantically valid interval-tree assignment. -/
public theorem isValidAssign_assignOfPTree (p : Program (arithSignature K) (n + m) s)
    (v_out : Wire (n + m) s) (e : Fin m → Bool) {k : ℕ} (hk : k < d) (T : PTree (n + m) s k)
    (hT : T.IsLegal p e) :
    IsValidAssign p v_out (assignOfPTree p v_out e hk T) := by
  have hinv := place_invariants p e (d := d) (lo := 0) (k := k) (by omega) .root (by simp)
    (fun _ h => by cases h) (fun _ h => by cases h) v_out T hT
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14⟩ := hinv
  have hno_root : ∀ {k' lo : ℕ} (hhi : lo + k' < d) (pk : ParKind d) (_ : pk ≠ .root)
      (T' : PTree (n + m) s k') (l r : Fin d), placePar p d lo hhi pk T' l r ≠ .root := by
    intro k' lo hhi pk hpk T'
    induction T' generalizing lo pk with
    | leaf j => intro l r; simp only [placePar]; split_ifs <;> simp [hpk]
    | node _ a L R ihL ihR =>
        intro l r; simp only [placePar]
        split_ifs
        · exact hpk
        · exact ihL _ _ (by simp) _ _
        · exact ihR _ _ (by simp) _ _
        · simp
  refine ⟨?_, ?_, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10,
    fun l r q h1 h2 => (i11 l r q h1 h2).1 (Or.inr (by simp)),
    fun l r q h2 h1 => (i11 l r q h1 h2).2 (Or.inr (by simp)) h2,
    i12, fun l r q g h1 h2 hs hg => (i13 l r q g h1 h2 hs hg).1,
    fun l r q g h2 h1 hs hg => (i13 l r q g h1 h2 hs hg).2 h2, i14⟩
  · intro l r
    simp only [assignOfPTree]
    cases T with
    | leaf j =>
        simp only [placePar]
        split_ifs with h
        · simp [h.1, h.2]
        · simp only [false_iff, not_and]
          intro h1 h2; exact h ⟨h1, by omega⟩
    | node g a L R =>
        simp only [placePar]
        split_ifs with h1 h2 h3
        · simp [h1.1, h1.2]
        · rw [iff_false_left (hno_root _ _ (by simp) L l r)]
          rintro ⟨hl, hr⟩; exact h1 ⟨hl, by omega⟩
        · rw [iff_false_left (hno_root _ _ (by simp) R l r)]
          rintro ⟨hl, hr⟩; exact h1 ⟨hl, by omega⟩
        · simp only [false_iff, not_and]
          intro hl hr; exact h1 ⟨hl, by omega⟩
  · intro l r hp
    simp only [assignOfPTree] at hp ⊢
    cases T with
    | leaf j =>
        simp only [placePar] at hp; split_ifs at hp with h
        simp [h]
    | node g a L R =>
        simp only [placePar] at hp
        split_ifs at hp with h1 h2 h3
        · simp [h1]
        · exact absurd hp (hno_root _ _ (by simp) L l r)
        · exact absurd hp (hno_root _ _ (by simp) R l r)

private theorem placeGate_of_r_lt_lo {d k lo : ℕ} (hhi : lo + k < d)
    (T : PTree (n + m) s k) (l r : Fin d) (hr : r.1 < lo) :
    placeGate d lo hhi T l r = none := by
  induction T generalizing lo with
  | leaf _ => rfl
  | node _ a L R ihL ihR =>
      simp only [placeGate]
      split_ifs with h1 h2 h3
      · omega
      · exact ihL _ (by omega)
      · exact ihR _ (by omega)
      · rfl

private theorem assignWeight_subtree (p : Program (arithSignature K) (n + m) s) (e : Fin m → Bool)
    {d k lo : ℕ} (hhi : lo + k < d) (w : Wire (n + m) s) (T : PTree (n + m) s k)
    (hT : T.IsLegal p e) :
    (∏ l : Fin d, ∏ r : Fin d,
      match placeWire p d lo hhi w T l r, placeGate d lo hhi T l r with
      | some w', some g' => C (linCoeff p w' (.gate g'))
      | _, _ => 1) *
    (∏ l : Fin d,
      match placeWire p d lo hhi w T l l, placeLeaf d lo hhi T l with
      | some w', some j' => C (linCoeff p w' (.input j'))
      | _, _ => 1) *
    (∏ l : Fin d,
      match placeLeaf d lo hhi T l with
      | some j' => varVal e j'
      | none => 1) =
    T.eval p e w := by
  induction T generalizing lo w with
  | leaf j =>
      have h1 : (∏ l : Fin d, ∏ r : Fin d,
          match placeWire p d lo hhi w (.leaf j) l r, placeGate d lo hhi (.leaf j) l r with
          | some w', some g' => (C (linCoeff p w' (.gate g')) : MvPolynomial (Fin n) K)
          | _, _ => (1 : MvPolynomial (Fin n) K)) = 1 :=
        Finset.prod_eq_one fun l _ => Finset.prod_eq_one fun r _ => by
          cases placeWire p d lo hhi w (.leaf j) l r <;> rfl
      let loF : Fin d := ⟨lo, by omega⟩
      have h2 : (∏ l : Fin d,
          match placeWire p d lo hhi w (.leaf j) l l,
            placeLeaf (s := s) d lo hhi (.leaf j) l with
          | some w', some j' => (C (linCoeff p w' (.input j')) : MvPolynomial (Fin n) K)
          | _, _ => (1 : MvPolynomial (Fin n) K)) =
          (C (linCoeff p w (.input j)) : MvPolynomial (Fin n) K) := by
        rw [Finset.prod_eq_single loF]
        · simp [loF]
        · intro l _ hne
          have : l.1 ≠ lo := fun h => hne (Fin.ext h)
          simp [this]
        · intro h; exact absurd (Finset.mem_univ loF) h
      have h3 : (∏ l : Fin d,
          match placeLeaf (s := s) d lo hhi (.leaf j) l with
          | some j' => (varVal e j' : MvPolynomial (Fin n) K)
          | none => (1 : MvPolynomial (Fin n) K)) =
          (varVal e j : MvPolynomial (Fin n) K) := by
        rw [Finset.prod_eq_single loF]
        · simp [loF]
        · intro l _ hne
          have : l.1 ≠ lo := fun h => hne (Fin.ext h)
          simp [this]
        · intro h; exact absurd (Finset.mem_univ loF) h
      rw [h1, h2, h3, one_mul, PTree.eval_leaf]
  | @node g k' a L R ihL ihR =>
      obtain ⟨hgmul, hL, hR⟩ := hT
      cases hmw : mulWires (p.lines g) with
      | none => rw [isMulGate_eq_isSome, hmw] at hgmul; simp at hgmul
      | some uv =>
          have hu : mulLeftWire p g = some uv.1 := by rw [mulLeftWire_eq_map, hmw]; rfl
          have hv : mulRightWire p g = some uv.2 := by rw [mulRightWire_eq_map, hmw]; rfl
          have hEval : (PTree.node g a L R).eval p e w =
              C (linCoeff p w (.gate g)) * L.eval p e uv.1 * R.eval p e uv.2 := by
            rw [PTree.eval_node, hmw]
          let loF : Fin d := ⟨lo, by omega⟩
          let hiF : Fin d := ⟨lo + k' + 1, by omega⟩
          have hP1 :
              (∏ l : Fin d, ∏ r : Fin d,
                match placeWire p d lo hhi w (.node g a L R) l r,
                  placeGate d lo hhi (.node g a L R) l r with
                | some w', some g' => (C (linCoeff p w' (.gate g')) : MvPolynomial (Fin n) K)
                | _, _ => (1 : MvPolynomial (Fin n) K)) =
              (C (linCoeff p w (.gate g)) : MvPolynomial (Fin n) K) *
                (∏ l : Fin d, ∏ r : Fin d,
                  match placeWire p d lo (by omega) uv.1 L l r, placeGate d lo (by omega) L l r with
                  | some w', some g' => (C (linCoeff p w' (.gate g')) : MvPolynomial (Fin n) K)
                  | _, _ => (1 : MvPolynomial (Fin n) K)) *
                (∏ l : Fin d, ∏ r : Fin d,
                  match placeWire p d (lo + a.1 + 1) (by omega) uv.2 R l r,
                    placeGate d (lo + a.1 + 1) (by omega) R l r with
                  | some w', some g' => (C (linCoeff p w' (.gate g')) : MvPolynomial (Fin n) K)
                  | _, _ => (1 : MvPolynomial (Fin n) K)) := by
            have htop_prod :
                (∏ l : Fin d, ∏ r : Fin d,
                  if l = loF ∧ r = hiF then (C (linCoeff p w (.gate g)) : MvPolynomial (Fin n) K)
                  else 1) =
                (C (linCoeff p w (.gate g)) : MvPolynomial (Fin n) K) := by
              rw [Finset.prod_eq_single loF]
              · rw [Finset.prod_eq_single hiF]
                · simp
                · intro r _ hne; simp [hne]
                · intro h; exact absurd (Finset.mem_univ hiF) h
              · intro l _ hne; exact Finset.prod_eq_one fun r _ => by simp [hne]
              · intro h; exact absurd (Finset.mem_univ loF) h
            rw [← htop_prod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
            refine Finset.prod_congr rfl fun l _ => ?_
            rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
            refine Finset.prod_congr rfl fun r _ => ?_
            simp only [placeWire, placeGate, hu, hv]
            by_cases h1 : l.1 = lo ∧ r.1 = lo + k' + 1
            · have heq : l = loF ∧ r = hiF := ⟨Fin.ext h1.1, Fin.ext h1.2⟩
              rw [ite_eq_left h1, ite_eq_left h1, ite_eq_left heq]
              rw [placeGate_outside (lo := lo) (k := a.1) (by omega) L l r (Or.inr (by omega))]
              rw [placeGate_outside (lo := lo + a.1 + 1) (k := k' - a.1) (by omega) R l r
                (Or.inl (by omega))]
              simp
            · have hne : ¬ (l = loF ∧ r = hiF) := by
                rintro ⟨rfl, rfl⟩; exact h1 ⟨rfl, rfl⟩
              rw [ite_eq_right h1, ite_eq_right h1, ite_eq_right hne, one_mul]
              by_cases h2 : r.1 ≤ lo + a.1
              · rw [ite_eq_left h2, ite_eq_left h2]
                rw [placeGate_of_r_lt_lo (lo := lo + a.1 + 1) (k := k' - a.1) (by omega) R l r
                  (by omega)]
                simp
              · rw [ite_eq_right h2, ite_eq_right h2]
                rw [placeGate_outside (lo := lo) (k := a.1) (by omega) L l r (Or.inr (by omega))]
                by_cases h3 : lo + a.1 + 1 ≤ l.1
                · rw [ite_eq_left h3, ite_eq_left h3]; simp
                · rw [ite_eq_right h3, ite_eq_right h3]
                  rw [placeGate_outside (lo := lo + a.1 + 1) (k := k' - a.1) (by omega) R l r
                    (Or.inl (by omega))]
                  simp
          have hP2 :
              (∏ l : Fin d,
                match placeWire p d lo hhi w (.node g a L R) l l,
                  placeLeaf (s := s) d lo hhi (.node g a L R) l with
                | some w', some j' => (C (linCoeff p w' (.input j')) : MvPolynomial (Fin n) K)
                | _, _ => (1 : MvPolynomial (Fin n) K)) =
              (∏ l : Fin d,
                match placeWire p d lo (by omega) uv.1 L l l,
                  placeLeaf (s := s) d lo (by omega) L l with
                | some w', some j' => (C (linCoeff p w' (.input j')) : MvPolynomial (Fin n) K)
                | _, _ => (1 : MvPolynomial (Fin n) K)) *
              (∏ l : Fin d,
                match placeWire p d (lo + a.1 + 1) (by omega) uv.2 R l l,
                  placeLeaf (s := s) d (lo + a.1 + 1) (by omega) R l with
                | some w', some j' => (C (linCoeff p w' (.input j')) : MvPolynomial (Fin n) K)
                | _, _ => (1 : MvPolynomial (Fin n) K)) := by
            rw [← Finset.prod_mul_distrib]
            refine Finset.prod_congr rfl fun l _ => ?_
            have hnt : ¬ (l.1 = lo ∧ l.1 = lo + k' + 1) := by omega
            simp only [placeWire, placeLeaf, hnt, ↓reduceIte, hu, hv]
            by_cases h2 : l.1 ≤ lo + a.1
            · rw [ite_eq_left h2, ite_eq_left h2]
              rw [placeLeaf_outside (lo := lo + a.1 + 1) (k := k' - a.1) (by omega) R l
                (Or.inl (by omega))]
              simp
            · rw [ite_eq_right h2, ite_eq_right h2, ite_eq_left (by omega)]
              rw [placeLeaf_outside (lo := lo) (k := a.1) (by omega) L l (Or.inr (by omega))]
              simp
          have hP3 :
              (∏ l : Fin d,
                match placeLeaf (s := s) d lo hhi (.node g a L R) l with
                | some j' => (varVal e j' : MvPolynomial (Fin n) K)
                | none => (1 : MvPolynomial (Fin n) K)) =
              (∏ l : Fin d,
                match placeLeaf (s := s) d lo (by omega) L l with
                | some j' => (varVal e j' : MvPolynomial (Fin n) K)
                | none => (1 : MvPolynomial (Fin n) K)) *
              (∏ l : Fin d,
                match placeLeaf (s := s) d (lo + a.1 + 1) (by omega) R l with
                | some j' => (varVal e j' : MvPolynomial (Fin n) K)
                | none => (1 : MvPolynomial (Fin n) K)) := by
            rw [← Finset.prod_mul_distrib]
            refine Finset.prod_congr rfl fun l _ => ?_
            simp only [placeLeaf]
            by_cases h2 : l.1 ≤ lo + a.1
            · rw [ite_eq_left h2]
              rw [placeLeaf_outside (lo := lo + a.1 + 1) (k := k' - a.1) (by omega) R l
                (Or.inl (by omega))]
              simp
            · rw [ite_eq_right h2]
              rw [placeLeaf_outside (lo := lo) (k := a.1) (by omega) L l (Or.inr (by omega))]
              simp
          rw [hP1, hP2, hP3, hEval,
            ← ihL (lo := lo) (by omega) uv.1 hL,
            ← ihR (lo := lo + a.1 + 1) (by omega) uv.2 hR]
          ring

/-- The weight of `assignOfPTree e hk T` equals `T.eval p e v_out`. -/
public theorem assignWeight_assignOfPTree (p : Program (arithSignature K) (n + m) s)
    (v_out : Wire (n + m) s) (e : Fin m → Bool) {k : ℕ} (hk : k < d) (T : PTree (n + m) s k)
    (hT : T.IsLegal p e) :
    assignWeight p v_out (assignOfPTree p v_out e hk T) = T.eval p e v_out := by
  rw [assignWeight_eq_prod]
  have hne0 : (assignOfPTree p v_out e hk T .rootDeg) ≠ 0 := by
    simp [Fin.ext_iff]
  rw [ite_eq_right hne0, one_mul]
  refine Eq.trans ?_ (assignWeight_subtree p e (d := d) (lo := 0) (by omega) v_out T hT)
  simp only [assignOfPTree]
  congr 1
  · congr 1
    · refine Finset.prod_congr rfl fun l _ => Finset.prod_congr rfl fun r _ => ?_
      cases placeWire p d 0 (by omega) v_out T l r <;> cases placeGate d 0 (by omega) T l r <;> rfl
    · refine Finset.prod_congr rfl fun l _ => ?_
      cases placeWire p d 0 (by omega) v_out T l l <;> cases placeLeaf d 0 (by omega) T l <;> rfl
  · refine Finset.prod_congr rfl fun l _ => ?_
    cases placeLeaf d 0 (by omega) T l <;> rfl

end TreePlace

end CslibFrontier.Computability.Circuit.Arithmetic.Permanent
