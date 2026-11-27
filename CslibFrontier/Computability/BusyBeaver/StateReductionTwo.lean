/-
Copyright (c) 2026 Cslib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers contributors
-/

module

public import CslibFrontier.Computability.BusyBeaver.TuringMachine

/-!
# Shannon Universal Two-State Reduction for Bi-Infinite Turing Machines

Simulates any blank-tape halting bi-infinite Turing machine with `n` states and `m` symbols using
only `2` control states: over `5 * m * (n + 1)` symbols when one initial non-blank cell is allowed,
and over `5 * m * (n + 2)` symbols starting on the all-blank tape via counter overflow
bootstrapping, yielding `busyBeaver n m ≤ busyBeaver 2 (5 * m * (n + 2))` for all `n, m ≥ 1`.
-/

public section

namespace CslibFrontier.Computability.BusyBeaver

section Alphabet

/-- Five cell-role tags used by the 2-state simulator: blank (`-`), newly activated
neighbor cells (`Lnew`, `Rnew`), and previous cells transferring a state counter (`Lold`, `Rold`).
-/
inductive Role5 : Type
  | blank | Lnew | Lold | Rnew | Rold
  deriving DecidableEq

/-- Default `Role5` tag is `.blank` (`-`). -/
instance instInhabitedRole5 : Inhabited Role5 := ⟨.blank⟩

@[simp] theorem default_role5 : (default : Role5) = .blank := rfl

/-- Finite enumeration of all `5` values of `Role5`. -/
instance instFintypeRole5 : Fintype Role5 where
  elems := {.blank, .Lnew, .Lold, .Rnew, .Rold}
  complete r := by cases r <;> simp

/-- `Role5` has cardinality `5`. -/
@[simp] theorem card_role5 : Fintype.card Role5 = 5 := rfl

/-- Tape alphabet for the 2-state non-blank-start simulator:
`Fin (n + 1) × Role5 × E`, of cardinality `5 * Fintype.card E * (n + 1)`. -/
abbrev Sym2NB (n : ℕ) (E : Type*) : Type _ := Fin (n + 1) × Role5 × E

/-- Definition of `Sym2NB`. -/
theorem sym2NB_def (n : ℕ) (E : Type*) : Sym2NB n E = (Fin (n + 1) × Role5 × E) := rfl

/-- Cardinality of `Sym2NB n E` is `5 * Fintype.card E * (n + 1)`. -/
theorem card_sym2NB (n : ℕ) (E : Type*) [Fintype E] :
    Fintype.card (Sym2NB n E) = 5 * Fintype.card E * (n + 1) := by
  simp only [Fintype.card_prod, Fintype.card_fin, card_role5]; ac_rfl

/-- Tape alphabet for the 2-state all-blank-start simulator:
`Fin (n + 2) × Role5 × E`, of cardinality `5 * Fintype.card E * (n + 2)`. -/
abbrev Sym2B (n : ℕ) (E : Type*) : Type _ := Fin (n + 2) × Role5 × E

/-- Definition of `Sym2B`. -/
theorem sym2B_def (n : ℕ) (E : Type*) : Sym2B n E = (Fin (n + 2) × Role5 × E) := rfl

/-- Cardinality of `Sym2B n E` is `5 * Fintype.card E * (n + 2)`. -/
theorem card_sym2B (n : ℕ) (E : Type*) [Fintype E] :
    Fintype.card (Sym2B n E) = 5 * Fintype.card E * (n + 2) := by
  simp only [Fintype.card_prod, Fintype.card_fin, card_role5]; ac_rfl

private def otherDir : Turing.Dir → Turing.Dir | .left => .right | .right => .left
@[simp] private lemma otherDir_otherDir (d : Turing.Dir) : otherDir (otherDir d) = d := by
  cases d <;> rfl
private lemma otherDir_ne (d : Turing.Dir) : otherDir d ≠ d := by cases d <;> decide

private def roleNew : Turing.Dir → Role5 | .left => .Lnew | .right => .Rnew
private def roleOld : Turing.Dir → Role5 | .left => .Lold | .right => .Rold
private lemma roleNew_inj {d₁ d₂ : Turing.Dir} : roleNew d₁ = roleNew d₂ ↔ d₁ = d₂ := by
  cases d₁ <;> cases d₂ <;> simp [roleNew]
private lemma roleNew_ne_blank (d : Turing.Dir) : roleNew d ≠ .blank := by cases d <;> decide
private lemma roleOld_ne_blank (d : Turing.Dir) : roleOld d ≠ .blank := by cases d <;> decide
private lemma roleNew_ne_roleOld (d₁ d₂ : Turing.Dir) : roleNew d₁ ≠ roleOld d₂ := by
  cases d₁ <;> cases d₂ <;> decide

private def dirStep : Turing.Dir → ℤ | .left => -1 | .right => 1
@[simp] private lemma dirStep_otherDir (d : Turing.Dir) : dirStep (otherDir d) = -dirStep d := by
  cases d <;> rfl
private lemma dirStep_ne_zero (d : Turing.Dir) : dirStep d ≠ 0 := by cases d <;> decide
private lemma zero_ne_neg_dirStep (d : Turing.Dir) : (0 : ℤ) ≠ -dirStep d := by
  cases d <;> decide
private lemma dirStep_ne_neg_self (d : Turing.Dir) : dirStep d ≠ -dirStep d := by
  cases d <;> decide


private lemma tape_move_nth {Γ : Type*} [Inhabited Γ] (T : Turing.Tape Γ) (d : Turing.Dir)
    (i : ℤ) : (T.move d).nth i = T.nth (i + dirStep d) := by
  cases d with
  | left => simp [dirStep, sub_eq_add_neg]
  | right => simp [dirStep]

private lemma tape_write_move_nth {Γ : Type*} [Inhabited Γ] (T : Turing.Tape Γ) (a : Γ)
    (d : Turing.Dir) (i : ℤ) :
    ((T.write a).move d).nth i = if i = -dirStep d then a else T.nth (i + dirStep d) := by
  rw [tape_move_nth, Turing.Tape.write_nth]
  by_cases hi : i = -dirStep d
  · subst hi; simp
  · have hne : i + dirStep d ≠ 0 := fun h ↦ hi (by omega)
    simp [hi, hne]

private lemma tape_round_trip_nth {Γ : Type*} [Inhabited Γ] (T : Turing.Tape Γ) (a b : Γ)
    (d : Turing.Dir) :
    let S := (((T.write a).move d).write b).move (otherDir d)
    S.nth 0 = a ∧ S.nth (dirStep d) = b ∧
      (∀ i : ℤ, i ≠ 0 → i ≠ dirStep d → S.nth i = T.nth i) := by
  refine ⟨?_, ?_, fun i hi0 hid ↦ ?_⟩
  · rw [tape_write_move_nth, dirStep_otherDir, neg_neg,
      ite_eq_right_iff.mpr (fun h ↦ absurd h.symm (dirStep_ne_zero d)), zero_add,
      tape_write_move_nth]; simp
  · rw [tape_write_move_nth, dirStep_otherDir, neg_neg]; simp
  · rw [tape_write_move_nth, dirStep_otherDir, neg_neg,
      ite_eq_right_iff.mpr (fun h ↦ absurd h hid), tape_write_move_nth,
      ite_eq_right_iff.mpr (fun h ↦ absurd (by omega : i = 0) hi0),
      show i + -dirStep d + dirStep d = i by omega]

private lemma tape_step_nth {Γ : Type*} [Inhabited Γ] (T : Turing.Tape Γ) (e' : Γ)
    (d' : Turing.Dir) :
    ((T.write e').move d').nth 0 = T.nth (dirStep d') ∧
    ((T.write e').move d').nth (-dirStep d') = e' ∧
    ∀ i : ℤ, i ≠ -dirStep d' → ((T.write e').move d').nth i = T.nth (i + dirStep d') := by
  refine ⟨?_, ?_, fun i hi ↦ ?_⟩
  · rw [tape_write_move_nth]; simp [zero_ne_neg_dirStep d']
  · rw [tape_write_move_nth]; simp
  · rw [tape_write_move_nth]; simp [hi]

private lemma tape_mk_single_nth {Γ : Type*} [Inhabited Γ] (a : Γ) {i : ℤ} (hi : i ≠ 0) :
    (Turing.Tape.mk a default default).nth i = default := by
  cases i with
  | ofNat k => cases k with
    | zero => exact absurd rfl hi
    | succ k => change (Turing.ListBlank.mk ([] : List Γ)).nth k = default; simp
  | negSucc k => change (Turing.ListBlank.mk ([] : List Γ)).nth k = default; simp

private lemma tape_nth_default {Γ : Type*} [Inhabited Γ] (i : ℤ) :
    (default : Turing.Tape Γ).nth i = default := by
  by_cases hi : i = 0
  · subst hi; rfl
  · exact tape_mk_single_nth default hi

end Alphabet

section SharedTransitions

private noncomputable def canonInitEquiv {Q : Type*} [Fintype Q] (q₀ : Q) :
    Q ≃ Fin (Fintype.card Q) := by
  classical
  have hpos : 0 < Fintype.card Q := Fintype.card_pos_iff.mpr ⟨q₀⟩
  let e₀ : Q ≃ Fin (Fintype.card Q) := (Fintype.truncEquivFin Q).out
  exact e₀.trans (Equiv.swap (e₀ q₀) ⟨0, hpos⟩)

private lemma canonInitEquiv_self {Q : Type*} [Fintype Q] (q₀ : Q) :
    (canonInitEquiv q₀ q₀).1 = 0 := by
  classical
  have hpos : 0 < Fintype.card Q := Fintype.card_pos_iff.mpr ⟨q₀⟩
  change (Equiv.swap ((Fintype.truncEquivFin Q).out q₀) ⟨0, hpos⟩
    ((Fintype.truncEquivFin Q).out q₀)).1 = 0
  rw [Equiv.swap_apply_left]

private noncomputable def transTwoAux {Q E : Type*} [Fintype Q] [Inhabited E]
    (M : BiInfTM Q E) (eQ : Q ≃ Fin (Fintype.card Q)) {N : ℕ} (hN : Fintype.card Q ≤ N)
    (extra : Turing.Dir → Fin (N + 1) × Role5 × E →
      Option Turing.Dir × (Fin (N + 1) × Role5 × E) × Turing.Dir)
    (q : Turing.Dir) (sym : Fin (N + 1) × Role5 × E) :
    Option Turing.Dir × (Fin (N + 1) × Role5 × E) × Turing.Dir :=
  let n := Fintype.card Q
  have hn : 0 < n := Fintype.card_pos_iff.mpr ⟨M.initState⟩
  let c := sym.1.1; let r := sym.2.1; let e := sym.2.2
  if c = 0 ∧ r = .blank then
    (some (otherDir q), (⟨1, by omega⟩, roleNew q, e), otherDir q)
  else if 1 ≤ c ∧ c ≤ n ∧ r = roleNew q then
    (some (otherDir q), (⟨min (c + 1) N, by omega⟩, roleNew q, e), otherDir q)
  else if 1 ≤ c ∧ c ≤ n ∧ r = roleOld (otherDir q) then
    (some (otherDir q), (⟨c - 1, by have := sym.1.2; omega⟩, roleOld (otherDir q), e), otherDir q)
  else if c = 0 ∧ r = roleOld (otherDir q) then
    (some q, (0, .blank, e), otherDir q)
  else if 1 ≤ c ∧ c ≤ n ∧ r = roleNew (otherDir q) then
    let s : Fin (Fintype.card Q) := ⟨min (c - 1) (n - 1), by omega⟩
    match M.trans (eQ.symm s) e with
    | (none, _, _) => (none, default, .right)
    | (some q', e', d') =>
      (some d', (⟨(eQ q').1, by have := (eQ q').2; omega⟩, roleOld d', e'), d')
  else extra q sym

section Rules

variable {Q E : Type*} [Fintype Q] [Inhabited E]
  (M : BiInfTM Q E) (eQ : Q ≃ Fin (Fintype.card Q)) {N : ℕ} (hN : Fintype.card Q ≤ N)
  (extra : Turing.Dir → Fin (N + 1) × Role5 × E →
    Option Turing.Dir × (Fin (N + 1) × Role5 × E) × Turing.Dir)

private lemma transTwoAux_rule1 (Y : Turing.Dir) (e : E) :
    transTwoAux M eQ hN extra Y (⟨0, Nat.zero_lt_succ _⟩, .blank, e) =
      (some (otherDir Y), (⟨1, by have := Fintype.card_pos_iff.mpr ⟨M.initState⟩; omega⟩,
        roleNew Y, e), otherDir Y) := by
  simp [transTwoAux]

private lemma transTwoAux_rule2 (Y : Turing.Dir) (j : ℕ) (hj1 : 1 ≤ j)
    (hjn : j ≤ Fintype.card Q) (hjN : j + 1 ≤ N) (e : E) :
    transTwoAux M eQ hN extra Y (⟨j, by omega⟩, roleNew Y, e) =
      (some (otherDir Y), (⟨j + 1, by omega⟩, roleNew Y, e), otherDir Y) := by
  dsimp only [transTwoAux]
  rw [ite_eq_right_iff.mpr (fun h ↦ absurd h.2 (roleNew_ne_blank Y)),
    ite_eq_left_iff.mpr (fun h ↦ absurd ⟨hj1, hjn, rfl⟩ h)]
  simp [min_eq_left hjN]

private lemma transTwoAux_rule3 (Y : Turing.Dir) (c : ℕ) (hcn : c + 1 < Fintype.card Q) (e : E) :
    transTwoAux M eQ hN extra Y (⟨c + 1, by omega⟩, roleOld (otherDir Y), e) =
      (some (otherDir Y), (⟨c, by omega⟩, roleOld (otherDir Y), e), otherDir Y) := by
  dsimp only [transTwoAux]
  rw [ite_eq_right_iff.mpr (fun h ↦ absurd h.2 (roleOld_ne_blank (otherDir Y))),
    ite_eq_right_iff.mpr (fun h ↦ absurd h.2.2.symm (roleNew_ne_roleOld Y (otherDir Y))),
    ite_eq_left_iff.mpr (fun h ↦ absurd ⟨Nat.succ_pos c, by omega, rfl⟩ h)]
  simp

private lemma transTwoAux_rule4 (Y : Turing.Dir) (e : E) :
    transTwoAux M eQ hN extra Y (⟨0, Nat.zero_lt_succ _⟩, roleOld (otherDir Y), e) =
      (some Y, (0, .blank, e), otherDir Y) := by
  dsimp only [transTwoAux]
  rw [ite_eq_right_iff.mpr (fun h ↦ absurd h.2 (roleOld_ne_blank (otherDir Y))),
    ite_eq_right_iff.mpr (fun h ↦ absurd h.1 (by omega)),
    ite_eq_right_iff.mpr (fun h ↦ absurd h.1 (by omega)),
    ite_eq_left_iff.mpr (fun h ↦ absurd ⟨rfl, rfl⟩ h)]

private lemma transTwoAux_rule5 (Y : Turing.Dir) (q : Q) (e : E) :
    transTwoAux M eQ hN extra Y
        (⟨(eQ q).1 + 1, by have := (eQ q).2; omega⟩, roleNew (otherDir Y), e) =
      match M.trans q e with
      | (none, _, _) => (none, default, .right)
      | (some q', e', d') =>
        (some d', (⟨(eQ q').1, by have := (eQ q').2; omega⟩, roleOld d', e'), d') := by
  dsimp only [transTwoAux]
  rw [ite_eq_right_iff.mpr (fun h ↦ absurd h.2 (roleNew_ne_blank (otherDir Y))),
    ite_eq_right_iff.mpr (fun h ↦ absurd (roleNew_inj.mp h.2.2) (otherDir_ne Y)),
    ite_eq_right_iff.mpr (fun h ↦ absurd h.2.2 (roleNew_ne_roleOld (otherDir Y) (otherDir Y))),
    ite_eq_right_iff.mpr (fun h ↦ absurd h.1 (Nat.succ_ne_zero _)),
    ite_eq_left_iff.mpr (fun h ↦ absurd ⟨Nat.succ_le_succ (Nat.zero_le _), (eQ q).2, rfl⟩ h)]
  have hs : (⟨min ((eQ q).1 + 1 - 1) (Fintype.card Q - 1), by
      have := (eQ q).2; omega⟩ : Fin (Fintype.card Q)) = eQ q := by
    ext; have := (eQ q).2; simp only [Nat.add_sub_cancel]; exact min_eq_left (by omega)
  rw [hs, eQ.symm_apply_apply]

private lemma transfer_loop (M' : BiInfTM Turing.Dir (Fin (N + 1) × Role5 × E))
    (hm' : M'.trans = transTwoAux M eQ hN extra) (d' : Turing.Dir) (e' e₂ : E) :
    ∀ (c j : ℕ) (hcj : c + j ≤ Fintype.card Q) (hj1 : 1 ≤ j)
      (T : Turing.Tape (Fin (N + 1) × Role5 × E)),
      T.nth 0 = (⟨c, by omega⟩, roleOld d', e') →
      T.nth (dirStep d') = (⟨j, by omega⟩, roleNew d', e₂) →
      ∃ T' : Turing.Tape (Fin (N + 1) × Role5 × E),
        M'.step^[2 * c] ⟨some (otherDir d'), T⟩ = ⟨some (otherDir d'), T'⟩ ∧
        T'.nth 0 = (⟨0, by omega⟩, roleOld d', e') ∧
        T'.nth (dirStep d') = (⟨c + j, by omega⟩, roleNew d', e₂) ∧
        (∀ i : ℤ, i ≠ 0 → i ≠ dirStep d' → T'.nth i = T.nth i)
  | 0, j, _, _, T, hT0, hTd => by
    refine ⟨T, rfl, hT0, ?_, fun _ _ _ ↦ rfl⟩
    simpa [Nat.zero_add] using hTd
  | c + 1, j, hcj, hj1, T, hT0, hTd => by
    have hhead0 : T.head = (⟨c + 1, by omega⟩, roleOld (otherDir (otherDir d')), e') := by
      simpa [Turing.Tape.nth_zero, otherDir_otherDir] using hT0
    have hstep1 : M'.step ⟨some (otherDir d'), T⟩ =
        ⟨some d', (T.write (⟨c, by omega⟩, roleOld d', e')).move d'⟩ := by
      rw [BiInfTM.step_some, hhead0, hm',
        transTwoAux_rule3 M eQ hN extra (otherDir d') c (by omega) e', otherDir_otherDir]
    set S₁ := (T.write (⟨c, by omega⟩, roleOld d', e')).move d'
    have hS₁0 : S₁.nth 0 = (⟨j, by omega⟩, roleNew d', e₂) := by
      rw [tape_write_move_nth]; simp [zero_ne_neg_dirStep d', hTd]
    have hstep2 : M'.step ⟨some d', S₁⟩ =
        ⟨some (otherDir d'),
          (S₁.write (⟨j + 1, by omega⟩, roleNew d', e₂)).move (otherDir d')⟩ := by
      rw [BiInfTM.step_some, show S₁.head = S₁.nth 0 from rfl, hS₁0, hm',
        transTwoAux_rule2 M eQ hN extra d' j hj1 (by omega) (by omega) e₂]
    set S₂ := (S₁.write (⟨j + 1, by omega⟩, roleNew d', e₂)).move (otherDir d')
    rcases tape_round_trip_nth T (⟨c, by omega⟩, roleOld d', e')
      (⟨j + 1, by omega⟩, roleNew d', e₂) d' with ⟨hS₂0, hS₂d, hS₂_other⟩
    obtain ⟨T', hT'steps, hT'0, hT'd, hT'other⟩ :=
      transfer_loop M' hm' d' e' e₂ c (j + 1) (by omega) (by omega) S₂ hS₂0 hS₂d
    have h2c : M'.step^[2 * (c + 1)] ⟨some (otherDir d'), T⟩ =
        M'.step^[2 * c] ⟨some (otherDir d'), S₂⟩ := by
      have h2_it : M'.step^[2] ⟨some (otherDir d'), T⟩ = ⟨some (otherDir d'), S₂⟩ := by
        change M'.step (M'.step ⟨some (otherDir d'), T⟩) = _; rw [hstep1, hstep2]
      rw [show 2 * (c + 1) = 2 * c + 2 by omega, Function.iterate_add_apply, h2_it]
    refine ⟨T', h2c.trans hT'steps, hT'0, ?_,
      fun i hi0 hid ↦ (hT'other i hi0 hid).trans (hS₂_other i hi0 hid)⟩
    simpa [Nat.add_assoc, Nat.add_comm 1 j] using hT'd

private lemma simulate_active_step (M' : BiInfTM Turing.Dir (Fin (N + 1) × Role5 × E))
    (hm' : M'.trans = transTwoAux M eQ hN extra)
    {Y d' : Turing.Dir} {e' e₂ : E} {c : ℕ} (hc : c < Fintype.card Q)
    {T : Turing.Tape (Fin (N + 1) × Role5 × E)}
    (ht5 : M'.trans Y (T.nth 0) = (some d', (⟨c, by omega⟩, roleOld d', e'), d'))
    (ht1 : M'.trans d' (T.nth (dirStep d')) =
      (some (otherDir d'), (⟨1, by omega⟩, roleNew d', e₂), otherDir d')) :
    ∃ T'' : Turing.Tape (Fin (N + 1) × Role5 × E),
      M'.step^[2 * c + 3] ⟨some Y, T⟩ = ⟨some (otherDir d'), T''⟩ ∧
      T''.nth 0 = (⟨c + 1, by omega⟩, roleNew d', e₂) ∧
      T''.nth (-dirStep d') = (0, .blank, e') ∧
      (∀ i : ℤ, i ≠ 0 → i ≠ -dirStep d' → T''.nth i = T.nth (i + dirStep d')) := by
  have hstep1 : M'.step ⟨some Y, T⟩ =
      ⟨some d', (T.write (⟨c, by omega⟩, roleOld d', e')).move d'⟩ := by
    rw [BiInfTM.step_some, show T.head = T.nth 0 from rfl, ht5]
  set S₁ := (T.write (⟨c, by omega⟩, roleOld d', e')).move d'
  have hS₁0 : S₁.nth 0 = T.nth (dirStep d') := by
    rw [tape_write_move_nth]; simp [zero_ne_neg_dirStep d']
  have hstep2 : M'.step ⟨some d', S₁⟩ =
      ⟨some (otherDir d'), (S₁.write (⟨1, by omega⟩, roleNew d', e₂)).move (otherDir d')⟩ := by
    rw [BiInfTM.step_some, show S₁.head = S₁.nth 0 from rfl, hS₁0, ht1]
  set S₂ := (S₁.write (⟨1, by omega⟩, roleNew d', e₂)).move (otherDir d')
  rcases tape_round_trip_nth T (⟨c, by omega⟩, roleOld d', e')
    (⟨1, by omega⟩, roleNew d', e₂) d' with ⟨hS₂0, hS₂d, hS₂_other⟩
  obtain ⟨T', hT'steps, hT'0, hT'd, hT'other⟩ :=
    transfer_loop M eQ hN extra M' hm' d' e' e₂ c 1 (by omega) (le_refl 1) S₂ hS₂0 hS₂d
  have hT'head : T'.head = (⟨0, Nat.zero_lt_succ N⟩, roleOld (otherDir (otherDir d')), e') := by
    simpa [Turing.Tape.nth_zero, otherDir_otherDir] using hT'0
  have hstep4 : M'.step ⟨some (otherDir d'), T'⟩ =
      ⟨some (otherDir d'), (T'.write (0, .blank, e')).move d'⟩ := by
    rw [BiInfTM.step_some, hT'head, hm', transTwoAux_rule4 M eQ hN extra (otherDir d') e',
      otherDir_otherDir]
  set T'' := (T'.write (0, .blank, e')).move d'
  have h2_it : M'.step^[2] ⟨some Y, T⟩ = ⟨some (otherDir d'), S₂⟩ := by
    change M'.step (M'.step ⟨some Y, T⟩) = _; rw [hstep1, hstep2]
  refine ⟨T'', ?_, ?_, ?_, ?_⟩
  · rw [show 2 * c + 3 = 1 + (2 * c + 2) by omega, Function.iterate_add_apply,
      Function.iterate_add_apply, Function.iterate_one, h2_it, hT'steps, hstep4]
  · rw [tape_write_move_nth]; simp [zero_ne_neg_dirStep d', hT'd]
  · rw [tape_write_move_nth]; simp
  · intro i hi0 hind
    rw [tape_write_move_nth, ite_eq_right_iff.mpr (fun h ↦ absurd h hind)]
    exact (hT'other (i + dirStep d') (by omega) (by omega)).trans
      (hS₂_other (i + dirStep d') (by omega) (by omega))

end Rules

end SharedTransitions

section NonBlankSim

/-- 2-state simulating Turing machine over `Sym2NB (Fintype.card Q) E` starting from a single
non-blank cell `(1, .Rnew, default)`. -/
noncomputable def stateTwoNonBlankTM {Q E : Type*} [Fintype Q] [Inhabited E]
    (M : BiInfTM Q E) : BiInfTM Turing.Dir (Sym2NB (Fintype.card Q) E) where
  initState := .left
  trans := transTwoAux M (canonInitEquiv M.initState) (le_refl _)
    (fun _ _ ↦ (none, default, .right))

/-- The initial state of `stateTwoNonBlankTM M` is `.left`. -/
@[simp] theorem stateTwoNonBlankTM_initState {Q E : Type*} [Fintype Q] [Inhabited E]
    (M : BiInfTM Q E) : (stateTwoNonBlankTM M).initState = .left := by
  dsimp [stateTwoNonBlankTM]

private lemma stateTwoNonBlankTM_trans {Q E : Type*} [Fintype Q] [Inhabited E] (M : BiInfTM Q E) :
    (stateTwoNonBlankTM M).trans = transTwoAux M (canonInitEquiv M.initState)
      (le_refl _) (fun _ _ ↦ (none, default, .right)) := by
  dsimp [stateTwoNonBlankTM]

private def RelNB {Q E : Type*} [Fintype Q] [Inhabited E] (M : BiInfTM Q E)
    (c₁ : Cfg Q E) (c₂ : Cfg Turing.Dir (Sym2NB (Fintype.card Q) E)) : Prop :=
  (c₁.state = none ∧ c₂.state = none) ∨
  (∃ (q : Q) (Y : Turing.Dir),
    c₁.state = some q ∧ c₂.state = some Y ∧
    c₂.tape.nth 0 = (⟨(canonInitEquiv M.initState q).1 + 1,
      Nat.succ_lt_succ (canonInitEquiv M.initState q).2⟩, roleNew (otherDir Y), c₁.tape.nth 0) ∧
    (∀ i : ℤ, i ≠ 0 → c₂.tape.nth i = (0, .blank, c₁.tape.nth i)))

private lemma relNB_init {Q E : Type*} [Fintype Q] [Inhabited E] (M : BiInfTM Q E) :
    RelNB M (M.initConfig default)
      ((stateTwoNonBlankTM M).initConfig
        (Turing.Tape.mk (1, .Rnew, default) default default)) := by
  refine Or.inr ⟨M.initState, .left, rfl, ?_, ?_, ?_⟩
  · simp [BiInfTM.initConfig_state, stateTwoNonBlankTM_initState]
  · have hpos : 0 < Fintype.card Q := Fintype.card_pos_iff.mpr ⟨M.initState⟩
    have h0 : (canonInitEquiv M.initState M.initState).1 = 0 := canonInitEquiv_self M.initState
    rw [BiInfTM.initConfig_tape, BiInfTM.initConfig_tape, tape_nth_default]
    exact Prod.ext (Fin.ext (by simp [h0, Nat.mod_eq_of_lt (Nat.succ_lt_succ hpos)])) rfl
  · intro i hi
    rw [BiInfTM.initConfig_tape, BiInfTM.initConfig_tape, tape_mk_single_nth _ hi,
      tape_nth_default]; rfl

private lemma relNB_step {Q E : Type*} [Fintype Q] [Inhabited E] (M : BiInfTM Q E)
    {c₁ : Cfg Q E} {c₂ : Cfg Turing.Dir (Sym2NB (Fintype.card Q) E)}
    (hR : RelNB M c₁ c₂) (hne : c₁.state ≠ none) :
    ∃ k ≥ 1, RelNB M (M.step c₁) ((stateTwoNonBlankTM M).step^[k] c₂) ∧
      ((M.step c₁).state = none → k = 1) := by
  rcases hR with ⟨h1, _⟩ | ⟨q, Y, hq, hY, hT0, hTother⟩
  · exact absurd h1 hne
  rcases c₁ with ⟨st₁, T₁⟩; rcases c₂ with ⟨st₂, T₂⟩
  dsimp only at hq hY; subst hq hY
  have hhead₁ : T₁.head = T₁.nth 0 := rfl
  rcases htr : M.trans q (T₁.nth 0) with ⟨_ | q', e', d'⟩
  · refine ⟨1, le_refl 1, Or.inl ⟨?_, ?_⟩, fun _ ↦ rfl⟩
    · rw [BiInfTM.step_some, hhead₁, htr]
    · simp only [Function.iterate_one, BiInfTM.step_some, ← Turing.Tape.nth_zero,
        stateTwoNonBlankTM_trans, hT0, transTwoAux_rule5, htr]
  · let eQ := canonInitEquiv M.initState
    have htr5 : (stateTwoNonBlankTM M).trans Y (T₂.nth 0) =
        (some d', (⟨(eQ q').1, by have := (eQ q').2; omega⟩, roleOld d', e'), d') := by
      rw [stateTwoNonBlankTM_trans, hT0, transTwoAux_rule5, htr]
    have htr1 : (stateTwoNonBlankTM M).trans d' (T₂.nth (dirStep d')) =
        (some (otherDir d'), (⟨1, by have := (eQ q').2; omega⟩,
          roleNew d', T₁.nth (dirStep d')), otherDir d') := by
      rw [stateTwoNonBlankTM_trans, hTother (dirStep d') (dirStep_ne_zero d')]
      exact transTwoAux_rule1 M eQ (le_refl _) _ d' _
    obtain ⟨T'', hT''steps, hT''0, hT''neg, hT''other⟩ :=
      simulate_active_step M eQ (le_refl _) _ (stateTwoNonBlankTM M)
        (stateTwoNonBlankTM_trans M) (eQ q').2 htr5 htr1
    rcases tape_step_nth T₁ e' d' with ⟨hT1'0, hT1'neg, hT1'other⟩
    have hmstep : M.step ⟨some q, T₁⟩ = ⟨some q', (T₁.write e').move d'⟩ := by
      rw [BiInfTM.step_some, hhead₁, htr]
    refine ⟨2 * (eQ q').1 + 3, by omega, Or.inr ⟨q', otherDir d', ?_, ?_, ?_, ?_⟩, fun hn ↦ ?_⟩
    · rw [hmstep]
    · rw [hT''steps]
    · rw [hmstep, hT''steps]; dsimp only [Cfg.tape]; rw [hT''0, hT1'0, otherDir_otherDir]
    · intro i hi0; rw [hmstep, hT''steps]; dsimp only [Cfg.tape]
      by_cases hind : i = -dirStep d'
      · subst hind; rw [hT''neg, hT1'neg]
      · rw [hT''other i hi0 hind, hTother (i + dirStep d') (fun h ↦ hind (by omega)),
          hT1'other i hind]
    · rw [hmstep] at hn; nomatch hn

private noncomputable def simSeqNB {Q E : Type*} [Fintype Q] [Inhabited E] (M : BiInfTM Q E) :
    (t : ℕ) → { u : ℕ //
      RelNB M (M.evalSteps t default)
        ((stateTwoNonBlankTM M).evalSteps u
          (Turing.Tape.mk (1, .Rnew, default) default default)) }
  | 0 => ⟨0, relNB_init M⟩
  | t + 1 => by
    classical
    let prev := simSeqNB M t
    exact if hs : (M.evalSteps t default).state = none then
      ⟨prev.1, by rw [M.evalSteps_succ, M.step_of_state_eq_none hs]; exact prev.2⟩
    else
      let hex := relNB_step M prev.2 hs
      ⟨prev.1 + Classical.choose hex, by
        rw [M.evalSteps_succ, (stateTwoNonBlankTM M).evalSteps_add]
        exact (Classical.choose_spec hex).2.1⟩

/-- Starting from the single non-blank tape cell `(1, .Rnew, default)`,
`stateTwoNonBlankTM M` simulates `M` faithfully and halts in `u ≥ M.time` steps. -/
theorem stateTwoNonBlankTM_halts_and_time_le {Q E : Type*} [Fintype Q] [Inhabited E]
    (M : BiInfTM Q E) (h : M.HaltsOnBlank) :
    ∃ u : ℕ, M.time ≤ u ∧
      ((stateTwoNonBlankTM M).evalSteps u
        (Turing.Tape.mk (1, .Rnew, default) default default)).state = none ∧
      ∀ j < u,
        ((stateTwoNonBlankTM M).evalSteps j
          (Turing.Tape.mk (1, .Rnew, default) default default)).state ≠ none := by
  classical
  let T₀ : Turing.Tape (Sym2NB (Fintype.card Q) E) :=
    Turing.Tape.mk (1, .Rnew, default) default default
  let M' := stateTwoNonBlankTM M
  let seq := simSeqNB M
  have hle : ∀ t ≤ M.time, t ≤ (seq t).1 := by
    intro t ht
    induction t with
    | zero => exact Nat.zero_le _
    | succ t ih =>
      have ht_lt : t < M.time := Nat.lt_of_succ_le ht
      have hnot : (M.evalSteps t default).state ≠ none :=
        M.not_haltsInStepsOnBlank_of_lt_time ht_lt
      have hnext : (seq (t + 1)).1 =
          (seq t).1 + Classical.choose (relNB_step M (seq t).2 hnot) := by
        change (simSeqNB M (t + 1)).1 = _; dsimp [simSeqNB]; rw [dite_eq_right hnot]
      have hk := (Classical.choose_spec (relNB_step M (seq t).2 hnot)).1
      have iht := ih ht_lt.le; omega
  let t₀ : ℕ := M.time - 1
  have ht₀_lt : t₀ < M.time := Nat.sub_lt (M.one_le_time_of_haltsOnBlank h) Nat.zero_lt_one
  have ht₀_succ : t₀ + 1 = M.time := Nat.sub_add_cancel (M.one_le_time_of_haltsOnBlank h)
  have hnot₀ : (M.evalSteps t₀ default).state ≠ none :=
    M.not_haltsInStepsOnBlank_of_lt_time ht₀_lt
  have hhalt_time : (M.evalSteps M.time default).state = none := M.haltsInStepsOnBlank_time h
  have hk1 : Classical.choose (relNB_step M (seq t₀).2 hnot₀) = 1 :=
    (Classical.choose_spec (relNB_step M (seq t₀).2 hnot₀)).2.2
      (by rw [← M.evalSteps_succ, ht₀_succ]; exact hhalt_time)
  have hu_eq : (seq M.time).1 = (seq t₀).1 + 1 := by
    rw [← ht₀_succ]; change (simSeqNB M (t₀ + 1)).1 = (seq t₀).1 + 1
    dsimp [simSeqNB]; rw [dite_eq_right hnot₀]; dsimp only; rw [hk1]
  have hne0 : (M'.evalSteps (seq t₀).1 T₀).state ≠ none := by
    rcases (seq t₀).2 with ⟨h1, _⟩ | ⟨q, Y, _, hY, _, _⟩
    · exact absurd h1 hnot₀
    · rw [show (M'.evalSteps (seq t₀).1 T₀).state = some Y from hY]
      exact Option.some_ne_none Y
  have hhalt_u : (M'.evalSteps (seq M.time).1 T₀).state = none := by
    rcases (seq M.time).2 with ⟨_, h2⟩ | ⟨q, _, hq, _, _, _⟩
    · exact h2
    · rw [hhalt_time] at hq; nomatch hq
  refine ⟨(seq M.time).1, hle M.time (le_refl _), hhalt_u, fun j hj hhj ↦ ?_⟩
  have hhj' : (M'.evalSteps j T₀).state = none := hhj
  have heq := M'.evalSteps_eq_of_halted hhj' (show j ≤ (seq t₀).1 by omega)
  exact hne0 (by rw [heq]; exact hhj')

end NonBlankSim

section BlankSim

private def initDir₂ {Q E : Type*} [Inhabited E] (M : BiInfTM Q E) : Turing.Dir :=
  (M.trans M.initState default).2.2

private noncomputable def transTwoBootExtra {Q E : Type*} [Fintype Q] [Inhabited E]
    (M : BiInfTM Q E) (eQ : Q ≃ Fin (Fintype.card Q))
    (q : Turing.Dir) (sym : Sym2B (Fintype.card Q) E) :
    Option Turing.Dir × Sym2B (Fintype.card Q) E × Turing.Dir :=
  let n := Fintype.card Q; let X := initDir₂ M
  let c := sym.1.1; let r := sym.2.1; let e := sym.2.2
  if c = n + 1 ∧ q = X ∧ r = roleNew X then
    match M.trans M.initState e with
    | (none, _, _) => (none, default, .right)
    | (some q', e', d') =>
      (some d', (⟨(eQ q').1, by have := (eQ q').2; omega⟩, roleOld d', e'), d')
  else if c = n + 1 ∧ q = otherDir X ∧ r = roleNew (otherDir X) then
    (some X, (⟨1, by omega⟩, roleNew (otherDir X), e), X)
  else (none, default, .right)

/-- 2-state simulating Turing machine over `Sym2B (Fintype.card Q) E` starting from the
all-blank tape via the overflow bootstrap. -/
noncomputable def stateTwoBlankTM {Q E : Type*} [Fintype Q] [Inhabited E]
    (M : BiInfTM Q E) : BiInfTM Turing.Dir (Sym2B (Fintype.card Q) E) where
  initState := initDir₂ M
  trans := transTwoAux M (canonInitEquiv M.initState) (Nat.le_succ _)
    (transTwoBootExtra M (canonInitEquiv M.initState))

/-- The initial state of `stateTwoBlankTM M` is `(M.trans M.initState default).2.2`. -/
@[simp] theorem stateTwoBlankTM_initState {Q E : Type*} [Fintype Q] [Inhabited E]
    (M : BiInfTM Q E) : (stateTwoBlankTM M).initState = (M.trans M.initState default).2.2 := by
  dsimp [stateTwoBlankTM, initDir₂]

private lemma stateTwoBlankTM_initDir {Q E : Type*} [Fintype Q] [Inhabited E] (M : BiInfTM Q E) :
    (stateTwoBlankTM M).initState = initDir₂ M := by dsimp [stateTwoBlankTM]

private lemma stateTwoBlankTM_trans {Q E : Type*} [Fintype Q] [Inhabited E] (M : BiInfTM Q E) :
    (stateTwoBlankTM M).trans = transTwoAux M (canonInitEquiv M.initState)
      (Nat.le_succ _) (transTwoBootExtra M (canonInitEquiv M.initState)) := by
  dsimp [stateTwoBlankTM]

private lemma transTwoB_bootStart {Q E : Type*} [Fintype Q] [Inhabited E] (M : BiInfTM Q E)
    (eQ : Q ≃ Fin (Fintype.card Q)) (e : E) :
    transTwoAux M eQ (Nat.le_succ _) (transTwoBootExtra M eQ) (initDir₂ M)
        (⟨Fintype.card Q + 1, by omega⟩, roleNew (initDir₂ M), e) =
      match M.trans M.initState e with
      | (none, _, _) => (none, default, .right)
      | (some q', e', d') =>
        (some d', (⟨(eQ q').1, by have := (eQ q').2; omega⟩, roleOld d', e'), d') := by
  dsimp only [transTwoAux, transTwoBootExtra]
  rw [ite_eq_right_iff.mpr (fun h ↦ absurd h.1 (Nat.succ_ne_zero _)),
    ite_eq_right_iff.mpr (fun h ↦ by have := h.2.1; omega),
    ite_eq_right_iff.mpr (fun h ↦ by have := h.2.1; omega),
    ite_eq_right_iff.mpr (fun h ↦ absurd h.1 (Nat.succ_ne_zero _)),
    ite_eq_right_iff.mpr (fun h ↦ by have := h.2.1; omega),
    ite_eq_left_iff.mpr (fun h ↦ absurd ⟨rfl, rfl, rfl⟩ h)]

private lemma transTwoB_bootBlank {Q E : Type*} [Fintype Q] [Inhabited E] (M : BiInfTM Q E)
    (eQ : Q ≃ Fin (Fintype.card Q)) (e : E) :
    transTwoAux M eQ (Nat.le_succ _) (transTwoBootExtra M eQ) (otherDir (initDir₂ M))
        (⟨Fintype.card Q + 1, by omega⟩, roleNew (otherDir (initDir₂ M)), e) =
      (some (initDir₂ M), (⟨1, by omega⟩, roleNew (otherDir (initDir₂ M)), e), initDir₂ M) := by
  dsimp only [transTwoAux, transTwoBootExtra]
  rw [ite_eq_right_iff.mpr (fun h ↦ absurd h.1 (Nat.succ_ne_zero _)),
    ite_eq_right_iff.mpr (fun h ↦ by have := h.2.1; omega),
    ite_eq_right_iff.mpr (fun h ↦ by have := h.2.1; omega),
    ite_eq_right_iff.mpr (fun h ↦ absurd h.1 (Nat.succ_ne_zero _)),
    ite_eq_right_iff.mpr (fun h ↦ by have := h.2.1; omega),
    ite_eq_right_iff.mpr (fun h ↦ absurd h.2.1 (otherDir_ne (initDir₂ M))),
    ite_eq_left_iff.mpr (fun h ↦ absurd ⟨rfl, rfl, rfl⟩ h)]

private lemma boot_round_trip {Q E : Type*} [Fintype Q] [Inhabited E] (M : BiInfTM Q E)
    (T : Turing.Tape (Sym2B (Fintype.card Q) E)) (k : ℕ) (r₀ : Role5)
    (hk : k + 1 ≤ Fintype.card Q + 1)
    (h1 : (stateTwoBlankTM M).step ⟨some (initDir₂ M), T⟩ =
      ⟨some (otherDir (initDir₂ M)),
        (T.write (⟨k + 1, by omega⟩, roleNew (initDir₂ M), default)).move
          (otherDir (initDir₂ M))⟩)
    (hTneg : T.nth (-dirStep (initDir₂ M)) = (⟨k, by omega⟩, r₀, default))
    (htr2 : ∀ U : Turing.Tape (Sym2B (Fintype.card Q) E),
      U.head = (⟨k, by omega⟩, r₀, default) →
      (stateTwoBlankTM M).step ⟨some (otherDir (initDir₂ M)), U⟩ =
        ⟨some (initDir₂ M),
          (U.write (⟨k + 1, by omega⟩, roleNew (otherDir (initDir₂ M)), default)).move
            (initDir₂ M)⟩) :
    ∃ V : Turing.Tape (Sym2B (Fintype.card Q) E),
      (stateTwoBlankTM M).step^[2] ⟨some (initDir₂ M), T⟩ = ⟨some (initDir₂ M), V⟩ ∧
      V.nth 0 = (⟨k + 1, by omega⟩, roleNew (initDir₂ M), default) ∧
      V.nth (-dirStep (initDir₂ M)) =
        (⟨k + 1, by omega⟩, roleNew (otherDir (initDir₂ M)), default) ∧
      (∀ i : ℤ, i ≠ 0 → i ≠ -dirStep (initDir₂ M) → V.nth i = T.nth i) := by
  set U := (T.write (⟨k + 1, by omega⟩, roleNew (initDir₂ M), default)).move
    (otherDir (initDir₂ M))
  have hUhead : U.head = (⟨k, by omega⟩, r₀, default) := by
    change U.nth 0 = _; rw [tape_write_move_nth, dirStep_otherDir, neg_neg]
    simp [(dirStep_ne_zero (initDir₂ M)).symm, hTneg]
  rcases tape_round_trip_nth T (⟨k + 1, by omega⟩, roleNew (initDir₂ M), default)
    (⟨k + 1, by omega⟩, roleNew (otherDir (initDir₂ M)), default)
    (otherDir (initDir₂ M)) with ⟨hV0, hVneg, hVother⟩
  simp only [otherDir_otherDir, dirStep_otherDir] at hV0 hVneg hVother
  refine ⟨_, ?_, hV0, hVneg, fun i hi0 hind ↦ hVother i hi0 hind⟩
  change (stateTwoBlankTM M).step ((stateTwoBlankTM M).step ⟨some (initDir₂ M), T⟩) = _
  rw [h1, htr2 U hUhead]

private lemma bootstrap_aux {Q E : Type*} [Fintype Q] [Inhabited E] (M : BiInfTM Q E) :
    ∀ k : ℕ, (hk : k ≤ Fintype.card Q) →
      ∃ T : Turing.Tape (Sym2B (Fintype.card Q) E),
        (stateTwoBlankTM M).evalSteps (2 * (k + 1)) default = ⟨some (initDir₂ M), T⟩ ∧
        T.nth 0 = (⟨k + 1, by omega⟩, roleNew (initDir₂ M), default) ∧
        T.nth (-dirStep (initDir₂ M)) =
          (⟨k + 1, by omega⟩, roleNew (otherDir (initDir₂ M)), default) ∧
        (∀ i : ℤ, i ≠ 0 → i ≠ -dirStep (initDir₂ M) → T.nth i = (0, .blank, default))
  | 0, hk => by
    have hhead : (default : Turing.Tape (Sym2B (Fintype.card Q) E)).head =
        (⟨0, Nat.zero_lt_succ _⟩, .blank, default) := rfl
    have hstep1 : (stateTwoBlankTM M).step
        ⟨some (initDir₂ M), (default : Turing.Tape (Sym2B (Fintype.card Q) E))⟩ =
        ⟨some (otherDir (initDir₂ M)),
          ((default : Turing.Tape (Sym2B (Fintype.card Q) E)).write
            (⟨1, by omega⟩, roleNew (initDir₂ M), default)).move (otherDir (initDir₂ M))⟩ := by
      rw [BiInfTM.step_some, stateTwoBlankTM_trans, hhead, transTwoAux_rule1]
    have hTneg : (default : Turing.Tape (Sym2B (Fintype.card Q) E)).nth (-dirStep (initDir₂ M)) =
        (⟨0, Nat.zero_lt_succ _⟩, .blank, default) := by rw [tape_nth_default]; rfl
    have htr2 : ∀ U : Turing.Tape (Sym2B (Fintype.card Q) E),
        U.head = (⟨0, Nat.zero_lt_succ _⟩, .blank, default) →
        (stateTwoBlankTM M).step ⟨some (otherDir (initDir₂ M)), U⟩ =
          ⟨some (initDir₂ M),
            (U.write (⟨1, by omega⟩, roleNew (otherDir (initDir₂ M)), default)).move
              (initDir₂ M)⟩ := fun U hU ↦ by
      rw [BiInfTM.step_some, stateTwoBlankTM_trans, hU, transTwoAux_rule1, otherDir_otherDir]
    obtain ⟨V, hVsteps, hV0, hVneg, hVother⟩ :=
      boot_round_trip M default 0 .blank (by omega) hstep1 hTneg htr2
    refine ⟨V, ?_, hV0, hVneg, fun i hi0 hind ↦ ?_⟩
    · rw [BiInfTM.evalSteps_def, BiInfTM.initConfig_def, stateTwoBlankTM_initDir]; exact hVsteps
    · rw [hVother i hi0 hind, tape_nth_default]; rfl
  | k + 1, hk => by
    obtain ⟨T, hTsteps, hT0, hTneg, hTother⟩ := bootstrap_aux M k (by omega)
    have hstep1 : (stateTwoBlankTM M).step ⟨some (initDir₂ M), T⟩ =
        ⟨some (otherDir (initDir₂ M)),
          (T.write (⟨k + 2, by omega⟩, roleNew (initDir₂ M), default)).move
            (otherDir (initDir₂ M))⟩ := by
      rw [BiInfTM.step_some, stateTwoBlankTM_trans, show T.head = T.nth 0 from rfl, hT0,
        transTwoAux_rule2 M _ _ _ (initDir₂ M) (k + 1) (by omega) (by omega) (by omega) default]
    have htr2 : ∀ U : Turing.Tape (Sym2B (Fintype.card Q) E),
        U.head = (⟨k + 1, by omega⟩, roleNew (otherDir (initDir₂ M)), default) →
        (stateTwoBlankTM M).step ⟨some (otherDir (initDir₂ M)), U⟩ =
          ⟨some (initDir₂ M),
            (U.write (⟨k + 2, by omega⟩, roleNew (otherDir (initDir₂ M)), default)).move
              (initDir₂ M)⟩ := fun U hU ↦ by
      rw [BiInfTM.step_some, stateTwoBlankTM_trans, hU,
        transTwoAux_rule2 M _ _ _ (otherDir (initDir₂ M)) (k + 1) (by omega) (by omega)
          (by omega) default, otherDir_otherDir]
    obtain ⟨V, hVsteps, hV0, hVneg, hVother⟩ :=
      boot_round_trip M T (k + 1) (roleNew (otherDir (initDir₂ M))) (by omega) hstep1 hTneg htr2
    refine ⟨V, ?_, hV0, hVneg, fun i hi0 hind ↦ (hVother i hi0 hind).trans (hTother i hi0 hind)⟩
    rw [show 2 * (k + 1 + 1) = 2 * (k + 1) + 2 by omega, BiInfTM.evalSteps_add, hTsteps, hVsteps]

private def RelB {Q E : Type*} [Fintype Q] [Inhabited E] (M : BiInfTM Q E)
    (c₁ : Cfg Q E) (c₂ : Cfg Turing.Dir (Sym2B (Fintype.card Q) E)) : Prop :=
  (c₁.state = none ∧ c₂.state = none) ∨
  (c₁.state = some M.initState ∧ c₁.tape.nth 0 = default ∧ c₂.state = some (initDir₂ M) ∧
    c₂.tape.nth 0 = (⟨Fintype.card Q + 1, by omega⟩, roleNew (initDir₂ M), default) ∧
    c₂.tape.nth (-dirStep (initDir₂ M)) =
      (⟨Fintype.card Q + 1, by omega⟩, roleNew (otherDir (initDir₂ M)), default) ∧
    c₁.tape.nth (-dirStep (initDir₂ M)) = default ∧
    (∀ i : ℤ, i ≠ 0 → i ≠ -dirStep (initDir₂ M) → c₂.tape.nth i = (0, .blank, c₁.tape.nth i))) ∨
  (∃ (m : ℕ) (q : Q) (Y : Turing.Dir),
    c₁.state = some q ∧ c₂.state = some Y ∧
    c₂.tape.nth 0 = (⟨(canonInitEquiv M.initState q).1 + 1,
      by have := (canonInitEquiv M.initState q).2; omega⟩, roleNew (otherDir Y), c₁.tape.nth 0) ∧
    c₂.tape.nth (-((m + 1 : ℕ) : ℤ) * dirStep (initDir₂ M)) =
      (⟨Fintype.card Q + 1, by omega⟩, roleNew (otherDir (initDir₂ M)), default) ∧
    c₁.tape.nth (-((m + 1 : ℕ) : ℤ) * dirStep (initDir₂ M)) = default ∧
    (∀ i : ℤ, i ≠ 0 → i ≠ -((m + 1 : ℕ) : ℤ) * dirStep (initDir₂ M) →
      c₂.tape.nth i = (0, .blank, c₁.tape.nth i))) ∨
  (∃ (q : Q) (Y : Turing.Dir),
    c₁.state = some q ∧ c₂.state = some Y ∧
    c₂.tape.nth 0 = (⟨(canonInitEquiv M.initState q).1 + 1,
      by have := (canonInitEquiv M.initState q).2; omega⟩, roleNew (otherDir Y), c₁.tape.nth 0) ∧
    (∀ i : ℤ, i ≠ 0 → c₂.tape.nth i = (0, .blank, c₁.tape.nth i)))

private lemma relB_init {Q E : Type*} [Fintype Q] [Inhabited E] (M : BiInfTM Q E) :
    ∃ k₀, RelB M (M.initConfig default) ((stateTwoBlankTM M).evalSteps k₀ default) := by
  obtain ⟨T, hTsteps, hT0, hTneg, hTother⟩ := bootstrap_aux M (Fintype.card Q) (le_refl _)
  refine ⟨2 * (Fintype.card Q + 1), Or.inr (Or.inl ⟨rfl, tape_nth_default 0, ?_⟩)⟩
  rw [hTsteps]
  refine ⟨rfl, hT0, hTneg, tape_nth_default _, fun i hi0 hind ↦ ?_⟩
  rw [hTother i hi0 hind, BiInfTM.initConfig_tape, tape_nth_default]

private lemma stepB_halt {Q E : Type*} [Fintype Q] [Inhabited E] (M : BiInfTM Q E)
    {T₁ : Turing.Tape E} {T₂ : Turing.Tape (Sym2B (Fintype.card Q) E)}
    {q : Q} {Y : Turing.Dir} {e' : E} {d' : Turing.Dir}
    (htr : M.trans q (T₁.nth 0) = (none, e', d'))
    (ht5 : ((stateTwoBlankTM M).trans Y (T₂.nth 0)).1 = none) :
    RelB M (M.step ⟨some q, T₁⟩) ((stateTwoBlankTM M).step^[1] ⟨some Y, T₂⟩) := by
  refine Or.inl ⟨?_, ?_⟩
  · rw [BiInfTM.step_some, show T₁.head = T₁.nth 0 from rfl, htr]
  · simpa [Function.iterate_one, BiInfTM.step_some, ← Turing.Tape.nth_zero] using ht5

private lemma stepB_active {Q E : Type*} [Fintype Q] [Inhabited E] (M : BiInfTM Q E)
    {T₁ : Turing.Tape E} {T₂ : Turing.Tape (Sym2B (Fintype.card Q) E)}
    {q q' : Q} {e' : E} {Y d' : Turing.Dir}
    (htr : M.trans q (T₁.nth 0) = (some q', e', d'))
    (ht5 : (stateTwoBlankTM M).trans Y (T₂.nth 0) =
      (some d', (⟨(canonInitEquiv M.initState q').1,
        by have := (canonInitEquiv M.initState q').2; omega⟩, roleOld d', e'), d'))
    (ht1 : (stateTwoBlankTM M).trans d' (T₂.nth (dirStep d')) =
      (some (otherDir d'), (⟨1, by omega⟩, roleNew d', T₁.nth (dirStep d')), otherDir d')) :
    ∃ T'',
      (stateTwoBlankTM M).step^[2 * (canonInitEquiv M.initState q').1 + 3] ⟨some Y, T₂⟩ =
        ⟨some (otherDir d'), T''⟩ ∧
      M.step ⟨some q, T₁⟩ = ⟨some q', (T₁.write e').move d'⟩ ∧
      T''.nth 0 = (⟨(canonInitEquiv M.initState q').1 + 1,
        by have := (canonInitEquiv M.initState q').2; omega⟩,
        roleNew (otherDir (otherDir d')), ((T₁.write e').move d').nth 0) ∧
      T''.nth (-dirStep d') = (0, .blank, ((T₁.write e').move d').nth (-dirStep d')) ∧
      (∀ i : ℤ, i ≠ 0 → i ≠ -dirStep d' → T''.nth i = T₂.nth (i + dirStep d')) ∧
      (∀ i : ℤ, i ≠ -dirStep d' → ((T₁.write e').move d').nth i = T₁.nth (i + dirStep d')) := by
  let eQ := canonInitEquiv M.initState
  obtain ⟨T'', hT''steps, hT''0, hT''neg, hT''other⟩ :=
    simulate_active_step M eQ (Nat.le_succ _) _ (stateTwoBlankTM M)
      (stateTwoBlankTM_trans M) (eQ q').2 ht5 ht1
  rcases tape_step_nth T₁ e' d' with ⟨hT1'0, hT1'neg, hT1'other⟩
  refine ⟨T'', hT''steps, ?_, ?_, ?_, hT''other, hT1'other⟩
  · rw [BiInfTM.step_some, show T₁.head = T₁.nth 0 from rfl, htr]
  · rw [hT''0, hT1'0, otherDir_otherDir]
  · rw [hT''neg, hT1'neg]

private lemma stepB_keepBoot {Q E : Type*} [Fintype Q] [Inhabited E] (M : BiInfTM Q E)
    {T₁ : Turing.Tape E} {T₂ : Turing.Tape (Sym2B (Fintype.card Q) E)}
    {q q' : Q} {e' : E} {Y d' : Turing.Dir} (m' : ℕ) {b : ℤ}
    (htr : M.trans q (T₁.nth 0) = (some q', e', d'))
    (ht5 : (stateTwoBlankTM M).trans Y (T₂.nth 0) =
      (some d', (⟨(canonInitEquiv M.initState q').1,
        by have := (canonInitEquiv M.initState q').2; omega⟩, roleOld d', e'), d'))
    (ht1 : (stateTwoBlankTM M).trans d' (T₂.nth (dirStep d')) =
      (some (otherDir d'), (⟨1, by omega⟩, roleNew d', T₁.nth (dirStep d')), otherDir d'))
    (hb2 : T₂.nth b =
      (⟨Fintype.card Q + 1, by omega⟩, roleNew (otherDir (initDir₂ M)), default))
    (hb1 : T₁.nth b = default)
    (hoth : ∀ i : ℤ, i ≠ 0 → i ≠ b → T₂.nth i = (0, .blank, T₁.nth i))
    (hne0 : -((m' + 1 : ℕ) : ℤ) * dirStep (initDir₂ M) ≠ 0)
    (hned : -((m' + 1 : ℕ) : ℤ) * dirStep (initDir₂ M) ≠ -dirStep d')
    (hsh : -((m' + 1 : ℕ) : ℤ) * dirStep (initDir₂ M) + dirStep d' = b) :
    ∃ k ≥ 1, RelB M (M.step ⟨some q, T₁⟩) ((stateTwoBlankTM M).step^[k] ⟨some Y, T₂⟩) := by
  obtain ⟨T'', hT''steps, hmstep, hT''0, hT''neg, hT''other, hT1'other⟩ :=
    stepB_active M htr ht5 ht1
  refine ⟨2 * (canonInitEquiv M.initState q').1 + 3, by omega,
    Or.inr (Or.inr (Or.inl ⟨m', q', otherDir d', ?_, ?_, ?_, ?_, ?_, ?_⟩))⟩
  · rw [hmstep]
  · rw [hT''steps]
  · rw [hmstep, hT''steps]; exact hT''0
  · rw [hT''steps, hT''other _ hne0 hned, hsh]; exact hb2
  · rw [hmstep, hT1'other _ hned, hsh]; exact hb1
  · intro i hi0 hib; rw [hmstep, hT''steps]
    by_cases hind : i = -dirStep d'
    · subst hind; exact hT''neg
    · rw [hT''other i hi0 hind, hT1'other i hind]
      exact hoth _ (fun h ↦ hind (by omega)) (fun h ↦ hib (by omega))

private lemma stepB_clean {Q E : Type*} [Fintype Q] [Inhabited E] (M : BiInfTM Q E)
    {T₁ : Turing.Tape E} {T₂ : Turing.Tape (Sym2B (Fintype.card Q) E)}
    {q q' : Q} {e' : E} {Y d' : Turing.Dir}
    (htr : M.trans q (T₁.nth 0) = (some q', e', d'))
    (ht5 : (stateTwoBlankTM M).trans Y (T₂.nth 0) =
      (some d', (⟨(canonInitEquiv M.initState q').1,
        by have := (canonInitEquiv M.initState q').2; omega⟩, roleOld d', e'), d'))
    (ht1 : (stateTwoBlankTM M).trans d' (T₂.nth (dirStep d')) =
      (some (otherDir d'), (⟨1, by omega⟩, roleNew d', T₁.nth (dirStep d')), otherDir d'))
    (hoth : ∀ i : ℤ, i ≠ 0 → i ≠ -dirStep d' →
      T₂.nth (i + dirStep d') = (0, .blank, T₁.nth (i + dirStep d'))) :
    ∃ k ≥ 1, RelB M (M.step ⟨some q, T₁⟩) ((stateTwoBlankTM M).step^[k] ⟨some Y, T₂⟩) := by
  obtain ⟨T'', hT''steps, hmstep, hT''0, hT''neg, hT''other, hT1'other⟩ :=
    stepB_active M htr ht5 ht1
  refine ⟨2 * (canonInitEquiv M.initState q').1 + 3, by omega,
    Or.inr (Or.inr (Or.inr ⟨q', otherDir d', ?_, ?_, ?_, ?_⟩))⟩
  · rw [hmstep]
  · rw [hT''steps]
  · rw [hmstep, hT''steps]; exact hT''0
  · intro i hi0; rw [hmstep, hT''steps]
    by_cases hind : i = -dirStep d'
    · subst hind; exact hT''neg
    · rw [hT''other i hi0 hind, hT1'other i hind]; exact hoth i hi0 hind

private lemma relB_step {Q E : Type*} [Fintype Q] [Inhabited E] (M : BiInfTM Q E)
    {c₁ : Cfg Q E} {c₂ : Cfg Turing.Dir (Sym2B (Fintype.card Q) E)}
    (hR : RelB M c₁ c₂) (hne : c₁.state ≠ none) :
    ∃ k ≥ 1, RelB M (M.step c₁) ((stateTwoBlankTM M).step^[k] c₂) := by
  let eQ := canonInitEquiv M.initState
  rcases hR with ⟨h1, _⟩ | ⟨hq, hT10, hY, hT20, hT2neg, hT1neg, hTother⟩ |
      ⟨m, q, Y, hq, hY, hT0, hTb2, hTb1, hTother⟩ | ⟨q, Y, hq, hY, hT0, hTother⟩
  · exact absurd h1 hne
  · rcases c₁ with ⟨st₁, T₁⟩; rcases c₂ with ⟨st₂, T₂⟩
    dsimp only at hq hT10 hY; subst hq hY
    rcases htr : M.trans M.initState default with ⟨_ | q', e', d'⟩
    · exact ⟨1, le_refl 1, stepB_halt M (by rw [hT10, htr])
        (by rw [stateTwoBlankTM_trans, hT20, transTwoB_bootStart, htr])⟩
    · have hd' : d' = initDir₂ M := by change d' = (M.trans M.initState default).2.2; rw [htr]
      subst hd'
      have ht5 : (stateTwoBlankTM M).trans (initDir₂ M) (T₂.nth 0) =
          (some (initDir₂ M), (⟨(eQ q').1, by have := (eQ q').2; omega⟩,
            roleOld (initDir₂ M), e'), initDir₂ M) := by
        rw [stateTwoBlankTM_trans, hT20, transTwoB_bootStart, htr]
      have ht1 : (stateTwoBlankTM M).trans (initDir₂ M) (T₂.nth (dirStep (initDir₂ M))) =
          (some (otherDir (initDir₂ M)), (⟨1, by omega⟩, roleNew (initDir₂ M),
            T₁.nth (dirStep (initDir₂ M))), otherDir (initDir₂ M)) := by
        rw [stateTwoBlankTM_trans, hTother _ (dirStep_ne_zero _) (dirStep_ne_neg_self _)]
        exact transTwoAux_rule1 M eQ _ _ (initDir₂ M) _
      exact stepB_keepBoot M 1 (by rw [hT10, htr]) ht5 ht1 hT2neg hT1neg hTother
        (by cases initDir₂ M <;> simp [dirStep])
        (by cases initDir₂ M <;> simp [dirStep])
        (by cases initDir₂ M <;> simp [dirStep])
  · rcases c₁ with ⟨st₁, T₁⟩; rcases c₂ with ⟨st₂, T₂⟩
    dsimp only at hq hY; subst hq hY
    rcases htr : M.trans q (T₁.nth 0) with ⟨_ | q', e', d'⟩
    · exact ⟨1, le_refl 1, stepB_halt M htr
        (by rw [stateTwoBlankTM_trans, hT0, transTwoAux_rule5, htr])⟩
    · have ht5 : (stateTwoBlankTM M).trans Y (T₂.nth 0) =
          (some d', (⟨(eQ q').1, by have := (eQ q').2; omega⟩, roleOld d', e'), d') := by
        rw [stateTwoBlankTM_trans, hT0, transTwoAux_rule5, htr]
      by_cases hdX : d' = initDir₂ M
      · subst hdX
        have ht1 : (stateTwoBlankTM M).trans (initDir₂ M) (T₂.nth (dirStep (initDir₂ M))) =
            (some (otherDir (initDir₂ M)), (⟨1, by omega⟩, roleNew (initDir₂ M),
              T₁.nth (dirStep (initDir₂ M))), otherDir (initDir₂ M)) := by
          rw [stateTwoBlankTM_trans,
            hTother _ (dirStep_ne_zero _) (by cases initDir₂ M <;> simp [dirStep] <;> omega)]
          exact transTwoAux_rule1 M eQ _ _ (initDir₂ M) _
        exact stepB_keepBoot M (m + 1) htr ht5 ht1 hTb2 hTb1 hTother
          (by cases initDir₂ M <;> simp [dirStep] <;> omega)
          (by cases initDir₂ M <;> simp [dirStep] <;> omega)
          (by cases initDir₂ M <;> simp [dirStep])
      · have hd_eq : d' = otherDir (initDir₂ M) := by
          cases hd' : d' <;> cases hX' : initDir₂ M <;> simp_all [otherDir]
        subst hd_eq
        cases m with
        | zero =>
          have hb_eq : dirStep (otherDir (initDir₂ M)) =
              -((0 + 1 : ℕ) : ℤ) * dirStep (initDir₂ M) := by simp [dirStep_otherDir]
          have ht1 : (stateTwoBlankTM M).trans (otherDir (initDir₂ M))
              (T₂.nth (dirStep (otherDir (initDir₂ M)))) =
              (some (otherDir (otherDir (initDir₂ M))),
                (⟨1, by omega⟩, roleNew (otherDir (initDir₂ M)),
                  T₁.nth (dirStep (otherDir (initDir₂ M)))),
                otherDir (otherDir (initDir₂ M))) := by
            rw [stateTwoBlankTM_trans, hb_eq, hTb2, hTb1, transTwoB_bootBlank, otherDir_otherDir]
          exact stepB_clean M htr ht5 ht1 fun i hi0 hind ↦
            hTother _ (by omega) (by rw [← hb_eq]; omega)
        | succ m' =>
          have ht1 : (stateTwoBlankTM M).trans (otherDir (initDir₂ M))
              (T₂.nth (dirStep (otherDir (initDir₂ M)))) =
              (some (otherDir (otherDir (initDir₂ M))),
                (⟨1, by omega⟩, roleNew (otherDir (initDir₂ M)),
                  T₁.nth (dirStep (otherDir (initDir₂ M)))),
                otherDir (otherDir (initDir₂ M))) := by
            rw [stateTwoBlankTM_trans, hTother _ (dirStep_ne_zero _)
              (by cases initDir₂ M <;> simp [dirStep, otherDir] <;> omega)]
            exact transTwoAux_rule1 M eQ _ _ (otherDir (initDir₂ M)) _
          exact stepB_keepBoot M m' htr ht5 ht1 hTb2 hTb1 hTother
            (by cases initDir₂ M <;> simp [dirStep] <;> omega)
            (by cases initDir₂ M <;> simp [dirStep, otherDir] <;> omega)
            (by cases initDir₂ M <;> simp [dirStep, otherDir]; omega)
  · rcases c₁ with ⟨st₁, T₁⟩; rcases c₂ with ⟨st₂, T₂⟩
    dsimp only at hq hY; subst hq hY
    rcases htr : M.trans q (T₁.nth 0) with ⟨_ | q', e', d'⟩
    · exact ⟨1, le_refl 1, stepB_halt M htr
        (by rw [stateTwoBlankTM_trans, hT0, transTwoAux_rule5, htr])⟩
    · have ht5 : (stateTwoBlankTM M).trans Y (T₂.nth 0) =
          (some d', (⟨(eQ q').1, by have := (eQ q').2; omega⟩, roleOld d', e'), d') := by
        rw [stateTwoBlankTM_trans, hT0, transTwoAux_rule5, htr]
      have ht1 : (stateTwoBlankTM M).trans d' (T₂.nth (dirStep d')) =
          (some (otherDir d'), (⟨1, by omega⟩, roleNew d', T₁.nth (dirStep d')),
            otherDir d') := by
        rw [stateTwoBlankTM_trans, hTother _ (dirStep_ne_zero d')]
        exact transTwoAux_rule1 M eQ _ _ d' _
      exact stepB_clean M htr ht5 ht1 fun i _ hind ↦ hTother _ (by omega)

private lemma relB_halt {Q E : Type*} [Fintype Q] [Inhabited E] (M : BiInfTM Q E)
    (c₁ : Cfg Q E) (c₂ : Cfg Turing.Dir (Sym2B (Fintype.card Q) E))
    (hR : RelB M c₁ c₂) : c₂.state = none ↔ c₁.state = none := by
  rcases hR with ⟨h1, h2⟩ | ⟨h1, _, h2, _⟩ | ⟨_, _, _, h1, h2, _⟩ | ⟨_, _, h1, h2, _⟩ <;>
    simp [h1, h2]

/-- Starting from the all-blank tape, `stateTwoBlankTM M` simulates `M`
faithfully via the overflow bootstrap, halts on the blank tape, and runs at least `M.time` steps.
-/
theorem stateTwoBlankTM_halts_and_time_le {Q E : Type*} [Fintype Q] [Inhabited E]
    (M : BiInfTM Q E) (h : M.HaltsOnBlank) :
    (stateTwoBlankTM M).HaltsOnBlank ∧ M.time ≤ (stateTwoBlankTM M).time :=
  haltsOnBlank_and_time_le_of_rel_sim (RelB M) (relB_init M)
    (fun _ _ hR hne ↦ relB_step M hR hne) (relB_halt M) h

/-- Busy Beaver lower bound from 2-state simulation: any blank-tape halting
machine `M` over `(Q, E)` satisfies
`M.time ≤ busyBeaver 2 (5 * Fintype.card E * (Fintype.card Q + 2))`. -/
theorem busyBeaver_stateTwo {Q E : Type*} [Fintype Q] [Fintype E] [Inhabited E]
    (M : BiInfTM Q E) (h : M.HaltsOnBlank) :
    M.time ≤ busyBeaver 2 (5 * Fintype.card E * (Fintype.card Q + 2)) := by
  have hsim := (stateTwoBlankTM_halts_and_time_le M h).2
  have hbb := time_le_busyBeaver (stateTwoBlankTM M)
  rw [card_turingDir, card_sym2B] at hbb
  exact hsim.trans hbb

end BlankSim

/-- Shannon 2-state Busy Beaver reduction inequality (all-blank initial tape): for all `1 ≤ n` and
`1 ≤ m`, `busyBeaver n m ≤ busyBeaver 2 (5 * m * (n + 2))`. -/
theorem busyBeaver_le_stateTwo {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    busyBeaver n m ≤ busyBeaver 2 (5 * m * (n + 2)) := by
  let _ : NeZero n := ⟨by omega⟩
  let _ : NeZero m := ⟨by omega⟩
  obtain ⟨M, hM⟩ := exists_time_eq_busyBeaver n m
  by_cases hhalt : M.HaltsOnBlank
  · rw [← hM]
    simpa only [Fintype.card_fin] using busyBeaver_stateTwo M hhalt
  · rw [← hM, BiInfTM.time_of_not_haltsOnBlank hhalt]
    exact Nat.zero_le _

end CslibFrontier.Computability.BusyBeaver
