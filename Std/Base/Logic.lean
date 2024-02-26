/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn, Mario Carneiro
-/
import Std.Tactic.Lint.Misc

/- Defined in core; made simp in Mathlib-/
attribute [simp] cast_eq cast_heq

/-# iff -/

/- simp rule in std-/
@[simp] theorem eq_iff_iff {p q : Prop} : (p = q) ↔ (p ↔ q) :=
  Iff.intro Iff.of_eq  propext

theorem iff_of_true (ha : a) (hb : b) : a ↔ b := ⟨fun _ => hb, fun _ => ha⟩

theorem iff_true_intro (h : a) : a ↔ True := iff_of_true h ⟨⟩

/-# implication -/

/- simp rule in std-/
@[simp] theorem imp_self : (a → a) ↔ True := iff_true_intro id

/- simp rule in std-/
@[simp] theorem imp_not_self : (a → ¬a) ↔ ¬a := ⟨fun h ha => h ha ha, fun h _ => h⟩

/- non-simp rule in std; made simp in Mathlib. -/
@[simp] theorem imp_false : (a → False) ↔ ¬a := Iff.rfl

/-# and -/

/- simp rule in std-/
@[simp] theorem and_imp : (a ∧ b → c) ↔ (a → b → c) :=
  Iff.intro (fun h ha hb => h ⟨ha, hb⟩) (fun h ⟨ha, hb⟩ => h ha hb)

/- simp rule in std -/
@[simp] theorem not_and : ¬(a ∧ b) ↔ (a → ¬b) := and_imp

/- simp rule in std -/
@[simp]
theorem and_not_self : ¬(a ∧ ¬a) | ⟨ha, hn⟩ => hn ha

/- simp rule in std -/
@[simp]
theorem not_and_self : ¬(¬a ∧ a) | ⟨hn, ha⟩ => hn ha

/- simp rule in std -/
@[simp] theorem and_self_left : a ∧ (a ∧ b) ↔ a ∧ b :=
  ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, h.1, h.2⟩⟩

/- simp rule in std -/
@[simp] theorem and_self_right : (a ∧ b) ∧ b ↔ a ∧ b :=
  ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2⟩, h.2⟩⟩

theorem and_comm : a ∧ b ↔ b ∧ a := And.comm

/-# or -/


theorem or_imp : (a ∨ b → c) ↔ (a → c) ∧ (b → c) :=
  ⟨fun h => ⟨h ∘ .inl, h ∘ .inr⟩, fun ⟨ha, hb⟩ => Or.rec ha hb⟩

/-
This is made simp for confluence with `¬((b || c) = true)`:

Critical pair:
1. `¬(b = true ∨ c = true)` via `Bool.or_eq_true`.
2. `(b || c = false)` via `Bool.not_eq_true` which then
   reduces to `b = false ∧ c = false` via Mathlib simp lemma
   `Bool.or_eq_false_eq_eq_false_and_eq_false`.
-/
@[simp]
theorem not_or : ¬(p ∨ q) ↔ ¬p ∧ ¬q := or_imp

/- simp rule in std -/
@[simp] theorem or_self_left : a ∨ (a ∨ b) ↔ a ∨ b := ⟨.rec .inl id, .rec .inl (.inr ∘ .inr)⟩

/- simp rule in std -/
@[simp] theorem or_self_right : (a ∨ b) ∨ b ↔ a ∨ b := ⟨.rec id .inr, .rec (.inl ∘ .inl) .inr⟩

theorem Or.resolve_left {a b : Prop} (h: a ∨ b) (na : ¬a) : b := h.elim (absurd · na) id

/-- Construct a non-Prop by cases on an `Or`, when the left conjunct is decidable. -/
protected def Or.by_cases [Decidable p] {α : Sort u} (h : p ∨ q) (h₁ : p → α) (h₂ : q → α) : α :=
  if hp : p then h₁ hp else h₂ (h.resolve_left hp)


/-# ite -/

/-- Negation of the condition `P : Prop` in a `dite` is the same as swapping the branches. -/
/- simp rule in std -/
@[simp] theorem dite_not (P : Prop) {_ : Decidable P}  (x : ¬P → α) (y : ¬¬P → α) :
    dite (¬P) x y = dite P (fun h => y (not_not_intro h)) x := by
  by_cases h : P <;> simp [h]

/-- Negation of the condition `P : Prop` in a `ite` is the same as swapping the branches. -/
/- simp rule in std -/
@[simp] theorem ite_not (P : Prop) {_ : Decidable P} (x y : α) : ite (¬P) x y = ite P y x :=
  dite_not P (fun _ => x) (fun _ => y)

/- New simp rule -/
@[simp] theorem ite_true_same (p q : Prop) [Decidable p] : (if p then p else q) = (p ∨ q) := by
  by_cases h : p <;> simp [h]

/- New simp rule -/
@[simp] theorem ite_false_same (p q : Prop) [Decidable p] : (if p then q else p) = (p ∧ q) := by
  by_cases h : p <;> simp [h]

/- in std (not simp)  -/
theorem iff_not_self : ¬(a ↔ ¬a) | H => let f h := H.1 h h; f (H.2 f)

/- simp rule in std -/
@[simp] theorem not_iff_self : ¬(¬a ↔ a) | H => iff_not_self H.symm

theorem and_iff_left_of_imp (h : a → b) : (a ∧ b) ↔ a :=
  ⟨And.left, fun ha => ⟨ha, h ha⟩⟩

theorem and_iff_right_of_imp (h : b → a) : (a ∧ b) ↔ b :=
  ⟨And.right, fun hb => ⟨h hb, hb⟩⟩

/- simp rule in std -/
@[simp] theorem and_iff_left_iff_imp : ((a ∧ b) ↔ a) ↔ (a → b) :=
  ⟨fun h ha => (h.2 ha).2, and_iff_left_of_imp⟩

/- simp rule in std -/
@[simp] theorem and_iff_right_iff_imp : ((a ∧ b) ↔ b) ↔ (b → a) :=
  ⟨fun h ha => (h.2 ha).1, and_iff_right_of_imp⟩

/- simp rule in std -/
@[simp] theorem iff_self_and : (p ↔ p ∧ q) ↔ (p → q) := by
  rw [@Iff.comm p, and_iff_left_iff_imp]
  exact Iff.refl _

/- simp rule in std -/
@[simp] theorem iff_and_self : (p ↔ q ∧ p) ↔ (p → q) := by
  rw [and_comm, iff_self_and]
  exact Iff.refl _

theorem and_congr_right (h : a → (b ↔ c)) : a ∧ b ↔ a ∧ c :=
  ⟨fun ⟨ha, hb⟩ => ⟨ha, (h ha).1 hb⟩, fun ⟨ha, hb⟩ => ⟨ha, (h ha).2 hb⟩⟩

theorem and_congr_left (h : c → (a ↔ b)) : a ∧ c ↔ b ∧ c :=
  and_comm.trans <| (and_congr_right h).trans and_comm

/- simp rule in std -/
@[simp] theorem and_congr_right_iff : (a ∧ b ↔ a ∧ c) ↔ (a → (b ↔ c)) :=
  ⟨fun h ha => by simp [ha] at h; exact h, and_congr_right⟩

/- simp rule in std -/
@[simp] theorem and_congr_left_iff : (a ∧ c ↔ b ∧ c) ↔ c → (a ↔ b) := by
  simp only [and_comm, ← and_congr_right_iff]

/-# Decidable -/

/--
simp rule in std
-/
@[simp] theorem decide_eq_false_iff_not (p : Prop) {_ : Decidable p} : (decide p = false) ↔ ¬p :=
  ⟨of_decide_eq_false, decide_eq_false⟩

theorem decide_eq_true_iff (p : Prop) [Decidable p] : (decide p = true) ↔ p := by simp

/--
simp rule in std
-/
@[simp] theorem decide_eq_decide {p q : Prop} {_ : Decidable p} {_ : Decidable q} :
    decide p = decide q ↔ (p ↔ q) := by
  apply Iff.intro
  · intro h
    rw [← decide_eq_true_iff p, h, decide_eq_true_iff]
    exact Iff.rfl
  · intro h
    simp [h]

/-
Defined in std.
We are making simp here.

Mathlib makes Classical.not_not simp
-/
@[simp] theorem Decidable.not_not [Decidable p] : ¬¬p ↔ p := ⟨of_not_not, not_not_intro⟩

/- Note.  This instance overlaps with `instDecidableNot` -/
instance forall_prop_decidable {p} (P : p → Prop)
  [Decidable p] [∀ h, Decidable (P h)] : Decidable (∀ h, P h) :=
if h : p then
  decidable_of_decidable_of_iff ⟨fun h2 _ => h2, fun al => al h⟩
else isTrue fun h2 => absurd h2 h

instance exists_prop_decidable {p} (P : p → Prop)
  [Decidable p] [∀ h, Decidable (P h)] : Decidable (∃ h, P h) :=
if h : p then
  decidable_of_decidable_of_iff ⟨fun h2 => ⟨h, h2⟩, fun ⟨_, h2⟩ => h2⟩
else isFalse fun ⟨h', _⟩ => h h'

/- Mathlib simp rule -/
@[simp]
theorem if_true_left {p q : Prop} [Decidable p] :
    ite p True q ↔ p ∨ q := by by_cases h : p <;> simp [h]

/- Mathlib simp rule -/
@[simp]
theorem if_false_left {p q : Prop} [Decidable p] :
    ite p False q ↔ ¬p ∧ q := by by_cases h : p <;> simp [h]

/- Mathlib simp rule -/
@[simp]
theorem if_true_right {p q : Prop} [Decidable p] :
    ite p q True ↔ ¬p ∨ q := by by_cases h : p <;> simp [h]

/- Mathlib simp rule -/
@[simp]
theorem if_false_right {p q : Prop} [Decidable p] :
    ite p q False ↔ p ∧ q := by by_cases h : p <;> simp [h]
namespace Decidable

/-- Excluded middle.  Added as alias for Decidable.em -/
abbrev or_not_self := em

/-- Excluded middle commuted.  Added as alias for Decidable.em -/
theorem not_or_self (p : Prop) [Decidable p] : ¬p ∨ p := by
  by_cases h : p <;> simp [h]


/-
Defined in Std and made simp in Mathlib.
-/
@[simp]
theorem not_imp_self [Decidable a] : (¬a → a) ↔ a :=
  Iff.intro (fun f => if h : a then h else f h) (fun h _ => h)

end Decidable

theorem not_forall_of_exists_not {p : α → Prop} : (∃ x, ¬p x) → ¬∀ x, p x
  | ⟨x, hn⟩, h => hn (h x)

theorem Decidable.not_imp_symm [Decidable a] (h : ¬a → b) (hb : ¬b) : a :=
  byContradiction <| hb ∘ h

protected theorem Decidable.not_forall {p : α → Prop} [Decidable (∃ x, ¬p x)]
    [∀ x, Decidable (p x)] : (¬∀ x, p x) ↔ ∃ x, ¬p x :=
  Iff.intro
    (Decidable.not_imp_symm fun nx x => Decidable.not_imp_symm (fun h => ⟨x, h⟩) nx)
    not_forall_of_exists_not

@[nolint unusedArguments]
theorem imp_intro {α β : Prop} (h : α) : β → α := fun _ => h

theorem imp_iff_right {a : Prop} (ha : a) : (a → b) ↔ b := ⟨fun f => f ha, imp_intro⟩

theorem Or.imp (f : a → c) (g : b → d) (h : a ∨ b) : c ∨ d := h.elim (inl ∘ f) (inr ∘ g)

theorem Or.imp_left (f : a → b) : a ∨ c → b ∨ c := .imp f id

theorem Or.imp_right (f : b → c) : a ∨ b → a ∨ c := .imp id f

theorem Decidable.imp_iff_right_iff [Decidable a] : (a → b ↔ b) ↔ a ∨ b :=
  ⟨fun H => (Decidable.em a).imp_right fun ha' => H.1 fun ha => (ha' ha).elim,
   fun H => H.elim imp_iff_right fun hb => iff_of_true (fun _ => hb) hb⟩

theorem false_imp_iff (a : Prop) : (False → a) ↔ True := iff_true_intro False.elim

theorem true_imp_iff (α : Prop) : (True → α) ↔ α := ⟨fun h => h trivial, fun h _ => h⟩

theorem Decidable.and_or_imp [Decidable a] : a ∧ b ∨ (a → c) ↔ a → b ∨ c :=
  if ha : a then by simp only [ha, true_and, true_imp_iff]
  else by simp only [ha, false_or, false_and, false_imp_iff]

/-
/--
This generalize decide_not to accept an arbitrary proof `Decidable (Not u)`

`decide_not` is simp in core.
-/
theorem decide_not' (u : Prop) [uvd : Decidable (Not u)] [ax : Decidable u]
  : @Decidable.decide (Not u) uvd = !(@decide u ax) :=
  if h : u then by
    simp [h]
  else by
    simp [h]
-/

/-
New theorem

Added for addressing issue where `decide (not u)` would not simplify if
created from `u -> False` and `instDecidableForAll` or `forall_prop_deciable`
provided instance.
-/
theorem decide_forall_prop_decidable (u : Prop) (h : u → Prop) [ax : Decidable u]
    [bx : ∀(a : u), Decidable (h a)]
  : @Decidable.decide (no_index (∀ (a : u), h a)) (@forall_prop_decidable u h ax bx)
     = if a : u then decide (h a) else true :=
  if h : u then by
    simp only [h, dite_true, decide_eq_decide]
    exact Iff.intro (fun p => p True.intro) (fun p _ => p)
  else by
    simp only [h, dite_false, decide_eq_true_eq]
    intro p
    contradiction

/--
Added for overlap with `imp_false` and `decide_not`
-/
@[simp]
theorem decide_not' {u : Prop} {g : Decidable u} {h : Decidable (Not u)}
    : decide (Not u) = !(decide u) :=
  match g with
  | isTrue p => by
    simp [p]
  | isFalse p => by
    match h with
    | isTrue q =>
      simp [p, q, decide]
    | isFalse q =>
      contradiction

/-
`decide_implies` simp justification.

We have a critical pair from `decide (¬(p ∧ q))`:

 1. `decide (p → ¬q)` via `not_and` (in Std)
 2. `!decide (p ∧ q)` via `decide_not` (in Init) This further refines to
    `!(decide p) || !(decide q)` via `Bool.decide_and` (in Mathlib) and
    `Bool.not_and` (made simp in Mathlib).

We introduce `decide_implies` below and then both normalize to
`!(decide p) || !(decide q)`.
-/
@[simp]
theorem decide_implies (u v : Prop)
    {duv : Decidable (u → v)} {du : Decidable u} {dv : u → Decidable v}
  : decide (u → v) =
    if h : u then
      @decide v (dv h)
    else
      True :=
  if h : u then by
    simp [h]
  else by
    simp [h]

@[simp]
theorem decide_ite (u : Prop) {du : Decidable u} (p q : Prop)
      {dpq : Decidable (ite u p q)} {dp : Decidable p} {dq : Decidable q} :
    decide (ite u p q) = ite u (decide p) (decide q) := by
  by_cases h : u <;> simp [h]

theorem not_imp_self [Decidable a] : ¬a → a ↔ a := Decidable.not_imp_self

theorem Decidable.of_not_imp [Decidable a] (h : ¬(a → b)) : a :=
  if g : a then g else False.elim (h (False.elim ∘ g))

theorem not_of_not_imp {a : Prop} : ¬(a → b) → ¬b := mt fun h _ => h

theorem not_imp_of_and_not : a ∧ ¬b → ¬(a → b)
  | ⟨ha, hb⟩, h => hb <| h ha

theorem Decidable.not_imp_iff_and_not [Decidable a] : ¬(a → b) ↔ a ∧ ¬b :=
  Iff.intro (fun h => And.intro (of_not_imp h) (not_of_not_imp h))
            not_imp_of_and_not

namespace Classical

/-- The Double Negation Theorem: `¬¬P` is equivalent to `P`.
The left-to-right direction, double negation elimination (DNE),
is classically true but not constructively. -/
/- Scoped simp rule in Std; global in Mathlib. -/
@[simp] theorem not_not : ¬¬a ↔ a := Decidable.not_not

@[simp]
theorem not_imp : ¬(a → b) ↔ a ∧ ¬b := Decidable.not_imp_iff_and_not

/-
simp rule in Std

This is given low precedence so `not_imp` gets priority.
-/
@[simp low] theorem not_forall {p : α → Prop} : (¬∀ x, p x) ↔ ∃ x, ¬p x :=
  Decidable.not_forall

/- Simp rule in Mathlib in root namespace. -/
@[simp] theorem imp_iff_right_iff : (a → b ↔ b) ↔ a ∨ b := Decidable.imp_iff_right_iff

/- Simp rule in Mathlib in root namespace. -/
@[simp] theorem and_or_imp : a ∧ b ∨ (a → c) ↔ a → b ∨ c := Decidable.and_or_imp

end Classical

/- Export for Mathlib compat. -/
export Classical (imp_iff_right_iff and_or_imp not_imp)

@[simp]
theorem imp_and_neg_imp_iff (p q : Prop) : (p → q) ∧ (¬p → q) ↔ q :=
  Iff.intro (fun (a : _ ∧ _) => (Classical.em p).rec a.left a.right)
            (fun a => And.intro (fun _ => a) (fun _ => a))

-- FIXME: Triage

/-
#print imp_iff_or_not
#print imp_iff_or_not
#print not_not
#print or_and_left
#print not_and_self_iff
#print or_false_iff

@[simp]
theorem imp_and_neg_imp_iff (p q : Prop) : (p → q) ∧ (¬p → q) ↔ q :=

  rw [imp_iff_or_not, imp_iff_or_not, not_not, ← or_and_left, not_and_self_iff, or_false_iff]
-/

@[simp]
theorem eq_mp_eq_cast (h : α = β) : Eq.mp h = cast h :=
  rfl

@[simp]
theorem eq_mpr_eq_cast (h : α = β) : Eq.mpr h = cast h.symm :=
  rfl

@[simp] theorem cast_cast : ∀ (ha : α = β) (hb : β = γ) (a : α),
    cast hb (cast ha a) = cast (ha.trans hb) a
  | rfl, rfl, _ => rfl

@[simp] theorem eq_true_eq_id : Eq True = id := by
  funext _; simp only [true_iff, id.def, eq_iff_iff]
