/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn, Mario Carneiro
-/
import Std.Tactic.Lint.Misc

attribute [simp] cast_eq cast_heq

/-# iff -/

@[simp] theorem eq_iff_iff {p q : Prop} : (p = q) ↔ (p ↔ q) :=
  Iff.intro (fun e => Iff.intro e.mp e.mpr) propext

theorem iff_of_true (ha : a) (hb : b) : a ↔ b := ⟨fun _ => hb, fun _ => ha⟩

theorem iff_true_intro (h : a) : a ↔ True := iff_of_true h ⟨⟩

/-# and -/

@[simp] theorem and_imp : (a ∧ b → c) ↔ (a → b → c) :=
  Iff.intro (fun h ha hb => h ⟨ha, hb⟩) (fun h ⟨ha, hb⟩ => h ha hb)

@[simp] theorem not_and : ¬(a ∧ b) ↔ (a → ¬b) := and_imp

@[simp]
theorem and_not_self : ¬(a ∧ ¬a) | ⟨ha, hn⟩ => hn ha

@[simp]
theorem not_and_self : ¬(¬a ∧ a) | ⟨hn, ha⟩ => hn ha

@[simp] theorem and_self_left : a ∧ (a ∧ b) ↔ a ∧ b :=
  ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, h.1, h.2⟩⟩

@[simp] theorem and_self_right : (a ∧ b) ∧ b ↔ a ∧ b :=
  ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2⟩, h.2⟩⟩

/-# or -/

@[simp] theorem or_self_left : a ∨ (a ∨ b) ↔ a ∨ b := ⟨.rec .inl id, .rec .inl (.inr ∘ .inr)⟩

@[simp] theorem or_self_right : (a ∨ b) ∨ b ↔ a ∨ b := ⟨.rec id .inr, .rec (.inl ∘ .inl) .inr⟩

/-# implication -/

@[simp] theorem imp_self : (a → a) ↔ True := iff_true_intro id

@[simp] theorem imp_false : (a → False) ↔ ¬a := Iff.rfl

/-# ite -/

/-- Negation of the condition `P : Prop` in a `dite` is the same as swapping the branches. -/
@[simp] theorem dite_not (P : Prop) {_ : Decidable P}  (x : ¬P → α) (y : ¬¬P → α) :
    dite (¬P) x y = dite P (fun h => y (not_not_intro h)) x := by
  by_cases h : P <;> simp [h]

/-- Negation of the condition `P : Prop` in a `ite` is the same as swapping the branches. -/
@[simp] theorem ite_not (P : Prop) {_ : Decidable P} (x y : α) : ite (¬P) x y = ite P y x :=
  dite_not P (fun _ => x) (fun _ => y)

@[simp] theorem ite_true_same (p q : Prop) [Decidable p] : (if p then p else q) = (p ∨ q) := by
  by_cases h : p <;> simp [h]

@[simp] theorem ite_false_same (p q : Prop) [Decidable p] : (if p then q else p) = (p ∧ q) := by
  by_cases h : p <;> simp [h]

/-# Decidable -/

@[simp] theorem decide_eq_false_iff_not (p : Prop) {_ : Decidable p} : (decide p = false) ↔ ¬p :=
  ⟨of_decide_eq_false, decide_eq_false⟩

theorem decide_eq_true_iff (p : Prop) [Decidable p] : (decide p = true) ↔ p := by simp

@[simp] theorem decide_eq_decide {p q : Prop} {_ : Decidable p} {_ : Decidable q} :
    decide p = decide q ↔ (p ↔ q) := by
  apply Iff.intro
  · intro h
    rw [← decide_eq_true_iff p, h, decide_eq_true_iff]
    exact Iff.rfl
  · intro h
    simp [h]

@[simp] theorem Decidable.not_not [Decidable p] : ¬¬p ↔ p := ⟨of_not_not, not_not_intro⟩

namespace Decidable

/-- Simplify p ∨ ¬p -/
@[simp] abbrev or_not_self := em

@[simp] theorem not_or_self (p : Prop) [Decidable p] : ¬p ∨ p := by
  by_cases h : p <;> simp [h]

@[simp]
theorem decide_iff (p q : Prop) [Decidable p] [Decidable q] :
    (decide (p ↔ q)) = ((p : Bool) == (q : Bool)) := by
  by_cases g : p <;> by_cases h : q <;> simp [g, h, BEq.beq]

-- From Mathlib
@[simp]
theorem if_true_left_eq_or (p : Prop) [Decidable p] (f : Prop) :
    ite p True f ↔ p ∨ f := by by_cases h : p <;> simp [h]

-- From Mathlib
@[simp]
theorem if_false_left_eq_and (p : Prop) [Decidable p] (f : Prop) :
    ite p False f ↔ ¬p ∧ f := by by_cases h : p <;> simp [h]

-- From Mathlib
@[simp]
theorem if_true_right_eq_or (p : Prop) [Decidable p] (t : Prop) :
    ite p t True ↔ ¬p ∨ t := by by_cases h : p <;> simp [h]

-- From Mathlib
@[simp]
theorem if_false_right_eq_and (p : Prop) [Decidable p] (t : Prop) :
    ite p t False ↔ p ∧ t := by by_cases h : p <;> simp [h]

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

namespace Classical

/-- The Double Negation Theorem: `¬¬P` is equivalent to `P`.
The left-to-right direction, double negation elimination (DNE),
is classically true but not constructively. -/
@[simp] theorem not_not : ¬¬a ↔ a := Decidable.not_not

@[simp] theorem not_forall {p : α → Prop} : (¬∀ x, p x) ↔ ∃ x, ¬p x :=
  Decidable.not_forall

@[simp] theorem imp_iff_right_iff : (a → b ↔ b) ↔ a ∨ b := Decidable.imp_iff_right_iff

@[simp] theorem and_or_imp : a ∧ b ∨ (a → c) ↔ a → b ∨ c := Decidable.and_or_imp

end Classical

export Classical (imp_iff_right_iff and_or_imp)
