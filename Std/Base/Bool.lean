/-
Copyright (c) 2023 F. G. Dorais. No rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, F. G. Dorais
-/

/- In Std -/
@[simp] theorem beq_eq_false_iff_ne [BEq α] [LawfulBEq α]
    (a b : α) : (a == b) = false ↔ a ≠ b := by
  rw [ne_eq, ← beq_iff_eq a b]
  cases a == b <;> decide

/-
Added for critical pair for `¬((a != b) = true)`

1. `(a != b) = false` via `Bool.not_eq_true`
2. `a ≠ b` via `bne_iff_ne`

-/
@[simp] theorem bne_eq_false_iff_eq [BEq α] [LawfulBEq α]
    (a b : α) : (a != b) = false ↔ a = b := by
  rw [bne, ← beq_iff_eq a b]
  cases a == b <;> decide

/-
example (a b c : Bool) : ¬((a == b) = true) = c := by
  rw [Bool.not_eq_true (a == b)]

  simp [-beq_iff_eq, -Bool.beq_to_eq]
  admit
  -/
/-
t0 : ¬((a == b) = true)
t1 : ¬(a = b) from `t0` via `beq_iff_eq`

beq_iff_eq:

t1: ¬ (a = true)
e /
-/

/- In Std -/
/-
@[simp] theorem bne_eq_false_iff_ne [BEq α] [LawfulBEq α]
    (a b : α) : (a != b) = false ↔ a ≠ b := by
  rw [ne_eq, ← beq_iff_eq a b]
  cases a == b <;> decide
-/

namespace Bool

/- Instance in Std -/
instance (p : Bool → Prop) [inst : DecidablePred p] : Decidable (∀ x, p x) :=
  match inst true, inst false with
  | isFalse ht, _ => isFalse fun h => absurd (h _) ht
  | _, isFalse hf => isFalse fun h => absurd (h _) hf
  | isTrue ht, isTrue hf => isTrue fun | true => ht | false => hf

/- Instance in Std -/
instance (p : Bool → Prop) [inst : DecidablePred p] : Decidable (∃ x, p x) :=
  match inst true, inst false with
  | isTrue ht, _ => isTrue ⟨_, ht⟩
  | _, isTrue hf => isTrue ⟨_, hf⟩
  | isFalse ht, isFalse hf => isFalse fun | ⟨true, h⟩ => absurd h ht | ⟨false, h⟩ => absurd h hf

/-- De Morgan's law for boolean and -/
/- Simp in Mathlib -/
@[simp]
theorem not_and : ∀ (x y : Bool), (!(x && y)) = (!x || !y) := by decide

/-- De Morgan's law for boolean or -/
/- simp in Mathlib -/
@[simp]
theorem not_or : ∀ (x y : Bool), (!(x || y)) = (!x && !y) := by decide

/- `Bool.and_not_self` and `Bool.not_and_self` are both simp in std -/
@[simp] theorem and_not_self : ∀ (x : Bool), (x && !x) = false := by decide
@[simp] theorem not_and_self : ∀ (x : Bool), (!x && x) = false := by decide

/- `Bool.or_not_self` and `Bool.not_or_self` are both simp in std -/
@[simp] theorem or_not_self : ∀ (x : Bool), (x || !x) = true := by decide
@[simp] theorem not_or_self : ∀ (x : Bool), (!x || x) = true := by decide

/-
`Bool.and_self_left` and `Bool.and_self_right` are added for consistency with
`and_self_left` and `and_self_right` (simp theorems in Std).s
-/
@[simp] theorem and_self_left  : ∀(a b : Bool), (a && (a && b)) = (a && b) := by decide
@[simp] theorem and_self_right : ∀(a b : Bool), ((a && b) && b) = (a && b) := by decide

/-
`Bool.or_self_left` and `Bool.or_self_right` are added for consistency with
`or_self_left` and `or_self_right` (simp theorems in Std).
-/
@[simp] theorem or_self_left : ∀(a b : Bool), (a || (a || b)) = (a || b) := by decide
@[simp] theorem or_self_right : ∀(a b : Bool), ((a || b) || b) = (a || b) := by decide

/-
In Std as `not_xor_self` and `xor_not_self`.
-/
@[simp] theorem not_bne_self : ∀ (x : Bool), ((!x) != x) = true := by decide
@[simp] theorem bne_not_self : ∀ (x : Bool), (x != !x) = true := by decide

/- Added for constency with `and_not_self`, `or_not_self`, `bne_not_self` and related. -/
@[simp] theorem not_beq_self : ∀ (x : Bool), (!x == x) = false := by decide
@[simp] theorem beq_not_self : ∀ (x : Bool), (x == !x) = false := by decide

/- These were added for constency with `and_self_left` `or_self_left` and related. -/
@[simp] theorem beq_self_left (a b : Bool) : (a == (a == b)) = b := by revert a b ; decide
@[simp] theorem beq_self_right (a b : Bool) : ((a == b) == b) = a := by revert a b ; decide
@[simp] theorem bne_self_left (a b : Bool) : (a != (a != b)) = b := by revert a b ; decide
@[simp] theorem bne_self_right (a b : Bool) : ((a != b) != b) = a := by revert a b ; decide

/- In std as `not_xor_not`. -/
@[simp] theorem not_bne_not : ∀ (x y : Bool), ((!x) != (!y)) = (x != y) := by decide

/--
These two rules follow trivially by simp, but are needed to avoid non-termination
in false_eq and true_eq.
-/
@[simp] theorem false_eq_true : (false = true) = False := by simp
@[simp] theorem true_eq_false : (true = false) = False := by simp

-- The two lemmas below normalize terms with a constant to the
-- right-hand side but risk non-termination if `false_eq_true` and
-- `true_eq_false` are disabled.
@[simp low] theorem false_eq (b : Bool) : (false = b) = (b = false) := by
  cases b <;> simp

@[simp low] theorem true_eq (b : Bool) : (true = b) = (b = true) := by
  cases b <;> simp

/-# beq -/

/- simp rule `true_xor` in std -/
@[simp] theorem true_bne  (b : Bool) : (true  != b) = !b := by cases b <;> simp [BEq.beq]
/- simp rule `false_xor` in std -/
@[simp] theorem false_bne (b : Bool) : (false != b) =  b := by cases b <;> simp [BEq.beq]
/- simp rule `xor_true` in std -/
@[simp] theorem bne_true  (b : Bool) : (b != true)  = !b := by cases b <;> simp [BEq.beq]
/- simp rule `xor_false` in std -/
@[simp] theorem bne_false (b : Bool) : (b != false) =  b := by cases b <;> simp [BEq.beq]

/- Added for compat with `true_bne`. -/
@[simp] theorem true_beq  (b : Bool) : (true  == b) =  b := by cases b <;> simp [BEq.beq]
/- New simp rule-/
@[simp] theorem false_beq (b : Bool) : (false == b) = !b := by cases b <;> simp [BEq.beq]
/- New simp rule-/
@[simp] theorem beq_true  (b : Bool) : (b == true)  =  b := by cases b <;> simp [BEq.beq]
/- New simp rule-/
@[simp] theorem beq_false (b : Bool) : (b == false) = !b := by cases b <;> simp [BEq.beq]

/--
In Std as xor_assoc (not simp rule in std, but made one in Mathlib)
-/
@[simp]
theorem bne_assoc : ∀ (x y z : Bool), ((x != y) != z) = (x != (y != z)) := by decide

/--
In Std as xor_left_inj (simp rule)
-/
@[simp]
theorem bne_left_inj : ∀ (x y z : Bool), (x != y) = (x != z) ↔ y = z := by decide

/--
In Std as xor_right_inj (simp rule)
-/
@[simp]
theorem bne_right_inj : ∀ (x y z : Bool), (x != z) = (y != z) ↔ x = y := by decide

/-# bool to prop normal forms: b = true, b = false -/

/--
Theorem in base as simp `and_eq_true` using eq instead of `iff.

Also in Std as and_eq_true_iff
Also in Mathlib asBool.and_eq_true_eq_eq_true_and_eq_true.
-/
theorem and_eq_true_iff : ∀ (x y : Bool), (x && y) = true ↔ x = true ∧ y = true :=
  fun x y => Iff.of_eq (and_eq_true x y)

/--
Theorem in Mathlib asBool.or_eq_true_eq_eq_true_or_eq_true.
Also in Std as or_eq_true_iff

Made simp rule for parity with or_eq_false_iff.
-/
@[simp]
theorem or_eq_true_iff : ∀ (x y : Bool), (x || y) = true ↔ x = true ∨ y = true := by decide

/--
This is defined in Std, but also defined in Mathlib as a simp rule named
`Bool.and_eq_false_eq_eq_false_or_eq_false`.
-/
theorem and_eq_false_iff : ∀ (x y : Bool), (x && y) = false ↔ x = false ∨ y = false := by decide
/-
New simp rule that replaces `Bool.and_eq_false_eq_eq_false_or_eq_false` in
Mathlib due to confluence:

Consider the term: `¬((b && c) = true)`:

1. Reduces to `((b && c) = false)` via `Bool.not_eq_true`
2. Reduces to `¬(b = true ∧ c = true)` via `Bool.and_eq_true`.


1. Further reduces to `b = false ∨ c = false` via `Bool.and_eq_false_eq_eq_false_or_eq_false`.
2. Further reduces to `b = true → c = false` via `not_and` and `Bool.not_eq_true`.
-/
@[simp]
theorem and_eq_false_imp : ∀ (x y : Bool), (x && y) = false ↔ (x = true → y = false) := by decide

/--
Simp rule in Mathlib as Bool.or_eq_false_eq_eq_false_and_eq_false.
Also non-simp rule in Std as or_eq_false_iff
-/
@[simp]
theorem or_eq_false_iff : ∀ (x y : Bool), (x || y) = false ↔ x = false ∧ y = false := by decide


/- Mathlib simp rule. -/
@[simp]
theorem not_eq_not : ∀ {a b : Bool}, ¬a = !b ↔ a = b := by decide

/- Mathlib simp rule. -/
@[simp]
theorem not_not_eq : ∀ {a b : Bool}, ¬(!a) = b ↔ a = b := by decide

-- Note. We push coercions to atoms so we can reduce the need for reasoning
-- about mixed Prop/Bool formulas.  As part of this, there are simp lemmas
-- that automatically distribute (_ = true) and (_ = false) over operations
-- because `(_ = true)` is introduced implicitly when coericing a `Bool` to a
-- `Prop` and `(_ = false)` arrises from `simp` rules on negation.

/-# decidability -/

/- Theorem in Mathlib -/
@[simp]
protected theorem decide_coe (b : Bool) [h : Decidable (b = true)] : @decide (b = true) h = b := by
  cases b
  · exact decide_eq_false <| λ j => by cases j
  · exact decide_eq_true <| rfl

/-
 `decide_eq_false` added for confluence of `decide (¬(a = false))`.

Reduces to:
1. `!decide (a = false)` via `decide_not`.
2. `decide (a = true)` via `Bool.not_eq_false`

These will both reduce to `a` using `decide_coe` and `decide_eq_false`.
-/

/- See note above -/
@[simp]
protected theorem decide_eq_false (b : Bool) : decide (b = false) = !b := by
  cases b <;> simp

/-
Mathlib simp rule
-/
@[simp]
theorem decide_and (p q : Prop) [Decidable p] [Decidable q] : decide (p ∧ q) = (p && q) := by
  by_cases p <;> by_cases q <;> simp [*]

/-
Mathlib simp rule
-/
@[simp]
theorem decide_or (p q : Prop) [Decidable p] [Decidable q] : decide (p ∨ q) = (p || q) := by
  by_cases p <;> by_cases q <;> simp [*]

/-
This is a new rule.  Added for consistency with decide_and/decide_or.
-/
@[simp]
theorem decide_iff_dist (p q : Prop) [Decidable p] [Decidable q] :
    (decide (p ↔ q)) = ((p : Bool) == (q : Bool)) := by
  by_cases g : p <;> by_cases h : q <;> simp [g, h, BEq.beq]

/- ## Simp lemmas for Bool to Prop normal forms: `b = true`, `b = false`-/

/- New simp rule -/
@[simp]
theorem coe_iff_coe : ∀(a b : Bool), (a ↔ b) ↔ a = b := by decide

/- New simp rule -/
@[simp]
theorem coe_true_iff_false : ∀(a b : Bool), (a ↔ b = false) ↔ a = (!b) := by decide

/- New simp rule -/
@[simp]
theorem coe_false_iff_true : ∀(a b : Bool), (a = false ↔ b) ↔ (!a) = b := by decide

/- New simp rule -/
@[simp]
theorem coe_false_iff_false : ∀(a b : Bool), (a = false ↔ b = false) ↔ (!a) = (!b) := by decide

/-# ite -/

/- Added for compatibility with `if_true_left` (Mathlib simp rule) -/
@[simp]
theorem if_true_left  (p : Prop) [Decidable p] (f : Bool) :
    (ite p true f) = (p || f) := by by_cases h : p <;> simp [h]

/- Added for compatibility with `if_false_left` (Mathlib simp rule) -/
@[simp]
theorem if_false_left  (p : Prop) [Decidable p] (f : Bool) :
    (ite p false f) = (!p && f) := by by_cases h : p <;> simp [h]

/- Added for compatibility with `if_true_right` (Mathlib simp rule) -/
@[simp]
theorem if_true_right  (p : Prop) [Decidable p] (t : Bool) :
    (ite p t true) = (!(p : Bool) || t) := by by_cases h : p <;> simp [h]

/- Added for compatibility with `if_false_right` (Mathlib simp rule) -/
@[simp]
theorem if_false_right  (p : Prop) [Decidable p] (t : Bool) :
    (ite p t false) = (p && t) := by by_cases h : p <;> simp [h]

/-
Defined in Mathlib (simp rule)
-/
@[simp] theorem ite_eq_true_distrib (p : Prop) [Decidable p] (t f : Bool) :
    (ite p t f = true) = ite p (t = true) (f = true) := by
  by_cases h : p <;> simp [h]

/-
Defined in Mathlib (simp rule)
-/
@[simp] theorem ite_eq_false_distrib (p : Prop) [Decidable p] (t f : Bool) :
    (ite p t f = false) = ite p (t = false) (f = false) := by
  by_cases h : p <;> simp [h]

/-
`not_if_prop_coerce_true` and `not_if_prop_coerce_false` are added
for non-confluence.  The motivating example for `not_if_prop_coerce_true`
is `¬((if u then b else c) = true)`.

This reduces to:
1. `¬((if u then (b = true) else (c = true))` via `ite_eq_true_distrib`
2. `(if u then b c) = false)` via `Bool.not_eq_true`.

Similar logic holds for `¬((if u then b else c) = false)` and related
lemmas.
-/

@[simp]
theorem not_ite_eq_true_eq_true (p : Prop) [Decidable p] (b c : Bool) :
  ¬(ite p (b = true) (c = true)) ↔ (ite p (b = false) (c = false)) := by
  by_cases h : p <;> simp [h]

@[simp]
theorem not_ite_eq_false_eq_false (p : Prop) [Decidable p] (b c : Bool) :
  ¬(ite p (b = false) (c = false)) ↔ (ite p (b = true) (c = true)) := by
  by_cases h : p <;> simp [h]

/- Added for consistency with `not_ite_eq_true_eq_true` -/
@[simp]
theorem not_ite_eq_true_eq_false (p : Prop) [Decidable p] (b c : Bool) :
  ¬(ite p (b = true) (c = false)) ↔ (ite p (b = false) (c = true)) := by
  by_cases h : p <;> simp [h]

/- Added for consistency with `not_ite_eq_true_eq_true` -/
@[simp]
theorem not_ite_eq_false_eq_true (p : Prop) [Decidable p] (b c : Bool) :
  ¬(ite p (b = false) (c = true)) ↔ (ite p (b = true) (c = false)) := by
  by_cases h : p <;> simp [h]

/-! cond -/

theorem cond_eq_ite {α} (b : Bool) (t e : α) : cond b t e = if b then t else e := by
  cases b <;> simp

/- Mathlib simp rule -/
@[simp]
theorem cond_not {α : Type _} (b : Bool) (t e : α) : cond (!b) t e = cond b e t := by cases b <;> rfl

/- Mathlib simp rule-/
@[simp]
theorem cond_self {α} (c : Bool) (t : α) : cond c t t = t := by cases c <;> simp

/-
This is a simp rule in Mathlib, but results in non-confluence that is
difficult to fix as decide distributes over propositions.

A possible fix would be to completely simplify away `cond`, but that
is not taken since it could result in major rewriting of code that is
otherwise purely about `Bool`.
-/
theorem cond_decide {α} (p : Prop) [Decidable p] (t e : α) :
    cond (decide p) t e = if p then t else e := by
  simp [cond_eq_ite]

/-
In lieu of cond_decide or cond_eq_ite being simp, we have more restained simp rules
`cond_eq_ite_iff` and `ite_eq_cond_iff`.
-/

@[simp]
theorem cond_eq_ite_iff {α : Type _} (a : Bool) (p : Prop) [Decidable p] (x y u v : α) :
  (cond a x y = ite p u v) ↔ ite a x y = ite p u v := by
  simp [Bool.cond_eq_ite]

@[simp]
theorem ite_eq_cond_iff {α : Type _} (p : Prop) [Decidable p] (a : Bool) (x y u v : α) :
  (ite p x y = cond a u v) ↔ ite p x y = ite a u v := by
  simp [Bool.cond_eq_ite]

/--
New rule (added for consistency with ite_eq_true_distrib)
-/
@[simp] theorem cond_eq_true_distrib (c t f : Bool) :
    (cond c t f = true) = ite (c = true) (t = true) (f = true) := by
  simp [Bool.cond_eq_ite]

/--
New rule (added for consistency with ite_eq_false_distrib)
-/
@[simp] theorem cond_eq_false_distrib (c t f : Bool) :
    (cond c t f = false) = ite (c = true) (t = false) (f = false) := by
  simp [Bool.cond_eq_ite]

/- Mathlib clone -/
protected theorem cond_true {α : Type u} {a b : α} : cond true a b = a := cond_true a b

/- Mathlib clone -/
protected theorem cond_false {α : Type u} {a b : α} : cond false a b = b := cond_false a b

/- Added for parity with `if_true_left` -/
@[simp]
theorem cond_true_left (c f : Bool) : (cond c true f) = (c || f) := by simp [Bool.cond_eq_ite]

/- Added for parity with `if_false_left` -/
@[simp]
theorem cond_false_left  (c f : Bool) : (cond c false f) = (!c && f) := by simp [Bool.cond_eq_ite]

/- Added for parity with `if_true_right` -/
@[simp]
theorem cond_true_right   (c t : Bool) : (cond c t true) = (!c || t) := by simp [Bool.cond_eq_ite]

/- Added for parity with `if_false_right` -/
@[simp]
theorem cond_false_right (c t : Bool) : (cond c t false) = (c && t) := by simp [Bool.cond_eq_ite]

/- New simp rule-/
@[simp]
theorem cond_true_same (c b : Bool) : cond c c b = (c || b) := by cases c <;> simp

/- New simp rule-/
@[simp]
theorem cond_false_same (c b : Bool) : cond c b c = (c && b) := by cases c <;> simp

/-# misc -/

@[simp]
theorem default_bool : default = false := rfl

-- @[simp] FIXME
theorem eq_false_or_eq_implies (a : Bool) (p : Prop) : (a = false ∨ p) ↔ ((a = true) → p) := by
  cases a <;> simp

-- @[simp] FIXME
theorem not_beq (b c : Bool) : (!(b == c)) = (b != c) := by
  cases b <;> cases c <;> simp

-- @[simp] FIXME
theorem not_bne (b c : Bool) : (!(b != c)) = (b == c) := by
  cases b <;> cases c <;> simp

-- @[simp] FIXME
theorem decide_eq (b c : Bool) : decide (b = c) = (b == c) := by
  cases b <;> cases c <;> simp
