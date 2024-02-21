/-
Copyright (c) 2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix
-/

/-
This module defines properties of the bitwise operations on Natural numbers.

It is primarily intended to support the bitvector library.
-/
import Std.Data.Nat.Basic
import Std.Tactic.Basic

namespace Nat

@[local simp]
private theorem one_div_two : 1/2 = 0 := by trivial

private theorem two_pow_succ_sub_succ_div_two : (2 ^ (n+1) - (x + 1)) / 2 = 2^n - (x/2 + 1) := by
  if h : x + 1 ≤ 2 ^ (n + 1) then
    apply fun x => (Nat.sub_eq_of_eq_add x).symm
    apply Eq.trans _
    apply Nat.add_mul_div_left _ _ Nat.zero_lt_two
    rw [← Nat.sub_add_comm h]
    rw [Nat.add_sub_assoc (by omega)]
    rw [Nat.pow_succ']
    rw [Nat.mul_add_div Nat.zero_lt_two]
    simp [show (2 * (x / 2 + 1) - (x + 1)) / 2 = 0 by omega]
  else
    rw [Nat.pow_succ'] at *
    omega

private theorem two_pow_succ_sub_one_div_two : (2 ^ (n+1) - 1) / 2 = 2^n - 1 :=
  two_pow_succ_sub_succ_div_two

private theorem two_mul_sub_one {n : Nat} (n_pos : n > 0) : (2*n - 1) % 2 = 1 := by
  match n with
  | 0 => contradiction
  | n + 1 => simp [Nat.mul_succ, Nat.mul_add_mod, mod_eq_of_lt]

/-! ### Preliminaries -/

/-! ### testBit -/

private theorem succ_mod_two : succ x % 2 = 1 - x % 2 := by
  induction x with
  | zero =>
    trivial
  | succ x hyp =>
    have p : 2 ≤ x + 2 := Nat.le_add_left _ _
    simp [Nat.mod_eq (x+2) 2, p, hyp]
    cases Nat.mod_two_eq_zero_or_one x with | _ p => simp [p]

private theorem testBit_succ_zero : testBit (x + 1) 0 = not (testBit x 0) := by
  simp [testBit_to_div_mod, succ_mod_two]
  cases Nat.mod_two_eq_zero_or_one x with | _ p =>
    simp [p]

/-! ### bitwise -/

/-! ### bitwise -/

@[local simp]
private theorem eq_0_of_lt_one (x : Nat) : x < 1 ↔ x = 0 :=
  Iff.intro
    (fun p =>
      match x with
      | 0 => Eq.refl 0
      | _+1 => False.elim (not_lt_zero _ (Nat.lt_of_succ_lt_succ p)))
    (fun p => by simp [p, Nat.zero_lt_succ])

private theorem eq_0_of_lt (x : Nat) : x < 2^ 0 ↔ x = 0 := eq_0_of_lt_one x

@[local simp]
private theorem zero_lt_pow (n : Nat) : 0 < 2^n := by
  induction n
  case zero => simp [eq_0_of_lt]
  case succ n hyp => simpa [pow_succ]

private theorem div_two_le_of_lt_two {m n : Nat} (p : m < 2 ^ succ n) : m / 2 < 2^n := by
  simp [div_lt_iff_lt_mul Nat.zero_lt_two]
  exact p
