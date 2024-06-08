/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Mario Carneiro, Gabriel Ebner
-/
import Batteries.Data.List.Lemmas
import Batteries.Data.Array.Basic
import Batteries.Tactic.SeqFocus
import Batteries.Util.ProofWanted

namespace Array

theorem forIn_eq_data_forIn [Monad m]
    (as : Array α) (b : β) (f : α → β → m (ForInStep β)) :
    forIn as b f = forIn as.data b f := by
  let rec loop : ∀ {i h b j}, j + i = as.size →
      Array.forIn.loop as f i h b = forIn (as.data.drop j) b f
    | 0, _, _, _, rfl => by rw [List.drop_length]; rfl
    | i+1, _, _, j, ij => by
      simp only [forIn.loop, Nat.add]
      have j_eq : j = size as - 1 - i := by simp [← ij, ← Nat.add_assoc]
      have : as.size - 1 - i < as.size := j_eq ▸ ij ▸ Nat.lt_succ_of_le (Nat.le_add_right ..)
      have : as[size as - 1 - i] :: as.data.drop (j + 1) = as.data.drop j := by
        rw [j_eq]; exact List.get_cons_drop _ ⟨_, this⟩
      simp only [← this, List.forIn_cons]; congr; funext x; congr; funext b
      rw [loop (i := i)]; rw [← ij, Nat.succ_add]; rfl
  conv => lhs; simp only [forIn, Array.forIn]
  rw [loop (Nat.zero_add _)]; rfl

/-! ### zipWith / zip -/

theorem zipWith_eq_zipWith_data (f : α → β → γ) (as : Array α) (bs : Array β) :
    (as.zipWith bs f).data = as.data.zipWith f bs.data := by
  let rec loop : ∀ (i : Nat) cs, i ≤ as.size → i ≤ bs.size →
      (zipWithAux f as bs i cs).data = cs.data ++ (as.data.drop i).zipWith f (bs.data.drop i) := by
    intro i cs hia hib
    unfold zipWithAux
    by_cases h : i = as.size ∨ i = bs.size
    case pos =>
      have : ¬(i < as.size) ∨ ¬(i < bs.size) := by
        cases h <;> simp_all only [Nat.not_lt, Nat.le_refl, true_or, or_true]
      -- Cleaned up aesop output below
      simp_all only [Nat.not_lt]
      cases h <;> [(cases this); (cases this)]
      · simp_all only [Nat.le_refl, Nat.lt_irrefl, dite_false, List.drop_length,
                      List.zipWith_nil_left, List.append_nil]
      · simp_all only [Nat.le_refl, Nat.lt_irrefl, dite_false, List.drop_length,
                      List.zipWith_nil_left, List.append_nil]
      · simp_all only [Nat.le_refl, Nat.lt_irrefl, dite_false, List.drop_length,
                      List.zipWith_nil_right, List.append_nil]
        split <;> simp_all only [Nat.not_lt]
      · simp_all only [Nat.le_refl, Nat.lt_irrefl, dite_false, List.drop_length,
                      List.zipWith_nil_right, List.append_nil]
        split <;> simp_all only [Nat.not_lt]
    case neg =>
      rw [not_or] at h
      have has : i < as.size := Nat.lt_of_le_of_ne hia h.1
      have hbs : i < bs.size := Nat.lt_of_le_of_ne hib h.2
      simp only [has, hbs, dite_true]
      rw [loop (i+1) _ has hbs, Array.push_data]
      have h₁ : [f as[i] bs[i]] = List.zipWith f [as[i]] [bs[i]] := rfl
      let i_as : Fin as.data.length := ⟨i, has⟩
      let i_bs : Fin bs.data.length := ⟨i, hbs⟩
      rw [h₁, List.append_assoc]
      congr
      rw [← List.zipWith_append (h := by simp), getElem_eq_data_get, getElem_eq_data_get]
      show List.zipWith f ((List.get as.data i_as) :: List.drop (i_as + 1) as.data)
        ((List.get bs.data i_bs) :: List.drop (i_bs + 1) bs.data) =
        List.zipWith f (List.drop i as.data) (List.drop i bs.data)
      simp only [List.get_cons_drop]
    termination_by as.size - i
  simp [zipWith, loop 0 #[] (by simp) (by simp)]

theorem size_zipWith (as : Array α) (bs : Array β) (f : α → β → γ) :
    (as.zipWith bs f).size = min as.size bs.size := by
  rw [size_eq_length_data, zipWith_eq_zipWith_data, List.length_zipWith]

theorem zip_eq_zip_data (as : Array α) (bs : Array β) :
    (as.zip bs).data = as.data.zip bs.data :=
  zipWith_eq_zipWith_data Prod.mk as bs

theorem size_zip (as : Array α) (bs : Array β) :
    (as.zip bs).size = min as.size bs.size :=
  as.size_zipWith bs Prod.mk

/-! ### filter -/

theorem size_filter_le (p : α → Bool) (l : Array α) :
    (l.filter p).size ≤ l.size := by
  simp only [← data_length, filter_data]
  apply List.length_filter_le

/-! ### join -/

@[simp] theorem join_data {l : Array (Array α)} : l.join.data = (l.data.map data).join := by
  dsimp [join]
  simp only [foldl_eq_foldl_data]
  generalize l.data = l
  have : ∀ a : Array α, (List.foldl ?_ a l).data = a.data ++ ?_ := ?_
  exact this #[]
  induction l with
  | nil => simp
  | cons h => induction h.data <;> simp [*]

theorem mem_join : ∀ {L : Array (Array α)}, a ∈ L.join ↔ ∃ l, l ∈ L ∧ a ∈ l := by
  simp only [mem_def, join_data, List.mem_join, List.mem_map]
  intro l
  constructor
  · rintro ⟨_, ⟨s, m, rfl⟩, h⟩
    exact ⟨s, m, h⟩
  · rintro ⟨s, h₁, h₂⟩
    refine ⟨s.data, ⟨⟨s, h₁, rfl⟩, h₂⟩⟩

/-! ### indexOf? -/

theorem indexOf?_data [BEq α] {a : α} {l : Array α} :
    l.data.indexOf? a = (l.indexOf? a).map Fin.val := by
  simpa using aux l 0
where
  aux (l : Array α) (i : Nat) :
       ((l.data.drop i).indexOf? a).map (·+i) = (indexOfAux l a i).map Fin.val := by
    rw [indexOfAux]
    if h : i < l.size then
      rw [List.drop_eq_get_cons h, ←getElem_eq_data_get, List.indexOf?_cons]
      if h' : l[i] == a then
        simp [h, h']
      else
        simp [h, h', ←aux l (i+1), Function.comp_def, ←Nat.add_assoc, Nat.add_right_comm]
    else
      have h' : l.size ≤ i := Nat.le_of_not_lt h
      simp [h, List.drop_length_le h', List.indexOf?]
  termination_by l.size - i

/-! ### erase -/

theorem eraseIdx_swap_data {l : Array α} (i : Nat) (lt : i + 1 < size l) :
    (l.swap ⟨i+1, lt⟩ ⟨i, Nat.lt_of_succ_lt lt⟩).data.eraseIdx (i+1) = l.data.eraseIdx i := by
  let ⟨xs⟩ := l
  induction i generalizing xs <;> let x₀::x₁::xs := xs
  case zero => simp [swap, get]
  case succ i ih _ =>
    have lt' := Nat.lt_of_succ_lt_succ lt
    have : (swap ⟨x₀::x₁::xs⟩ ⟨i.succ + 1, lt⟩ ⟨i.succ, Nat.lt_of_succ_lt lt⟩).data
        = x₀::(swap ⟨x₁::xs⟩ ⟨i + 1, lt'⟩ ⟨i, Nat.lt_of_succ_lt lt'⟩).data := by
      simp [swap_def, List.set_succ, getElem_eq_data_get]
    simp [this, ih]

theorem feraseIdx_data {l : Array α} {i : Fin l.size} :
    (l.feraseIdx i).data = l.data.eraseIdx i := by
  induction l, i using feraseIdx.induct with
  | @case1 a i lt a' i' ih =>
    rw [feraseIdx]
    simp [lt, ih, a', eraseIdx_swap_data i lt]
  | case2 a i lt =>
    have : i + 1 ≥ a.size := Nat.ge_of_not_lt lt
    have last : i + 1 = a.size := Nat.le_antisymm i.is_lt this
    simp [feraseIdx, lt, List.dropLast_eq_eraseIdx last]

@[simp] theorem erase_data [BEq α] {l : Array α} {a : α} : (l.erase a).data = l.data.erase a := by
  let ⟨xs⟩ := l
  match h : indexOf? ⟨xs⟩ a with
  | none =>
    simp only [erase, h]
    apply erase_none 0
    simpa [←indexOf?_data] using congrArg (Option.map Fin.val) h
  | some i =>
    simp only [erase, h]
    rw [feraseIdx_data, ←List.eraseIdx_indexOf_eq_erase]
    congr
    rw [List.indexOf_eq_indexOf?, indexOf?_data]
    simp [h]
where
  erase_none {xs : List α} (i : Nat) (h : List.indexOf? a xs = none) :
      xs.drop i = (xs.drop i).erase a := by
    if le : xs.length ≤ i then
      rw [List.drop_length_le le]
      rfl
    else
      have lt : i < xs.length := Nat.lt_of_not_le le
      have h' := List.findIdx?_of_eq_none h i
      simp only [List.get?_eq_get lt] at h'
      rw [List.drop_eq_get_cons lt, List.erase]
      simp [h', ←erase_none (i+1) h]
  termination_by xs.length - i

/-! ### shrink -/

theorem size_shrink_loop (a : Array α) (n) : (shrink.loop n a).size = a.size - n := by
  induction n generalizing a with simp[shrink.loop]
  | succ n ih =>
      simp[ih]
      omega

theorem size_shrink (a : Array α) (n) : (a.shrink n).size = min a.size n := by
  simp [shrink, size_shrink_loop]
  omega