module

public import Mathlib

variable {α} (l : List α) (a : α)

public section

theorem Set.range_list_get_eq_toFinset_toSet [DecidableEq α] :
    Set.range l.get = l.toFinset := by
  simp

theorem Set.range_get_nil : Set.range ([] : List α).get = ∅ := by
  simp

theorem Set.range_get_singleton : Set.range ([a] : List α).get = {a} := by
  simp

theorem Set.range_get_cons_list {a} : Set.range (a :: l).get = insert a (Set.range l.get) := by
  classical
  rw [Set.range_list_get_eq_toFinset_toSet, Set.range_list_get_eq_toFinset_toSet]
  simp

theorem List.toFinset_singleton [DecidableEq α] : [a].toFinset = {a} := by
  rfl
