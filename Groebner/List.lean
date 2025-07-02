import Mathlib

variable {α} (l : List α) (a : α)

-- open Classical
open Classical in
theorem Set.range_list_get_eq_toFinset_toSet :
    Set.range l.get = l.toFinset.toSet := by
  simp

theorem Set.range_get_nil : Set.range ([] : List α).get = ∅ := by
  simp

theorem Set.range_get_singleton : Set.range ([a] : List α).get = {a} := by
  simp

theorem Set.range_get_cons_list {a} : Set.range (a :: l).get = insert a (Set.range l.get) := by
  rw [Set.range_list_get_eq_toFinset_toSet, Set.range_list_get_eq_toFinset_toSet]
  simp

-- theorem Finset.toFinset
#check List.toFinset_nil
#check List.toFinset_cons

theorem List.toFinset_singleton [DecidableEq α] : [a].toFinset = {a} := by
  rfl
