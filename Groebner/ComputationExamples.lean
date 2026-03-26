import Groebner.ToMathlib.List
import Groebner.Groebner

open MonomialOrder
variable {σ} {R} [CommSemiring R] {m : MonomialOrder σ} (p : MvPolynomial σ R)
namespace MonomialOrder

set_option linter.unusedSimpArgs false in
example : True := by
  have : ({1, 2, 3} : Set Nat) = Set.range (?_ : List Nat).get := by
    simp only [← Set.range_get_nil, ← Set.range_get_singleton, ← Set.range_get_cons_list]
    exact rfl
  have : ({1, 2, 3} : Finset Nat) = Set.range (?_ : List Nat).get := by
    simp only [← List.toFinset_nil, ← List.toFinset_cons, ← List.toFinset_singleton]
    have := Set.range_list_get_eq_toFinset_toSet (α := Nat) [1,2,3]
    have := this.symm
    -- fail if Set.range_list_get_eq_toFinset_toSet is classical. WHY?????????????????
    -- rw [← Set.range_list_get_eq_toFinset_toSet]
    convert (Set.range_list_get_eq_toFinset_toSet _).symm
  trivial

open MvPolynomial MonomialOrder

-- for sorry-free examples, refer to
-- https://github.com/WuProver/MonomialOrderedPolynomial/blob/master/MonomialOrderedPolynomial/MvPolynomialExamples.lean
set_option linter.unusedSimpArgs false in
example :
    lex.IsRemainder (X 0 ^ 2 + X 1 ^ 3 + X 2 ^ 4 + X 3 ^ 5: MvPolynomial (Fin 4) ℚ)
      {X 0, X 1, X 2, X 3} 0 := by
  -- convert set to `Set.image list.get`
  simp only [← Set.range_get_nil, ← Set.range_get_singleton, ← Set.range_get_cons_list]
  -- use index
  rw [IsRemainder.isRemainder_range_fintype, ← exists_and_right]
  use [X 0, X 1 ^ 2, X 2 ^ 3, X 3 ^ 4].get
  split_ands
  · set_option backward.isDefEq.respectTransparency false in
    simp [Fin.univ_succ, -List.get_eq_getElem, List.get] -- convert sum to add
    try grind-- PIT, we will rely on reflection
  · intro i
    fin_cases i
    all_goals {
      simp [-List.get_eq_getElem, List.get]
      try sorry -- compare degree
    }
  · simp -- here the remainder is 0, whose support set is empty, so `simp` solves it...

set_option linter.unusedSimpArgs false in
example :
    lex.IsRemainder (X 0 ^ 2 + X 1 ^ 3 + X 2 ^ 4 + X 3 ^ 5: MvPolynomial (Fin 6) ℚ)
      {X 3, X 4 + X 5} (X 0 ^ 2 + X 1 ^ 3 + X 2 ^ 4) := by
  -- convert set to `Set.image list.get`
  simp only [← Set.range_get_nil, ← Set.range_get_singleton, ← Set.range_get_cons_list]
  -- use index
  rw [IsRemainder.isRemainder_range_fintype, ← exists_and_right]
  use [X 3 ^ 4, 0].get
  split_ands
  · set_option backward.isDefEq.respectTransparency false in
    simp [Fin.univ_succ, -List.get_eq_getElem, List.get] -- convert sum to add
    try grind-- PIT, we will rely on reflection later
  · intro i
    fin_cases i
    all_goals {
      simp [-List.get_eq_getElem, List.get]
      try sorry -- compare degree
    }
  · sorry -- we will rely on reflection

end MonomialOrder
