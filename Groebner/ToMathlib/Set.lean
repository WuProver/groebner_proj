module

public import Mathlib

-- merged: https://github.com/leanprover-community/mathlib4/pull/36368
@[simp]
public lemma Set.leftInverse_rangeFactorization._mathlib_ {α : Type*} {β : Type*} (f : α → β) :
    Function.LeftInverse (Set.rangeSplitting f) (Set.rangeFactorization f) ↔ f.Injective := by
  constructor
  · intro h x y heq
    rw [← Set.rangeFactorization_eq_rangeFactorization_iff] at heq
    apply congrArg (Set.rangeSplitting f) at heq
    rwa [h.eq, h.eq] at heq
  · intro h a
    rw [← h.eq_iff, Set.apply_rangeSplitting f, Set.rangeFactorization_coe]
