module

public import Mathlib

@[expose] public section
namespace MulEquiv
open Function
variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {S} {T : Submonoid M}

@[to_additive]
lemma range_subtype (s : Submonoid M) :
    Set.range s.subtype = s := by
  simp

@[to_additive]
lemma range_subtype' (s : Submonoid M) :
    ↥(Set.range s.subtype) = s := by
  simp

@[to_additive]
lemma _root_.MonoidHom.mrangeRestrict_eq_rangeFactorization {N} [MulOneClass N] (f : M →* N) :
    ⇑f.mrangeRestrict = Set.rangeFactorization f := rfl

#check AddMonoidHom.mrangeRestrict

/-- A monoid homomorphism `f : M →* N` with a left-inverse `g : N → M` defines a multiplicative
equivalence between `M` and `f.mrange`.
This is a bidirectional version of `MonoidHom.mrange_restrict`. -/
@[to_additive (attr := simps +simpRhs)
  /-- An additive monoid homomorphism `f : M →+ N` with a left-inverse `g : N → M` defines an
  additive equivalence between `M` and `f.mrange`. This is a bidirectional version of
  `AddMonoidHom.mrange_restrict`. -/]
def ofLeftInverse'' (f : M →* N) (g : MonoidHom.mrange f → M)
    (h : Function.LeftInverse g (MonoidHom.mrangeRestrict f)) :
    M ≃* MonoidHom.mrange f :=
  { f.mrangeRestrict with
    toFun := f.mrangeRestrict
    invFun := g
    left_inv := h
    right_inv x := Subtype.ext <| by
      let ⟨x', hx'⟩ := MonoidHom.mem_mrange.mp x.2
      rw [← hx', ← h x']
      exact congrArg (f ∘ g) (Set.rangeFactorization_eq_iff x' x |>.mpr hx').symm
  }

-- @[simp]
-- lemma _root_.Function.Injective.of_subsingleton {α : Type u_1} {β : Type u_2} [Subsingleton α]
--     (f : α → β) :
--     f.Injective := by
--   intro _ _ _
--   exact Subsingleton.allEq ..

-- @[simp]
-- lemma _root_.Function.LeftInverse.of_subsingleton {α : Sort*} {β : Sort*} [Subsingleton β]
--     (g : α → β) (f : β → α) : Function.LeftInverse g f := fun _ ↦ Subsingleton.allEq ..

-- @[simp]
-- lemma _root_.Function.RightInverse.of_subsingleton {α : Sort*} [Subsingleton α] {β : Sort*}
--     (g : α → β) (f : β → α) : Function.RightInverse g f := fun _ ↦ Subsingleton.allEq ..

-- @[simp]
-- lemma _root_.Function.LeftInverse.of_empty {α : Sort*} [IsEmpty α] {β : Sort*} (g : α → β)
--     (f : β → α) :
--     Function.LeftInverse g f := have := Function.isEmpty f; LeftInverse.of_subsingleton g f

-- @[simp]
-- lemma _root_.Function.RightInverse.of_empty {α : Sort*} {β : Sort*} [IsEmpty β] (g : α → β)
--     (f : β → α) :
--     Function.RightInverse g f := have := Function.isEmpty g; RightInverse.of_subsingleton g f

-- lemma _root_.Set.leftInverse_rangeFactorization {α : Type u_1} {β : Type u_2} (f : α → β) :
--     Function.LeftInverse (Set.rangeSplitting f) (Set.rangeFactorization f) ↔ f.Injective := by
--   constructor
--   · intro h x y heq
--     rw [← Set.rangeFactorization_eq_rangeFactorization_iff] at heq
--     apply congrArg (Set.rangeSplitting f) at heq
--     rwa [h.eq, h.eq] at heq
--   · intro h a
--     rw [← h.eq_iff, Set.apply_rangeSplitting f, Set.rangeFactorization_coe]

-- example (f : M →* N) (hf : Injective f) :
--     Function.LeftInverse (Set.rangeSplitting f) (MonoidHom.mrangeRestrict f) := by
--   rwa [f.mrangeRestrict_eq_rangeFactorization, Set.leftInverse_rangeFactorization]
