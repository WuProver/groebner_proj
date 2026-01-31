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

end MulEquiv
