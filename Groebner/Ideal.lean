module

public import Mathlib

@[expose] public section

open Ideal

namespace Minimal

theorem minimal_iff_minimal_exists_minimal_and_le {α} [Preorder α] [WellFoundedLT α]
    {P : α → Prop} {x : α} :
    Minimal P x ↔ Minimal (∃ m', Minimal P m' ∧ m' ≤ ·) x ∧ P x := by
  constructor
  · intro h
    rw [Minimal]
    refine ⟨⟨⟨x, by simp [h]⟩, ?_⟩, h.prop⟩
    rintro y ⟨z, hz, hzy⟩ hyx
    exact le_trans (h.le_of_le hz.prop <| le_trans hzy hyx) hzy
  rintro ⟨h, hx⟩
  by_contra
  rw [not_minimal_iff_exists_lt hx] at this
  obtain ⟨y, hyx, hy⟩ := this
  obtain ⟨y', hy'y, hy'⟩ := exists_minimal_le_of_wellFoundedLT _ _ hy
  replace h := h.le_of_le ⟨y', hy', le_refl _⟩ (le_trans hy'y hyx.le)
  exact not_le_of_gt (lt_of_le_of_lt hy'y hyx) h

theorem prop_of_minimal_exists_minimal_and_le {α} [PartialOrder α] [WellFoundedLT α]
    {P : α → Prop} {x : α} (h : Minimal (∃ m', Minimal P m' ∧ m' ≤ ·) x) : P x := by
  obtain ⟨y, hy, hyx⟩ := h.prop
  obtain hxy := h.le_of_le ⟨y, hy, le_refl _⟩ hyx
  exact le_antisymm hyx hxy ▸ hy.prop

theorem minimal_iff_minimal_exists_minimal_and_le' {α} [PartialOrder α] [WellFoundedLT α]
    {P : α → Prop} {x : α} :
    Minimal P x ↔ Minimal (∃ m', Minimal P m' ∧ m' ≤ ·) x := by
  have := minimal_iff_minimal_exists_minimal_and_le (P := P) (x := x)
  have := prop_of_minimal_exists_minimal_and_le (P := P) (x := x)
  tauto

end Minimal

section Preorder

variable {k A G : Type*} [CommSemiring k]
variable [AddCommMonoid A] [Preorder A] [WellFoundedLT A] [CanonicallyOrderedAdd A] {s t : Set A}

theorem AddMonoidAlgebra.ideal_span_of'_image_eq_ideal_span_of'_image_minimal :
    Ideal.span (AddMonoidAlgebra.of' k A '' s) =
      Ideal.span (AddMonoidAlgebra.of' k A '' {x | Minimal (· ∈ s) x}) := by
  refine le_antisymm ?_ <| Ideal.span_mono (Set.image_mono (fun _ ↦ Minimal.prop))
  rw [Ideal.span_le]
  intro x hx
  obtain ⟨a, ha, rfl⟩ := (Set.mem_image _ _ _).mp hx
  obtain ⟨b, hb, hb'⟩ := exists_minimal_le_of_wellFoundedLT (· ∈ s) a ha
  obtain ⟨c, rfl⟩ := exists_add_of_le hb
  rw [show of' k A (b + c) = of' k A b * of' k A c by simp] at *
  apply Ideal.mul_mem_right _ _
  apply Set.mem_of_subset_of_mem Ideal.subset_span
  exact (Set.mem_image_of_mem (of' k A) (Set.mem_ofPred.mpr hb'))

theorem AddMonoidAlgebra.ideal_span_single_image_eq_ideal_span_single_image_minimal :
    Ideal.span ((AddMonoidAlgebra.single · (1 : k)) '' s) =
      Ideal.span ((AddMonoidAlgebra.single · (1 : k)) '' {x | Minimal (· ∈ s) x}) :=
  AddMonoidAlgebra.ideal_span_of'_image_eq_ideal_span_of'_image_minimal

theorem AddMonoidAlgebra.minimal_span_of'_image_iff_minimal [Nontrivial k] {x} :
    Minimal (∃ p ∈ Ideal.span (AddMonoidAlgebra.of' k A '' s), · ∈ p.coeff.support) x ∧ x ∈ s ↔
      Minimal (· ∈ s) x := by
  classical
  simp_rw [AddMonoidAlgebra.ideal_span_of'_image_eq_ideal_span_of'_image_minimal (s := s),
    AddMonoidAlgebra.mem_ideal_span_of'_image, Set.mem_ofPred]
  convert (Minimal.minimal_iff_minimal_exists_minimal_and_le (α := A)).symm with y
  simp_rw [le_iff_exists_add']
  constructor
  · rintro ⟨p, h, h₂⟩
    exact h _ h₂
  · rintro h
    use .of' k A y
    -- todo: it should be a lemma
    simp_rw [show (of' k A y).coeff.support = {y} by simp [AddMonoidAlgebra.coeff_single, eq_comm]]
    simpa using h

theorem AddMonoidAlgebra.minimal_ideal_span_single_image_iff_minimal [Nontrivial k] {x} :
    Minimal (∃ p ∈ Ideal.span ((single · (1 : k)) '' s), · ∈ p.coeff.support) x ∧ x ∈ s ↔
      Minimal (· ∈ s) x :=
  AddMonoidAlgebra.minimal_span_of'_image_iff_minimal

end Preorder

section PartialOrder

variable {k A G : Type*} [CommSemiring k] [Nontrivial k]
variable [AddCommMonoid A] [PartialOrder A] [WellFoundedLT A] [CanonicallyOrderedAdd A]
variable {x : A} {s t : Set A}

theorem AddMonoidAlgebra.minimal_ideal_span_of'_image_iff_minimal' :
    Minimal (∃ p ∈ Ideal.span (AddMonoidAlgebra.of' k A '' s), · ∈ p.coeff.support) x ↔
      Minimal (· ∈ s) x := by
  -- the proof is similar with `AddMonoidAlgebra.minimal_span_of'_image_iff_minimal`
  classical
  simp_rw [AddMonoidAlgebra.ideal_span_of'_image_eq_ideal_span_of'_image_minimal (s := s),
    AddMonoidAlgebra.mem_ideal_span_of'_image, Set.mem_ofPred]
  convert (Minimal.minimal_iff_minimal_exists_minimal_and_le' (α := A)).symm with y
  simp_rw [le_iff_exists_add']
  constructor
  · rintro ⟨p, h, h₂⟩
    exact h _ h₂
  · rintro h
    use .of' k A y
    -- todo: it should be a lemma
    simp_rw [show (of' k A y).coeff.support = {y} by simp [AddMonoidAlgebra.coeff_single, eq_comm]]
    simpa using h

theorem AddMonoidAlgebra.minimal_ideal_span_single_image_iff_minimal' :
    Minimal (∃ p ∈ Ideal.span ((single · (1 : k)) '' s), · ∈ p.coeff.support) x ↔
      Minimal (· ∈ s) x :=
  AddMonoidAlgebra.minimal_ideal_span_of'_image_iff_minimal'

theorem AddMonoidAlgebra.ideal_span_of'_image_eq_ideal_span_of'_image_iff :
    Ideal.span (AddMonoidAlgebra.of' k A '' s) = Ideal.span (AddMonoidAlgebra.of' k A '' t) ↔
      ∀ x, Minimal (· ∈ s) x ↔ Minimal (· ∈ t) x := by
  classical
  refine ⟨fun h ↦ ?_,
    fun h ↦ by unfold of'; simp [ideal_span_single_image_eq_ideal_span_single_image_minimal, h]⟩
  intro x
  simp_rw [← AddMonoidAlgebra.minimal_ideal_span_of'_image_iff_minimal' (k := k), h]

theorem AddMonoidAlgebra.ideal_span_single_image_eq_ideal_span_single_image_iff :
    Ideal.span ((single · (1 : k))'' s) = Ideal.span ((single · 1) '' t) ↔
      ∀ x, Minimal (· ∈ s) x ↔ Minimal (· ∈ t) x :=
  AddMonoidAlgebra.ideal_span_of'_image_eq_ideal_span_of'_image_iff

end PartialOrder

namespace MvPolynomial

variable {σ} {R} [CommSemiring R] {x : σ →₀ ℕ} {s t : Set (σ →₀ ℕ)}

theorem ideal_span_monomial_image_eq_ideal_span_monomial_image_minimal :
    Ideal.span ((monomial · (1 : R)) '' s) =
      Ideal.span ((monomial · (1 : R)) '' {x | Minimal (· ∈ s) x}) :=
  AddMonoidAlgebra.ideal_span_of'_image_eq_ideal_span_of'_image_minimal

theorem minimal_ideal_span_monomial_image_iff_minimal [Nontrivial R] :
    Minimal (∃ p ∈ Ideal.span ((monomial · (1 : R)) '' s), · ∈ p.support) x ↔
      Minimal (· ∈ s) x :=
  AddMonoidAlgebra.minimal_ideal_span_of'_image_iff_minimal'

theorem ideal_span_monomial_image_eq_ideal_span_monomial_image_iff [Nontrivial R] :
    Ideal.span ((monomial · (1 : R)) '' s) = Ideal.span ((monomial · 1) '' t) ↔
      ∀ x, Minimal (· ∈ s) x ↔ Minimal (· ∈ t) x :=
  AddMonoidAlgebra.ideal_span_of'_image_eq_ideal_span_of'_image_iff

end MvPolynomial

namespace MonomialOrder

open MvPolynomial

variable {R} {σ} [CommSemiring R] {m : MonomialOrder σ}

lemma span_leadingTerm_le_span_monomial {B : Set (MvPolynomial σ R)} :
    span (m.leadingTerm '' B) ≤ span ((fun p ↦ monomial (m.degree p) (1 : R)) '' (B \ {0})) := by
  rw [← m.span_leadingTerm_sdiff_singleton_zero, Ideal.span_le, Set.image_subset_iff]
  intro p hp
  rw [Set.mem_preimage, SetLike.mem_coe, ← C_mul_leadingCoeff_monomial_degree]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, hp, rfl⟩)

lemma span_leadingTerm_eq_span_monomial._replace_ {B : Set (MvPolynomial σ R)}
    (hB : ∀ p ∈ B, IsUnit (m.leadingCoeff p)) :
    span (m.leadingTerm '' B) =
      span ((fun p ↦ MvPolynomial.monomial (m.degree p) (1 : R)) '' B) := by
  classical
  apply le_antisymm
  · apply le_trans span_leadingTerm_le_span_monomial
    exact span_mono <| Set.image_mono (by simp)
  rw [Ideal.span_le, Set.image_subset_iff]
  intro p hp
  rw [Set.mem_preimage, SetLike.mem_coe]
  convert (span <| m.leadingTerm '' B).mul_mem_left
    (MvPolynomial.C (hB p hp).unit⁻¹.val) <| subset_span ⟨p, hp, rfl⟩
  rw [← C_mul_leadingCoeff_monomial_degree, ← mul_assoc, ← map_mul,
    IsUnit.val_inv_mul, MvPolynomial.C_1, one_mul]

-- lemma span_leadingTerm_image_eq_span_monomial_image {B : Set (MvPolynomial σ R)}
--     {s : Set (σ →₀ ℕ)}
--     (h : span (m.leadingTerm '' B) = span ((monomial · (1 : R)) '' s)) :
--     span (m.leadingTerm '' B) = span ((fun p ↦ monomial (m.degree p) (1 : R)) '' (B \ {0})) := by
--   apply le_antisymm span_leadingTerm_le_span_monomial

  -- rw [Ideal.span_le, Set.image_subset_iff]
  -- intro p hp
  -- rw [Set.mem_preimage, SetLike.mem_coe, ← C_mul_leadingCoeff_monomial_degree]
  -- exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, hp, rfl⟩)

-- lemma span_leadingTerm_eq_span_monomial._replace_ {B : Set (MvPolynomial σ R)}

end MonomialOrder

-- instance {α} [CommMonoidWithZero α] : CommMonoidWithZero αᵐᵒᵖ where

-- instance {α} [CommMonoidWithZero α] [WfDvdMonoid α] : WfDvdMonoid αᵐᵒᵖ where
--   wf := by
--     sorry

-- #check 1 ∣ 2
-- #check DivisibleBy
-- #synth WfDvdMonoid (MvPolynomial ℚ ℚ)ᵐᵒᵖ
-- #check Submodule.generators
-- #check Multiplicative
-- #check MvPolynomial.mem_ideal_span_monomial_image
-- -- #check toMultiplicative
-- end MonoidAlgebra
-- #check Finset.sum_eq_
