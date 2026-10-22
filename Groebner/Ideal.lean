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

namespace MonoidAlgebra

#check MonoidAlgebra.mem_ideal_span_of_image
variable {k A G : Type*}

theorem mem_ideal_span_single_image_ [Monoid G] [Semiring k] {s : Set (k × G)}
    {x : MonoidAlgebra k G} :
    x ∈ Ideal.span ((fun cm ↦ MonoidAlgebra.single cm.2 cm.1) '' s) ↔
      ∀ m, x.coeff m ∈ Ideal.span (Prod.fst '' {cm ∈ s | ∃ d, m = d * cm.snd}) := by
  classical
  let RHS : Ideal k[G] := {
    carrier := {x | ∀ m, x.coeff m ∈ Ideal.span (Prod.fst '' {cm ∈ s | ∃ d, m = d * cm.2})},
    add_mem' ha hb m := Ideal.add_mem _ (ha m) (hb m),
    zero_mem' := by simp
    smul_mem' a b hb m := by
      simp only [smul_eq_mul, coeff_mul]
      refine Ideal.sum_mem _ fun m' hm' ↦ Ideal.sum_mem _ fun m'' hm'' ↦ ?_
      simp only [apply_ite, zero_mem, ite_true_right]
      rintro rfl
      refine Ideal.mul_mem_left _ _ <| Ideal.span_mono ?_ <| hb m''
      apply Set.image_mono
      rintro cm ⟨hcms, ⟨d, rfl⟩⟩
      exact ⟨hcms, ⟨m' * d, (mul_assoc ..).symm⟩⟩
  }
  change _ ↔ x ∈ RHS
  constructor
  · apply Ideal.span_le.mpr
    rintro _ ⟨cm, ⟨hcm, rfl⟩⟩
    simpa [Finsupp.single_apply, apply_ite, RHS, ← Submodule.carrier_eq_coe] using
      Ideal.subset_span <| Set.mem_image_of_mem _ <| by exact ⟨hcm, ⟨1, by simp⟩⟩
  · intro h
    rw [← x.sum_coeff_single]
    apply Ideal.sum_mem
    rintro m -
    specialize h m
    apply Submodule.mem_map_of_mem (f := lsingle (R := k) m) at h
    rw [Submodule.map_span] at h
    refine Ideal.span_le.mpr ?_ (Submodule.span_subset_span k k[G] (M := k[G]) _ h)
    rintro _ ⟨_, ⟨cm, ⟨hcm, ⟨d, rfl⟩⟩, rfl⟩, rfl⟩
    rw [lsingle_apply, ← one_mul cm.1, ← single_mul_single d cm.2 1 cm.1]
    exact Ideal.mul_mem_left _ _ <| Ideal.subset_span <| Set.mem_image_of_mem _ hcm

end MonoidAlgebra

section AddMonoidAlgebra

variable {k A G : Type*}

#check MvPolynomial.homogeneousComponent

-- #check Set.filterIm

-- theorem mem_ideal_span_single_image [AddMonoid G] [Semiring k] {s : Set _}
--     {m : G} {c : k} :
--     single m c ∈ Ideal.span ((fun ⟨c, m⟩ ↦ single m c) '' s) ↔
--       c ∈ Ideal.span (Prod.fst '' {cm ∈ s | ∃ d, m = d + cm.snd}) := by
--   -- have := singleHom
--   simp
--   sorry
-- #check mem_ideal_span_of'_image
-- #synth Module (AddMonoidAlgebra Int Int) (AddMonoidAlgebra Rat Int)
-- #check SkewPolynomial

open AddMonoidAlgebra in
lemma coeff_toMultiplicative_apply_ofAdd {R M} [Semiring R] [Add M] (x : R[M]) (m : M) :
    (toMultiplicative R M x).coeff (Multiplicative.ofAdd m) = x.coeff m := by
  rw [AddMonoidAlgebra.coeff_toMultiplicative_apply,
    Finsupp.mapDomain_apply_of_injective Multiplicative.ofAdd.injective]

lemma _root_.Set.image_ofPred {α β} {p : α → Prop} {f : β → α} (hf : f.Surjective) :
    f '' {b | p (f b)} = {a | p a} := by
  rw [← Set.preimage_ofPred_eq (f := f), Set.image_preimage_eq _ hf]

lemma _root_.Set.image_ofPred_comp {α β} {p : α → Prop} {f : β → α} (hf : f.Surjective) :
    f '' Set.ofPred (p ∘ f) = {a | p a} := Set.image_ofPred hf

theorem MonoidAlgebra.mem_ideal_span_single_image' {ι} [Monoid G] [Semiring k] {s : Set ι}
    {fm : ι → G} {fc : ι → k} {x : MonoidAlgebra k G} :
    x ∈ Ideal.span ((fun i ↦ MonoidAlgebra.single (fm i) (fc i)) '' s) ↔
      ∀ m, x.coeff m ∈ Ideal.span (fc '' {i ∈ s | ∃ d, m = d * (fm i)}) := by
  classical
  let RHS : Ideal (MonoidAlgebra k G) := {
    carrier := {x | ∀ m, x.coeff m ∈ Ideal.span (fc '' {i ∈ s | ∃ d, m = d * (fm i)})},
    add_mem' ha hb m := Ideal.add_mem _ (ha m) (hb m),
    zero_mem' := by simp
    smul_mem' a b hb m := by
      simp only [smul_eq_mul, coeff_mul]
      refine Ideal.sum_mem _ fun m' hm' ↦ Ideal.sum_mem _ fun m'' hm'' ↦ ?_
      simp only [apply_ite, zero_mem, ite_true_right]
      rintro rfl
      refine Ideal.mul_mem_left _ _ <| Ideal.span_mono ?_ <| hb m''
      apply Set.image_mono
      rintro i ⟨his, ⟨d, rfl⟩⟩
      exact ⟨his, ⟨m' * d, (mul_assoc ..).symm⟩⟩
  }
  change _ ↔ x ∈ RHS
  constructor
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, ⟨hi, rfl⟩⟩
    simpa [Finsupp.single_apply, apply_ite, RHS, ← Submodule.carrier_eq_coe] using
      Ideal.subset_span <| Set.mem_image_of_mem _ <| by exact ⟨hi, ⟨1, by simp⟩⟩
  · intro h
    rw [← x.sum_coeff_single]
    apply Ideal.sum_mem
    rintro m -
    specialize h m
    apply Submodule.mem_map_of_mem (f := MonoidAlgebra.lsingle (R := k) m) at h
    rw [Submodule.map_span] at h
    refine Ideal.span_le.mpr ?_ (Submodule.span_subset_span k _ (M := MonoidAlgebra k G) _ h)
    rintro _ ⟨_, ⟨i, ⟨hi, ⟨d, rfl⟩⟩, rfl⟩, rfl⟩
    rw [lsingle_apply, ← one_mul (fc i), ← single_mul_single d (fm i) 1 (fc i)]
    exact Ideal.mul_mem_left _ _ <| Ideal.subset_span <| Set.mem_image_of_mem _ hi

theorem MonoidAlgebra.mem_ideal_span_single_image {ι} [Monoid G] [Semiring k] {s : Set ι}
    {fm : ι → G} {fc : ι → k} {x : MonoidAlgebra k G} :
    x ∈ Ideal.span ((fun i ↦ MonoidAlgebra.single (fm i) (fc i)) '' s) ↔
      ∀ m ∈ x.coeff.support,
        x.coeff m ∈ Ideal.span (fc '' {i ∈ s | ∃ d, m = d * (fm i)}) := by
  convert x.mem_ideal_span_single_image' with m
  by_cases h : x.coeff m = 0 <;> simp [h]

open Multiplicative in
theorem AddMonoidAlgebra.mem_ideal_span_single_image' {ι} [AddMonoid G] [Semiring k] {s : Set ι}
    {fm : ι → G} {fc : ι → k} {x : AddMonoidAlgebra k G} :
    x ∈ Ideal.span ((fun i ↦ AddMonoidAlgebra.single (fm i) (fc i)) '' s) ↔
      ∀ m, x.coeff m ∈ Ideal.span (fc '' {i ∈ s | ∃ d, m = d + (fm i)}) := by
  convert
    (toMultiplicative _ _ x).mem_ideal_span_single_image' (s := s) (fm := ofAdd ∘ fm) (fc := fc)
  · simp_rw [Function.comp, ← AddMonoidAlgebra.toMultiplicative_single,
      ← Set.image_image, ← Ideal.map_span, Ideal.apply_mem_of_equiv_iff]
  · simp_rw [ofAdd.surjective.forall, ofAdd.surjective.exists, coeff_toMultiplicative_apply_ofAdd,
      Function.comp, ← ofAdd_add, ofAdd.apply_eq_iff_eq]

theorem AddMonoidAlgebra.mem_ideal_span_single_image {ι} [AddMonoid G] [Semiring k] {s : Set ι}
    {fm : ι → G} {fc : ι → k} {x : AddMonoidAlgebra k G} :
    x ∈ Ideal.span ((fun i ↦ AddMonoidAlgebra.single (fm i) (fc i)) '' s) ↔
      ∀ m ∈ x.coeff.support,
        x.coeff m ∈ Ideal.span (fc '' {i ∈ s | ∃ d, m = d + (fm i)}) := by
  convert x.mem_ideal_span_single_image' with m
  by_cases h : x.coeff m = 0 <;> simp [h]

-- theorem MvPolynomial.mem_ideal_span_monomial_image_' {σ R ι} [CommSemiring R]
--     {x : MvPolynomial σ R} {s : Set ι} {fm : ι → σ →₀ ℕ} {fc : ι → R} :
--     x ∈ Ideal.span ((fun i => monomial (fm i) (fc i)) '' s) ↔
--       ∀ xi, x.coeff xi ∈ Ideal.span (fc '' {i ∈ s | fm i ≤ xi}) := by
--   simpa [le_iff_exists_add', monomial] using x.mem_ideal_span_single_image' (fm := fm) (fc := fc)

theorem MvPolynomial.mem_ideal_span_monomial_image' {σ R ι} [CommSemiring R]
    {x : MvPolynomial σ R} {s : Set ι} {fm : ι → σ →₀ ℕ} {fc : ι → R} :
    x ∈ Ideal.span ((fun i => monomial (fm i) (fc i)) '' s) ↔
      ∀ xi ∈ x.support, x.coeff xi ∈ Ideal.span (fc '' {i ∈ s | fm i ≤ xi}) := by
  simpa [le_iff_exists_add', monomial] using x.mem_ideal_span_single_image (fm := fm) (fc := fc)

end AddMonoidAlgebra
