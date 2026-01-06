import Groebner.Basic

variable {σ R : Type*} [CommSemiring R] {m : MonomialOrder σ}
variable {G : Set (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)}
variable (hG : m.IsGroebnerBasis G I)

namespace MonomialOrder
open MonomialOrder
open MvPolynomial

-- merged: https://github.com/leanprover-community/mathlib4/pull/26039
@[simp]
lemma leadingTerm_leadingTerm (f : MvPolynomial σ R) :
    m.leadingTerm (m.leadingTerm f) = m.leadingTerm f := by
  classical
  by_cases h : f = 0 <;> simp [leadingTerm, h, degree_monomial]

set_option linter.unusedVariables false in
def IsGroebnerBasis.IsMinimal (hG : m.IsGroebnerBasis G I) :=
  (∀ p ∈ G, m.Monic p) ∧ (∀ p ∈ G, ∀ q ∈ G, q ≠ p → ¬ m.degree q ≤ m.degree p)

set_option linter.unusedVariables false in
def IsGroebnerBasis.IsReduced (hG : m.IsGroebnerBasis G I) :=
  (∀ p ∈ G, m.Monic p) ∧ ∀ p ∈ G, m.IsRemainder p (G \ {p}) p

-- lemma degree_eq_iff_of_isRemainder {p r : MvPolynomial σ R}
--     (hG : m.IsRemainder p G r)
--     (hG' : ∀ g ∈ G, IsUnit (m.leadingCoeff g)) :
--     m.degree p = m.degree r ↔
--       ∀ g ∈ G, ¬ m.degree g ≤ m.degree p := by
--   unfold IsRemainder at hG
--   sorry

lemma le_degree_of_mem_support {p : MvPolynomial σ R} {a : σ →₀ ℕ}
    (ha : a ∈ p.support) : a ≼[m] m.degree p := by
  simp [degree, Finset.le_sup ha]

-- lemma leadingTerm_eq_iff_of_isRemainder {p r : MvPolynomial σ R}
--     (hG : m.IsRemainder p G r)
--     (hG' : ∀ g ∈ G, IsUnit (m.leadingCoeff g)) :
--     m.leadingTerm p = m.leadingTerm r ↔
--       ∀ g ∈ G, ¬ m.degree g ≤ m.degree p := by
--   sorry

-- lemma isGroebnerBasis_of_isRemainder_of_isGroebnerBasis
--     {R : Type*} [CommRing R] {m : MonomialOrder σ}
--     {G : Set (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)}
--     (hG : m.IsGroebnerBasis G I) (hG' : ∀ g ∈ G, IsUnit (m.leadingCoeff g))
--     (r : G → MvPolynomial σ R) (hr : ∀ g : G, m.IsRemainder ↑g (G \ {↑g}) (r g)) :
--     m.IsGroebnerBasis (Set.range r) I := by
--   have rmemI (g : G) : r g ∈ I := by
--     rw [m.mem_ideal_iff_of_isRemainder _ (hr g)]
--     · exact Set.mem_of_subset_of_mem hG.1 g.2
--     rw [Set.diff_singleton_subset_iff, Set.subset_insert_iff]
--     simp [hG.1]
--   constructor
--   · intro r'
--     rw [Set.mem_range]
--     rintro ⟨g, hg⟩
--     exact hg ▸ rmemI g
--   refine le_antisymm ?_ ?_
--   on_goal -1 =>
--     rw [Ideal.span_le]
--     intro _
--     simp only [Set.mem_image, Set.mem_range]
--     rintro ⟨_, ⟨g, hg⟩, hg'⟩
--     subst hg hg'
--     apply Submodule.mem_span_of_mem (Set.mem_image_of_mem m.leadingTerm <| rmemI g)
--   rw [hG.2, Ideal.span_le]
--   intro _
--   rw [Set.mem_image]
--   rintro ⟨g, hgI, hLTg⟩
--   subst hLTg
--   -- rw [monomial_notMem_span_leadingTerm]
--   sorry

lemma IsGroebnerBasis.singleton_zero_bot :
    m.IsGroebnerBasis {(0 : MvPolynomial σ R)} ⊥ := by
  simp [IsGroebnerBasis]

lemma IsGroebnerBasis.empty_bot :
    m.IsGroebnerBasis (∅ : Set <| MvPolynomial σ R) ⊥ := by
  simp [IsGroebnerBasis]

@[simp]
lemma IsGroebnerBasis.singleton_zero_iff (I : Ideal (MvPolynomial σ R)) :
    m.IsGroebnerBasis {(0 : MvPolynomial σ R)} I ↔ I = ⊥ := by
  constructor
  · simp [IsGroebnerBasis, Ideal.span_eq_bot]
    aesop
  · simp_intro .. [IsGroebnerBasis.singleton_zero_bot]

@[simp]
lemma IsGroebnerBasis.empty_iff (I : Ideal (MvPolynomial σ R)) :
    m.IsGroebnerBasis (∅ : Set <| MvPolynomial σ R) I ↔ I = ⊥ := by
  constructor
  · simp [IsGroebnerBasis, Ideal.span_eq_bot]
    aesop
  · simp_intro .. [IsGroebnerBasis.empty_bot]

@[simp]
lemma IsRemainder.of_subsingleton [Subsingleton (MvPolynomial σ R)]
    {p r : MvPolynomial σ R} {s : Set (MvPolynomial σ R)} :
    m.IsRemainder p s r := by
  simp [IsRemainder, Subsingleton.eq_zero (α := MvPolynomial σ R)]

@[simp]
lemma IsGroebnerBasis.of_subsingleton [Subsingleton (MvPolynomial σ R)]
    {s : Set (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)} :
    m.IsGroebnerBasis s I := by
  classical
  simp [IsGroebnerBasis, Subsingleton.eq_zero (α := MvPolynomial σ R),
    Subsingleton.eq_zero (α := Ideal <| MvPolynomial σ R) I,
    Subsingleton.eq_zero (α := Ideal <| MvPolynomial σ R) (Ideal.span _)]

lemma IsGroebnerBasis.isGroebnerBasis_monomial {R : Type*} [CommSemiring R] (s : Set (σ →₀ ℕ)) :
    m.IsGroebnerBasis ((MvPolynomial.monomial · (1 : R)) '' s)
      (Ideal.span ((MvPolynomial.monomial · 1) '' s)) := by
  classical
  wlog nontrivial : Nontrivial R generalizing
  · rw [not_nontrivial_iff_subsingleton] at nontrivial
    exact IsGroebnerBasis.of_subsingleton ..
  refine ⟨Ideal.subset_span, ?_⟩
  rw [le_antisymm_iff, Ideal.span_le, Ideal.span_le]
  constructor
  case right =>
    apply (subset_trans · Ideal.subset_span)
    apply Set.image_mono
    exact Ideal.subset_span
  rw [m.span_leadingTerm_eq_span_monomial (by simp), Set.image_image]
  simp [-Set.image_subset_iff, m.degree_monomial]
  intro p
  simp [mem_ideal_span_monomial_image, leadingTerm]
  aesop

lemma IsGroebnerBasis.isGroebnerBasis_monomial_minimal {R : Type*} [CommSemiring R]
    (s : Set (σ →₀ ℕ)) :
    m.IsGroebnerBasis ((MvPolynomial.monomial · (1 : R)) '' {x | Minimal (· ∈ s) x})
      (Ideal.span ((MvPolynomial.monomial · 1) '' s)) := by
  classical
  wlog nontrivial : Nontrivial R generalizing
  · rw [not_nontrivial_iff_subsingleton] at nontrivial
    exact IsGroebnerBasis.of_subsingleton ..
  constructor
  · apply (subset_trans · Ideal.subset_span)
    exact Set.image_mono <| setOf_minimal_subset s
  rw [le_antisymm_iff, Ideal.span_le, Ideal.span_le]
  constructor
  case right =>
    apply (subset_trans · Ideal.subset_span)
    apply Set.image_mono
    apply (subset_trans · Ideal.subset_span)
    exact Set.image_mono <| setOf_minimal_subset s
  rw [m.span_leadingTerm_eq_span_monomial (by simp), Set.image_image]
  simp [-Set.image_subset_iff, m.degree_monomial]
  intro p
  simp_rw [Set.mem_image, SetLike.mem_coe, mem_ideal_span_monomial_image, Set.mem_setOf]
  rintro ⟨q, ⟨hq, rfl⟩⟩ a ha
  simp [leadingTerm] at ha
  obtain ⟨b, hbs, hbq⟩ := hq a (by aesop)
  obtain ⟨c, hc⟩ := exists_minimal_le_of_wellFoundedLT _ b hbs
  exact ⟨c, hc.2, le_trans hc.1 hbq⟩

lemma IsGroebnerBasis.smul
    {ι : Type*} (f : ι → R) (f' : ι → MvPolynomial σ R) (hf : ∀ i : ι, IsUnit (f i))
    (hG : m.IsGroebnerBasis (Set.range f') I) :
    m.IsGroebnerBasis (Set.range (fun i ↦ (f i) • (f' i))) I := by
  -- the proof can be generalized
  classical
  simp_rw [smul_eq_C_mul]
  constructor
  · intro p
    simp_rw [Set.mem_range]
    rintro ⟨q, rfl⟩
    exact Ideal.mul_mem_left I _ (hG.1 <| by simp)
  rw [hG.2]
  unfold Ideal.span
  rw [Submodule.span_eq_iSup_of_singleton_spans, Submodule.span_eq_iSup_of_singleton_spans]
  have hunit (i) : IsUnit (C (σ := σ) (f i)) := RingHom.isUnit_map C (hf i)
  simp_rw [iSup_image, iSup_range]
  congr
  ext i : 1
  convert Submodule.span_singleton_smul_eq (hunit i) (m.leadingTerm (f' i)) |>.symm using 3
  simp [leadingTerm, C_mul_monomial, leadingCoeff]
  suffices m.degree (C (f i) * (f' i)) = m.degree (f' i) by simp [this]
  wlog hg : f' i ≠ 0
  · push_neg at hg
    simp [hg]
  rw [m.degree_mul_of_isRegular_left, m.degree_C, zero_add]
  · simp [leadingCoeff, hf i |>.isRegular]
  · exact hg

lemma IsGroebnerBasis.smul_iff
    {ι : Type*} (f : ι → R) (f' : ι → MvPolynomial σ R) (hf : ∀ i : ι, IsUnit (f i)) :
    m.IsGroebnerBasis (Set.range (fun i ↦ (f i) • (f' i))) I ↔
      m.IsGroebnerBasis (Set.range f') I := by
  classical
  refine ⟨?_, IsGroebnerBasis.smul f f' hf⟩
  convert IsGroebnerBasis.smul
    (fun i ↦ ↑(hf i).unit⁻¹) (fun i ↦ (f i) • (f' i)) (by simp) (I := I)
  simp [smul_smul]

lemma IsGroebnerBasis.inv (hG : m.IsGroebnerBasis G I)
    (hG' : ∀ g ∈ G, IsUnit (m.leadingCoeff g)) :
    m.IsGroebnerBasis (Set.range fun (g : G) ↦ (hG' _ g.prop).unit⁻¹ • g.val) I :=
  smul (hG := by simp [hG]) (hf := by simp)

lemma IsGroebnerBasis.span_image_leadingTerm
    (hG : m.IsGroebnerBasis G I) (hG' : ∀ g ∈ G, IsUnit (m.leadingCoeff g)) :
    m.IsGroebnerBasis (m.leadingTerm '' G) (Ideal.span (m.leadingTerm '' I)) := by
  classical
  rw [hG.2, Set.image_eq_range, ← IsGroebnerBasis.smul_iff
    (f := fun (g : G) ↦ ↑(hG' g.1 g.2).unit⁻¹) (hf := by simp), ← Set.image_eq_range,
    m.span_leadingTerm_eq_span_monomial hG']
  simp [leadingTerm, smul_monomial,
    ← Set.image_eq_range (fun g ↦ monomial (m.degree g) (1 : R)) G,
    ← Set.image_image (monomial · (1 : R)),
    IsGroebnerBasis.isGroebnerBasis_monomial (σ := σ) (m := m)]

open MvPolynomial MonomialOrder MonomialOrder.IsGroebnerBasis
namespace IsGroebnerBasis

variable {hG}

-- todo: move
lemma IsRemainder.self_iff (p : MvPolynomial σ R)
    (G : Set (MvPolynomial σ R)) :
    m.IsRemainder p G p ↔
    ∀ a ∈ p.support, ∀ q ∈ G, q ≠ 0 → ¬ m.degree q ≤ a :=
  and_iff_right ⟨0, by simp⟩

lemma IsRemainder.self_tfae (p : MvPolynomial σ R)
    (G : Set (MvPolynomial σ R)) :
    [m.IsRemainder p G p, ∀ B' ⊆ G, m.IsRemainder p B' p,
      ∀ q ∈ G, m.IsRemainder p {q} p,
      ∀ a ∈ p.support, ∀ q ∈ G, q ≠ 0 → ¬ m.degree q ≤ a].TFAE := by
  classical
  apply List.tfae_of_forall (∀ a ∈ p.support, ∀ q ∈ G, q ≠ 0 → ¬ m.degree q ≤ a)
  intro h h
  fin_cases h
  · exact IsRemainder.self_iff ..
  · simp only [IsRemainder.self_iff]
    aesop
  · simp only [IsRemainder.self_iff]
    aesop
  rfl

lemma IsRemainder.self {p r : MvPolynomial σ R}
    (h : m.IsRemainder p G r) :
    m.IsRemainder r G r :=
  ⟨⟨0, by simp⟩, h.2⟩

lemma IsReduced.isReduced_def :
    hG.IsReduced ↔
      (∀ p ∈ G, m.Monic p) ∧
      ∀ p ∈ G, ∀ a ∈ p.support, ∀ q ∈ G, q ≠ p → ¬ m.degree q ≤ a := by
  simp? [IsReduced, m.isRemainder_self_iff] says
    simp only [IsReduced, IsRemainder.self_iff, mem_support_iff, ne_eq, Set.mem_diff,
      Set.mem_singleton_iff, and_imp, and_congr_right_iff]
  rintro h1
  wlog h : Nontrivial R
  · simp [(not_nontrivial_iff_subsingleton.mp h).eq_zero]
  have (g) (hg : g ∈ G) : g ≠ 0 := (h1 g hg).ne_zero
  aesop

lemma IsReduced.isMinimal : hG.IsReduced → hG.IsMinimal := by
  rw [IsReduced.isReduced_def, IsMinimal]
  intro h
  refine ⟨h.1, ?_⟩
  intro p hp q hq
  wlog nontrivial : Nontrivial R
  · have := not_nontrivial_iff_subsingleton.mp nontrivial
    simp [Subsingleton.eq_zero]
  exact h.2 p hp (m.degree p) (by simp [h.1 p hp |>.ne_zero]) q hq

@[simp]
lemma IsReduced.of_subsingleton [Subsingleton (MvPolynomial σ R)]
    {s : Set (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)} :
    (IsGroebnerBasis.of_subsingleton (m := m) (s := s) (I := I)).IsReduced := by
  simp [IsReduced, Subsingleton.eq_zero (α := MvPolynomial σ R), Monic,
    ← (MvPolynomial.C_injective σ R).eq_iff]

@[simp]
lemma IsMinimal.of_subsingleton [Subsingleton (MvPolynomial σ R)]
    {s : Set (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)} :
    (IsGroebnerBasis.of_subsingleton (m := m) (s := s) (I := I)).IsMinimal :=
  IsReduced.isMinimal IsReduced.of_subsingleton

lemma IsReduced.isReduced_monomial {s : Set (σ →₀ ℕ)} {I : Ideal (MvPolynomial σ R)}
    (h : m.IsGroebnerBasis ((MvPolynomial.monomial · (1 : R)) '' {x | Minimal (· ∈ s) x}) I) :
    h.IsReduced := by
  classical
  rw [IsReduced.isReduced_def]
  constructor
  · simp
  simp_rw [Set.mem_image, Set.mem_setOf]
  rintro p ⟨p', ⟨hp', rfl⟩⟩ a ha q ⟨q', ⟨hq', rfl⟩⟩ hqp
  simp [monomial_eq_monomial_iff] at hqp
  have : Nontrivial R := nontrivial_of_ne _ _ hqp.2
  simp at ha
  subst ha
  simp [degree_monomial]
  by_contra! hq'p'
  exact hqp.1 <| le_antisymm hq'p' <| hp'.le_of_le (hq'.prop) hq'p'

-- lemma isMinimal_monomial_iff_isReduced_monomial {s : Set (σ →₀ ℕ)} {I : Ideal (MvPolynomial σ R)}
--     (hs : m.IsGroebnerBasis ((MvPolynomial.monomial · (1 : R)) '' s) I) :
--     hs.IsMinimal ↔ hs.IsReduced := by
--   rw [IsMinimal, isReduced_def]
--   apply Iff.and (Iff.refl _)
--   simp_rw [Set.mem_image]
--   -- easy
--   sorry

@[simp]
lemma _root_.MonomialOrder.monic_leadingTerm (p : MvPolynomial σ R) :
    m.Monic (m.leadingTerm p) ↔ m.Monic p := by simp [leadingTerm, Monic]

lemma _root_.MonomialOrder.support_leadingTerm (p : MvPolynomial σ R) [Decidable (p = 0)] :
    support (m.leadingTerm p) = if p = 0 then ∅ else {m.degree p} := by
  classical
  simp [leadingTerm, support_monomial]

lemma _root_.MonomialOrder.support_leadingTerm' {p : MvPolynomial σ R} :
    p ≠ 0 → support (m.leadingTerm p) = {m.degree p} := by
  classical
  simp_intro .. [support_leadingTerm]

-- merged: https://github.com/leanprover-community/mathlib4/pull/26039
@[simp]
lemma _root_.MonomialOrder.degree_leadingTerm' (f : MvPolynomial σ R) :
    m.degree (m.leadingTerm f) = m.degree f := by
  classical
  simp only [leadingTerm, degree_monomial, leadingCoeff_eq_zero_iff, ite_eq_right_iff]
  simp_intro h

lemma IsMinimal.image_leadingTerm_eq_image_monomial_one (hG' : hG.IsMinimal) :
    m.leadingTerm '' G = (fun p ↦ monomial (m.degree p) 1) '' G := by
  simp_rw [Set.image_eq_range]
  congr
  ext x : 1
  simp [leadingTerm, hG'.1]

lemma IsMinimal.isReduced_leadingTerm (hG' : hG.IsMinimal) :
    IsGroebnerBasis.span_image_leadingTerm hG (by simp_intro .. [hG'.1])
      |>.IsReduced := by
  classical
  wlog nontrivial : Nontrivial R
  · rw [not_nontrivial_iff_subsingleton] at nontrivial
    simp
  rw [IsReduced.isReduced_def]
  constructor
  · simpa using hG'.1
  have := hG'.2
  simp_rw [Set.mem_image]
  rintro _ ⟨p, ⟨hp, rfl⟩⟩
  simp_rw [support_leadingTerm' (hG'.1 p hp).ne_zero, Finset.mem_singleton]
  rintro _ rfl _ ⟨q, ⟨hq, rfl⟩⟩ hqp
  simp [degree_leadingTerm', this _ hp _ hq (by aesop)]

-- lemσisReduced_span_monomial_iff {R : Type*} [CommSemiring R] {s : Set (σ →₀ ℕ)}
--     {I : Ideal (MvPolynomial σ R)}
--     (h : m.IsGroebnerBasis ((MvPolynomial.monomial · (1 : R)) '' {x | Minimal (· ∈ s) x}) I) :
--     h.IsReduced := by
--   classical
--   rw [isReduced_def]
--   constructor
--   · simp
--   simp_rw [Set.mem_image, Set.mem_setOf]
--   rintro p ⟨p', ⟨hp', rfl⟩⟩ a ha q ⟨q', ⟨hq', rfl⟩⟩ hqp
--   simp [monomial_eq_monomial_iff] at hqp
--   have : Nontrivial R := nontrivial_of_ne _ _ hqp.2
--   simp at ha
--   subst ha
--   simp [degree_monomial]
--   by_contra! hq'p'
--   exact hqp.1 <| le_antisymm hq'p' <| hp'.le_of_le (hq'.prop) hq'p'


-- lemma _root_.Set.eq_iff_of_image_eq {α β : Type*} {f : α → β} {s t : Set α}
--     (hf : f '' s = f '' t) : s = t ↔ ∀ a ∈ s, ∀ b ∈ t, f s = f t

-- this requires `R` to be nontrivial, or the reduced GB can be `∅` or `{0}`.
lemma IsReduced.unique {R : Type*} [CommRing R] [Nontrivial R]
    {G₁ G₂ : Set (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)}
    {hG₁ : m.IsGroebnerBasis G₁ I} (hG₁' : hG₁.IsReduced)
    {hG₂ : m.IsGroebnerBasis G₂ I} (hG₂' : hG₂.IsReduced) :
    G₁ = G₂ := by
  classical
  have : m.leadingTerm '' G₁ = m.leadingTerm '' G₂ := by
    ext p
    wlog hp : p ∈ m.leadingTerm '' G₁ ∧ p ∉ m.leadingTerm '' G₂ generalizing G₁ G₂ with h
    · by_contra!
      specialize h hG₂' hG₁' (by tauto)
      tauto
    obtain hLTG₁ := hG₁'.isMinimal.isReduced_leadingTerm.isMinimal
    unfold IsMinimal at hLTG₁
    set_option push_neg.use_distrib true in
    contrapose! hLTG₁
    right
    have h₁ := hG₁.2
    have h₂ := hG₂.2
    rw! [hG₁'.isMinimal.image_leadingTerm_eq_image_monomial_one,
      hG₂'.isMinimal.image_leadingTerm_eq_image_monomial_one] at *
    simp [m.degree_monomial, and_comm (a := _ ≠ _), ← lt_iff_le_and_ne]
    have : p ∈ Ideal.span ((fun p ↦ monomial (m.degree p) 1) '' G₂) := by
      rw [← h₂, h₁]
      exact Set.mem_of_subset_of_mem Ideal.subset_span hp.1
    obtain ⟨p, hpG₁, rfl⟩ := (Set.mem_image ..).mp hp.1
    use p, hpG₁
    rw [← Set.image_image (monomial · 1) m.degree G₂, mem_ideal_span_monomial_image] at this
    simp at this hp
    obtain ⟨b₂, hb₂G₂, hb₂p⟩ := this
    replace hb₂p := lt_of_le_of_ne hb₂p <| hp.2 _ hb₂G₂
    clear hp
    have : monomial (m.degree b₂) (1 : R) ∈
      Ideal.span ((fun p ↦ monomial (m.degree p) 1) '' G₁) := by
      rw [← h₁, h₂]
      exact Set.mem_of_subset_of_mem Ideal.subset_span <| Set.mem_image_of_mem _ hb₂G₂
    rw [← Set.image_image (monomial · 1) m.degree G₁, mem_ideal_span_monomial_image] at this
    simp at this
    obtain ⟨b₁, hb₁G₁, hb₁p⟩ := this
    exact ⟨b₁, hb₁G₁, lt_of_le_of_lt hb₁p hb₂p⟩

  /- We suppose there exists `p₁ ∈ G₁` and `p₂ ∈ G₂` s.t. `m.degree p₁ = m.degree p₂` and `p₁ ≠ p₂`,
  and prove contradiction about remainder of `p₁ - p₂` that it is unique but can be both `0` and
  `p₁ - p₂`. This contradiction is easy to obtain in informal proof. -/
  ext p₁
  wlog hp₁ : p₁ ∈ G₁ ∧ p₁ ∉ G₂ generalizing G₁ G₂ with h
  · specialize h hG₂' hG₁' this.symm
    aesop
  obtain ⟨hp₁, hp₂'⟩ := hp₁
  exfalso
  obtain ⟨p₂, ⟨hp₂, hp₁₂⟩⟩ := Set.mem_image .. |>.mp <| this ▸ (Set.mem_image_of_mem _ hp₁)
  rw [isReduced_def] at hG₁' hG₂'
  simp [leadingTerm, monomial_eq_monomial_iff, (hG₂'.1 p₂ hp₂).ne_zero] at hp₁₂
  suffices rem_self : m.IsRemainder (p₁ - p₂) G₁ (p₁ - p₂) by
    have := I.sub_mem (Set.mem_of_subset_of_mem hG₁.1 hp₁) (Set.mem_of_subset_of_mem hG₂.1 hp₂)
    rw [← m.remainder_eq_zero_iff_mem_ideal_of_isGroebner _ hG₁ rem_self, sub_eq_zero] at this
    · exact hp₂' <| this ▸ hp₂
    exact fun p hp ↦ by simp [hG₁'.1 p hp |>.leadingCoeff_eq_one]
  rw [IsRemainder.self_iff]
  rintro a ha q hq -
  replace ha' := Finset.mem_union.mp <| Finset.mem_of_subset (support_sub ..) ha
  by_cases hqp : m.degree q = m.degree p₁
  · apply not_imp_not.mpr (m.toSyn_monotone (a := m.degree q) (b := a))
    push_neg
    apply lt_of_le_of_ne
    · rcases ha' with ha | ha
      · exact hqp ▸ m.le_degree_of_mem_support ha
      · exact hqp ▸ hp₁₂.1 ▸ m.le_degree_of_mem_support ha
    contrapose! ha
    rw [m.toSyn.apply_eq_iff_eq] at ha
    simp_rw [leadingCoeff, hp₁₂.1, ← hqp] at hp₁₂
    simp [ha, hp₁₂.2]
  have hqnep : q ≠ p₁ := by contrapose! hqp; simp [hqp]
  rcases ha' with ha | ha
  · exact hG₁'.2 _ hp₁ _ ha _ hq hqnep
  obtain ⟨q', hq'⟩ := Set.mem_image .. |>.mp <| this ▸ (Set.mem_image_of_mem _ hq)
  simp [leadingTerm, monomial_eq_monomial_iff, (hG₁'.1 q hq).ne_zero] at hq'
  rw [← hq'.2.1]
  apply hG₂'.2 _ hp₂ _ ha _ hq'.1
  contrapose! hqp
  simp [← hq'.2.1, ← hp₁₂.1, hqp]

lemma IsMinimal.isGroebnerBasis_of_isMinimal_leadingTerm {R} [CommRing R]
    {G : Set (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)}
    (hG : m.IsGroebnerBasis (m.leadingTerm '' G) (Ideal.span <| m.leadingTerm '' I))
    (hG' : hG.IsMinimal) (hGsubset : G ⊆ I) :
    m.IsGroebnerBasis G I := by
    classical
    refine ⟨hGsubset, ?_⟩
    have eq := hG.2
    rw [Set.image_image] at eq
    have h₁ : m.leadingTerm '' G = (m.leadingTerm ∘ m.leadingTerm) '' G := by
      apply Set.image_congr
      intro g hg
      dsimp
      rw [leadingTerm_leadingTerm]
    apply le_antisymm
    ·
      simp only [leadingTerm_leadingTerm] at eq
      rw [← eq]
      apply Ideal.span_mono
      rintro x ⟨p, hp, rfl⟩
      refine ⟨m.leadingTerm p, ?_, leadingTerm_leadingTerm _⟩
      apply Ideal.subset_span
      exact ⟨p, hp, rfl⟩
    ·
      apply Ideal.span_mono
      apply Set.image_mono
      exact hGsubset

lemma IsMinimal.isMinimal_of_isMinimal_leadingTerm {R} [CommRing R]
    {G : Set (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)}
    (hG : m.IsGroebnerBasis (m.leadingTerm '' G) (Ideal.span <| m.leadingTerm '' I))
    (hG' : hG.IsMinimal) (hGsubset : G ⊆ I) (hLT : G.InjOn m.leadingTerm ) :
    (hG'.isGroebnerBasis_of_isMinimal_leadingTerm hG hGsubset).IsMinimal := by
    rw [IsMinimal]
    constructor
    · intro p hp
      have h_monic_lt := hG'.1 (m.leadingTerm p) (Set.mem_image_of_mem _ hp)
      simpa using h_monic_lt
    · intro p hp q hq h_neq
      contrapose! h_neq
      apply hLT hq hp
      by_contra h_lt_neq
      apply hG'.2 (m.leadingTerm p) (Set.mem_image_of_mem _ hp)
              (m.leadingTerm q) (Set.mem_image_of_mem _ hq)
              h_lt_neq
      simpa using h_neq

lemma IsMinimal.isGroebnerBasis_image_isRemainder
    (hG' : hG.IsMinimal)
    (f : G → MvPolynomial σ R) (hf : ∀ g, m.IsRemainder g.val (G \ {g.val}) (f g)) :
    m.IsGroebnerBasis (Set.range f) I := by
    classical
    refine ⟨?_, ?_⟩
    · rintro _ ⟨g, rfl⟩
      have := (hf g).1
      obtain ⟨coef, h_eq, -⟩ := this

      sorry
    ·
      sorry

lemma IsReduced.isReduced_image_isRemainder_of_IsMinimal (hG' : hG.IsMinimal)
    (f : G → MvPolynomial σ R) (hf : ∀ g, m.IsRemainder g.val (G \ {g.val}) (f g)) :
    hG'.isGroebnerBasis_image_isRemainder f hf |>.IsReduced := sorry

end MonomialOrder.IsGroebnerBasis
