import Mathlib-- should be removed later
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Finiteness.Basic
import Groebner.Set
import Groebner.Ideal
import Groebner.Defs

namespace MonomialOrder
open MvPolynomial
section Field

-- set_option linter.unusedTactic false

variable {σ : Type*} {m : MonomialOrder σ}
variable {s : σ →₀ ℕ} {k : Type*} [Field k] {R : Type*} [CommRing R]
variable (p : MvPolynomial σ k)
variable (G : Finset (MvPolynomial σ k)) (I : Ideal (MvPolynomial σ k))

/--
Let $I \subseteq k[x_1, \ldots, x_n]$ be an ideal. Then there exists a finite subset $G = \{g_1, \ldots, g_t\}$ of $I$ such that $G$ is a Gröbner basis for $I$.
-/
theorem exists_isGroebnerBasis [Finite σ] :
    ∃ G : Finset (MvPolynomial σ k), IsGroebnerBasis m G ↑I := by
  have key : (Ideal.span (α:=MvPolynomial σ k) (m.leadingTerm '' ↑I)).FG :=
    (inferInstance : IsNoetherian _ _).noetherian _
  simp only [Ideal.fg_span_iff_fg_span_finset_subset, Set.subset_image_iff] at key
  rcases key with ⟨s, ⟨G', hG'I, hG's⟩, hIs⟩
  obtain ⟨G, hG, hGG', -⟩ :=
    Set.finset_subset_preimage_of_finite_image (hG's.symm ▸ Finset.finite_toSet s)
  use G
  constructor
  · exact hG.trans hG'I
  · rw [hIs, hGG', hG's]

/-- Given a remainder `r` of a polynomial `p` on division by a Gröbner basis `G` of an ideal `I`,
the remainder `r` is 0 if and only if `p` is in the ideal `I`.

Any leading coefficient of polynomial in the Gröbner basis `G` is required to be a unit.

Formally:

Let $G = \{g_1, \dots, g_t\}$ be a Gröbner basis for an ideal $I \subseteq k[x_1, \dots, x_n]$ and let $f \in k[x_1, \dots, x_n]$. Then $f \in I$ if and only if the remainder on division of $f$ by $G$ is zero.
-/
-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
theorem remainder_eq_zero_iff_mem_ideal_of_isGroebner
    {p : MvPolynomial σ R} {G : Finset (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)}
    {r : MvPolynomial σ R} (hG : ∀ g ∈ G, IsUnit (m.leadingCoeff g)) (h : m.IsGroebnerBasis G I)
    (hr : m.IsRemainder p G r) :
    r = 0 ↔ p ∈ I := by
  constructor
  · rw [← m.mem_ideal_iff_of_isRemainder h.1 hr]
    simp_intro ..
  · intro h_p_mem
    by_contra hr_ne_zero
    have h₃: m.leadingTerm r ∉ Ideal.span (m.leadingTerm '' ↑G) := by
      nth_rewrite 1 [leadingTerm]
      apply term_notMem_span_leadingTerm_of_isRemainder hG hr
      exact (m.degree_mem_support_iff r).mpr hr_ne_zero
    rcases h with ⟨h_G', h_span⟩
    obtain ⟨⟨q, h_p_eq_sum_r, h_r_reduced⟩, h_degree⟩ := hr
    have h₁: (Finsupp.linearCombination (MvPolynomial σ R) fun g' ↦ ↑g') q ∈ I := by
      rw [Finsupp.linearCombination_apply]
      rw [Finsupp.sum]
      apply Ideal.sum_mem I
      intro a h_a_in_support
      have h₂: ↑a ∈ G := by
        exact Finset.coe_mem a
      exact Submodule.smul_mem I (q a) (h_G' h₂)
    rw [h_p_eq_sum_r] at h_p_mem
    have h₂: r ∈ I := by
      exact (Submodule.add_mem_iff_right I h₁).mp h_p_mem
    have h₄: m.leadingTerm r ∈ Ideal.span (m.leadingTerm '' ↑G) := by
      rw [←h_span]
      apply Ideal.subset_span
      apply Set.mem_image_of_mem
      exact h₂
    exact h₃ h₄

/-- Given a remainder `r` of a polynomial `p` on division by a Gröbner basis `G` of an ideal `I`,
the remainder `r` is 0 if and only if `p` is in the ideal `I`.

It is a variant of `MonomialOrder.remainder_eq_zero_iff_mem_ideal_of_isGroebner`, allowing the
finite set to contain also 0, besides polynomials with invertible leading coefficients. -/
-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
theorem remainder_eq_zero_iff_mem_ideal_of_isGroebner₀ {p : MvPolynomial σ R}
    {G : Finset (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)} {r : MvPolynomial σ R}
    (hG : ∀ g ∈ G, IsUnit (m.leadingCoeff g) ∨ g = 0) (h : m.IsGroebnerBasis G I)
    (hr : m.IsRemainder p G r) :
    r = 0 ↔ p ∈ I := by
  rw [← m.isGroebnerBasis_erase_zero] at h
  rw [← m.isRemainder_sdiff_singleton_zero_iff_isRemainder] at hr
  refine m.remainder_eq_zero_iff_mem_ideal_of_isGroebner ?_ h ?_
  · simp_intro .. [or_iff_not_imp_right.mp (hG _ _)]
  · convert hr
    simp

/-- Given a remainder `r` of a polynomial `p` on division by a Gröbner basis `G` of an ideal `I`,
the remainder `r` is 0 if and only if `p` is in the ideal `I`.

It is variant of `MonomialOrder.remainder_eq_zero_iff_mem_ideal_of_isGroebner`, over a field and
without hypothesis on leading coefficients in the finite set. -/
-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
theorem remainder_eq_zero_iff_mem_ideal_of_isGroebner' {p : MvPolynomial σ k}
    {G : Finset (MvPolynomial σ k)} {I : Ideal (MvPolynomial σ k)}
    {r : MvPolynomial σ k}
    (h : m.IsGroebnerBasis G I)
    (hr : m.IsRemainder p G r) :
    r = 0 ↔ p ∈ I := by
  refine remainder_eq_zero_iff_mem_ideal_of_isGroebner₀ ?_ h hr
  simp [em']

-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
theorem isRemainder_zero_iff_mem_ideal_of_isGroebner {p : MvPolynomial σ R}
    {G : Finset (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)}
    (hG : ∀ g ∈ G, IsUnit (m.leadingCoeff g))
    (h : m.IsGroebnerBasis G I) :
    m.IsRemainder p G 0 ↔ p ∈ I := by
  constructor
  · intro hr
    apply (remainder_eq_zero_iff_mem_ideal_of_isGroebner hG h hr).mp rfl
  · intro hp
    have hor: ∀ g ∈ G, IsUnit (m.leadingCoeff g) ∨ g = 0 := by
      exact fun g a ↦ Or.symm (Or.inr (hG g a))
    have h₁:  ∃ (r : MvPolynomial σ R), m.IsRemainder p G r := by
      exact div_set'₀ m hor p
    obtain ⟨r, hr⟩ := h₁
    have h₂: r = 0 := by
      exact (remainder_eq_zero_iff_mem_ideal_of_isGroebner hG h hr).mpr hp
    rw [h₂] at hr
    exact hr

-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
lemma isRemainder_zero_iff_mem_ideal_of_isGroebner₀ {p : MvPolynomial σ R}
    {G : Finset (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)}
    (hG : ∀ g ∈ G, IsUnit (m.leadingCoeff g) ∨ g = 0)
    (h : m.IsGroebnerBasis G I) :
    m.IsRemainder p G 0 ↔ p ∈ I := by
  rw [← m.isGroebnerBasis_erase_zero] at h
  rw [← m.isRemainder_sdiff_singleton_zero_iff_isRemainder]
  convert m.isRemainder_zero_iff_mem_ideal_of_isGroebner ?_ h
  · simp
  simp_intro a b [or_iff_not_imp_right.mp (hG _ _)]

-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
lemma isRemainder_zero_iff_mem_ideal_of_isGroebner' {p : MvPolynomial σ k}
    {G : Finset (MvPolynomial σ k)} {I : Ideal (MvPolynomial σ k)}
    (h : m.IsGroebnerBasis G I) :
    m.IsRemainder p G 0 ↔ p ∈ I := by
  refine m.isRemainder_zero_iff_mem_ideal_of_isGroebner₀ ?_ h
  simp [em']

-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
lemma exists_degree_le_degree_of_isRemainder_zero {R : Type*} [CommSemiring R]
    (p : MvPolynomial σ R) (hp : p ≠ 0) (B : Set (MvPolynomial σ R))
    (hB : ∀ b ∈ B, IsRegular (m.leadingCoeff b))
    (h : m.IsRemainder p B 0) :
    ∃ b ∈ B, m.degree b ≤ m.degree p := by
  classical
  rw [isRemainder_def''] at h
  rcases h with ⟨⟨g, B', h₁, hsum, h₃⟩, h₄⟩
  simp at hsum
  have : m.degree p ∈ p.support := m.degree_mem_support hp
  rw [hsum] at this
  obtain ⟨b, hb⟩ := Finset.mem_biUnion.mp <| hsum.symm ▸ Finset.mem_of_subset support_sum this
  use b
  constructor
  · exact h₁ hb.1
  · rcases hb with ⟨hb₁, hb₂⟩
    have := h₃ b hb₁
    obtain hgbne0 : g b ≠ 0 := by
      contrapose! hb₂
      simp [hb₂]
    apply le_degree (m:=m) at hb₂
    rw [mul_comm b] at this
    apply le_antisymm this at hb₂
    simp at hb₂
    rw [degree_mul_of_isRegular_right hgbne0] at hb₂
    · exact le_of_add_le_right (le_of_eq hb₂)
    exact hB b (Set.mem_of_mem_of_subset hb₁ h₁)

-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
lemma exists_degree_le_degree_of_isRemainder_zero₀ {R : Type*} [CommSemiring R]
    (p : MvPolynomial σ R) (hp : p ≠ 0) (B : Set (MvPolynomial σ R))
    (hB : ∀ b ∈ B, IsRegular (m.leadingCoeff b) ∨ b = 0)
    (h : m.IsRemainder p B 0) :
    ∃ b ∈ B, b ≠ 0 ∧ m.degree b ≤ m.degree p := by
  rw [← isRemainder_sdiff_singleton_zero_iff_isRemainder] at h
  convert m.exists_degree_le_degree_of_isRemainder_zero p hp (B \ {0}) ?_ h using 2
  · simp
    rw [and_assoc]
  · simp_intro a b [or_iff_not_imp_right.mp (hB _ _)]

-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
lemma exists_degree_le_degree_of_isRemainder_zero' (p : MvPolynomial σ k) (hp : p ≠ 0)
    (B : Set (MvPolynomial σ k)) (h : m.IsRemainder p B 0) :
    ∃ b ∈ B, b ≠ 0 ∧ m.degree b ≤ m.degree p :=
  m.exists_degree_le_degree_of_isRemainder_zero₀ p hp B (by simp [isRegular_iff_ne_zero, em']) h


-- lemma remainder_degree_ne_iff (p r : MvPolynomial σ k) (hp : p ≠ 0) (B : Set (MvPolynomial σ k)) (hr : m.IsRemainder p B r) :
--   (m.degree r ≠ m.degree p ∨ r = 0) ↔ ∃ b ∈ B, m.degree b ≤ m.degree p := by
--   constructor
--   · intro h
--     rw [isRemainder_def''] at hr
--     rcases hr with ⟨⟨g, B', h₁, hsum, h₃⟩, h₄⟩
--     --
--     rw [hsum] at h
--     have :
--     -- unfold IsRemainder at hr

--     sorry
--   ·
--     sorry

/--
Let $G = \{g_1, \ldots, g_t\}$ be a Gröbner basis for an ideal $I \subseteq k[x_1, \ldots, x_n]$. Then $G$ is a basis for the vector space $I$ over $k$.
-/
-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
theorem ideal_eq_span_of_isGroebner {G : Finset (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)}
    (hG : ∀ g ∈ G, IsUnit (m.leadingCoeff g)) (h : m.IsGroebnerBasis G I) :
    I = Ideal.span G := by
  apply le_antisymm
  · intro p hp
    rw [← isRemainder_zero_iff_mem_ideal_of_isGroebner hG h] at hp
    obtain ⟨⟨f, h_eq, h_deg⟩, h_remain⟩ := hp
    rw [h_eq, Finsupp.linearCombination_apply, add_zero]
    apply Ideal.sum_mem
    intro g hg
    rcases g with ⟨g, gG'⟩
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span gG')
  · intro p hp
    suffices Ideal.span ↑G ≤ I by
      exact this hp
    apply Ideal.span_le.mpr
    intro p hp'
    rw [SetLike.mem_coe]
    exact h.1 hp'

-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
theorem isGroebnerBasis_iff_ideal_eq_span_and_isGroebner_span (G : Finset (MvPolynomial σ R))
    (I : Ideal (MvPolynomial σ R)) (hG : ∀ g ∈ G, IsUnit (m.leadingCoeff g)) :
    m.IsGroebnerBasis G I ↔ (I = Ideal.span G ∧ m.IsGroebnerBasis G (Ideal.span G)) := by
  constructor
  · intro this
    simpa [ideal_eq_span_of_isGroebner hG this]
  · simp_intro ..

-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
theorem isGroebnerBasis_iff_span_eq_and_degree_le (G : Finset (MvPolynomial σ R))
    (I : Ideal (MvPolynomial σ R)) (hG : ∀ g ∈ G, IsUnit (m.leadingCoeff g)) :
    m.IsGroebnerBasis G I ↔
      Ideal.span G = I ∧ ∀ p ∈ I, p ≠ 0 → ∃ g ∈ G, m.degree g ≤ m.degree p := by
  classical
  constructor
  · intro h
    exists (m.ideal_eq_span_of_isGroebner hG h).symm
    intro p hp hp0
    apply m.exists_degree_le_degree_of_isRemainder_zero _ hp0 ↑G
      (by simp_intro .. [(hG _ _).isRegular])
    exact (m.isRemainder_zero_iff_mem_ideal_of_isGroebner hG h).mpr hp
  · rintro ⟨hG', h_degree⟩
    constructor
    · exact hG' ▸ Submodule.subset_span
    · rw [← hG', ←SetLike.coe_set_eq]
      apply Set.eq_of_subset_of_subset
      · apply Ideal.span_le.mpr
        intro p' hp
        rcases hp with ⟨p, hp', hp'₁⟩
        rw [hG'] at hp'
        rw [←hp'₁, leadingTerm, SetLike.mem_coe,
          m.span_leadingTerm_eq_span_monomial (by simp_intro .. [hG]),
          ← Set.image_image (monomial · 1) _ _, mem_ideal_span_monomial_image]
        intro j hj
        simp [MonomialOrder.leadingCoeff_eq_zero_iff] at hj
        simp
        exact hj.1 ▸ h_degree p hp' hj.2
      · rw [hG']
        apply Ideal.span_mono
        exact Set.image_mono (hG' ▸ Submodule.subset_span)

/-- A finite set of polynomials is a Gröbner basis of an ideal if and only if it is a subset of
this ideal and 0 is a remainder of each member of this ideal on division by this finite set.

Any leading coefficient of polynomial in the finite set is required to be a unit. -/
-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
theorem isGroebnerBasis_iff_subset_ideal_and_isRemainder_zero
    (G : Finset (MvPolynomial σ R)) (I : Ideal (MvPolynomial σ R))
    (hG : ∀ g ∈ G, IsUnit (m.leadingCoeff g)) :
    m.IsGroebnerBasis G I ↔ G.toSet ⊆ I ∧ ∀ p ∈ I, m.IsRemainder p G 0 := by
  classical
  constructor
  · intro h
    exists h.1
    intro p h_p_in_I
    rwa [isRemainder_zero_iff_mem_ideal_of_isGroebner hG h]
  · intro h
    rcases h with ⟨h_G, h_remainder⟩
    rw [m.isGroebnerBasis_iff_span_eq_and_degree_le G I hG]
    constructor
    · rw [←SetLike.coe_set_eq]
      norm_cast
      apply le_antisymm (Ideal.span_le.mpr h_G)
      intro p hp
      specialize h_remainder p hp
      have: Ideal.span G ≤ I:= by
        apply Ideal.span_le.mpr
        intro p hp'
        rw [SetLike.mem_coe]
        exact h_G hp'
      have h1: (G : Set <| MvPolynomial σ R) ⊆ (Ideal.span (α := MvPolynomial σ R) ↑G) := by
        exact Ideal.subset_span
      apply (mem_ideal_iff_of_isRemainder h1 h_remainder).mp
      simp
    · intro p hp hp0
      exact m.exists_degree_le_degree_of_isRemainder_zero p hp0 G
        (by simp_intro .. [(hG _ _).isRegular]) <|
          h_remainder p hp

/-- A finite set of polynomials is a Gröbner basis of an ideal if and only if it is a subset of
this ideal and 0 is a remainder of each member of this ideal on division by this finite set.

It is a variant of `MonomialOrder.isGroebnerBasis_iff_subset_ideal_and_isRemainder_zero`, allowing
the finite set to contain also 0, besides polynomials with invertible leading coefficients. -/
-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
theorem isGroebnerBasis_iff_subset_ideal_and_isRemainder_zero₀ (G : Finset (MvPolynomial σ R))
    (I : Ideal (MvPolynomial σ R)) (hG : ∀ g ∈ G, IsUnit (m.leadingCoeff g) ∨ g = 0) :
    m.IsGroebnerBasis G I ↔ G.toSet ⊆ I ∧ ∀ p ∈ I, m.IsRemainder p G 0 := by
  rw [← m.isGroebnerBasis_erase_zero]
  convert m.isGroebnerBasis_iff_subset_ideal_and_isRemainder_zero (G.erase 0) I _ using 2
  · simp
  · simp [m.isRemainder_sdiff_singleton_zero_iff_isRemainder]
  · simp_intro .. [or_iff_not_imp_right.mp (hG _ _)]

/-- A finite set of polynomials is a Gröbner basis of an ideal if and only if it is a subset of
this ideal and 0 is a remainder of each member of this ideal on division by this finite set.

It is a variant of `MonomialOrder.isGroebnerBasis_iff_subset_ideal_and_isRemainder_zero`,
over a field and without hypothesis on leading coefficients in the finite set.

Formally:

Let $G = \{g_1, \ldots, g_t\}$ be a finite subset of $k[x_1, \ldots, x_n]$.
Then $G$ is a Gröbner basis for the ideal $I = \langle G \rangle$ if and only if
for every $f \in I$, the remainder of $f$ on division by $G$ is zero.
whose leading coefficients are invertible with respect to a monomial order
-/
-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
theorem isGroebnerBasis_iff_subset_ideal_and_isRemainder_zero' :
    m.IsGroebnerBasis G I ↔ G.toSet ⊆ I ∧ ∀ p ∈ I, m.IsRemainder p G 0 :=
  m.isGroebnerBasis_iff_subset_ideal_and_isRemainder_zero₀ G I (by simp [em'])

theorem span_leadingTerm_eq_span_monomial_of_isGroebner {G : Finset (MvPolynomial σ R)}
    {I : Ideal (MvPolynomial σ R)}
    (h : m.IsGroebnerBasis G I) (hG : ∀ g ∈ G, IsUnit (m.leadingCoeff g)) :
    Ideal.span (m.leadingTerm '' ↑G) =
    Ideal.span ((fun p ↦ monomial (m.degree p) (1 : R)) '' (I \ {(0 : MvPolynomial σ R)})) := by
  classical
  by_cases hR : Nontrivial R
  · rw [m.span_leadingTerm_eq_span_monomial (B := (↑G : Set (MvPolynomial σ R))) hG]
    apply le_antisymm
    · rw [Ideal.span_le]
      refine subset_trans ?_ Submodule.subset_span
      apply Set.image_mono
      apply Set.subset_diff_singleton h.1
      contrapose! hG
      use 0
      simpa [hG]
    · rw [Ideal.span_le]
      intro x
      simp
      intro y hy hy0 hxy
      rw [← hxy, ← Set.image_image (monomial · 1) _ _, mem_ideal_span_monomial_image]
      simp
      exact ((m.isGroebnerBasis_iff_span_eq_and_degree_le _ _ hG).mp h).2 y hy hy0
  · rw [not_nontrivial_iff_subsingleton] at hR
    exact ((Submodule.subsingleton_iff _).mpr inferInstance).elim _ _

-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
theorem span_leadingTerm_eq_span_monomial_of_isGroebner₀ {G : Finset (MvPolynomial σ R)}
    {I : Ideal (MvPolynomial σ R)}
    (h : m.IsGroebnerBasis G I) (hG : ∀ g ∈ G, IsUnit (m.leadingCoeff g) ∨ g = 0) :
    Ideal.span (m.leadingTerm '' ↑G) =
    Ideal.span ((fun p ↦ monomial (m.degree p) (1 : R)) '' (I \ {(0 : MvPolynomial σ R)})) := by
  rw [← m.isGroebnerBasis_erase_zero] at h
  convert m.span_leadingTerm_eq_span_monomial_of_isGroebner h _ using 1
  · simp [m.image_leadingTerm_sdiff_singleton_zero]
  · simp_intro .. [or_iff_not_imp_right.mp (hG _ _)]

/-- Remainder of any polynomial on division by Gröbner basis exists and is unique.

Any leading coefficient of polynomial in the Gröbner basis is required to be a unit. -/
-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
theorem existsUnique_isRemainder_of_isGroebnerBasis {G : Finset (MvPolynomial σ R)}
    {I : Ideal (MvPolynomial σ R)}
    (h : m.IsGroebnerBasis G I) (hG : ∀ g ∈ G, IsUnit (m.leadingCoeff g)) (p : MvPolynomial σ R) :
    ∃! (r : MvPolynomial σ R), m.IsRemainder p G r := by
  classical
  apply existsUnique_of_exists_of_unique (m.div_set' hG p)
  intro r₁ r₂ hr₁ hr₂
  rw [← sub_eq_zero]
  by_contra! hrne0
  have hr := (m.degree_mem_support_iff _).mpr hrne0
  apply m.sub_monomial_notMem_span_leadingTerm_of_isRemainder (B := ↑G) hG hr₁ hr₂ at hr
  rw [m.span_leadingTerm_eq_span_monomial_of_isGroebner h hG] at hr
  apply hr
  apply Submodule.mem_span_of_mem
  apply Set.mem_image_of_mem
  simp [hrne0]
  exact m.sub_mem_ideal_of_isRemainder_of_subset_ideal h.1 hr₁ hr₂

/-- Remainder of any polynomial on division by Gröbner basis exists and is unique.

It is a variant of `MonomialOrder.existsUnique_isRemainder_of_isGroebnerBasis`, allowing the
Gröbner basis to contain also 0, besides polynomials with invertible leading coefficients. -/
-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
theorem existsUnique_isRemainder_of_isGroebnerBasis₀ {G : Finset (MvPolynomial σ R)}
    {I : Ideal (MvPolynomial σ R)}
    (h : m.IsGroebnerBasis G I) (hG : ∀ g ∈ G, IsUnit (m.leadingCoeff g) ∨ g = 0)
    (p : MvPolynomial σ R) :
    ∃! (r : MvPolynomial σ R), m.IsRemainder p G r := by
  rw [← m.isGroebnerBasis_erase_zero] at h
  simp_rw [← m.isRemainder_sdiff_singleton_zero_iff_isRemainder p G]
  convert m.existsUnique_isRemainder_of_isGroebnerBasis h _ p
  · simp
  · simp_intro .. [or_iff_not_imp_right.mp (hG _ _)]

lemma sPolynomial_ne_zero (f g : MvPolynomial σ R) (h : m.sPolynomial f g ≠ 0) :
    (0 < (m.toSyn <| m.degree f)) ∨ (0 < (m.toSyn <| m.degree g)) := by
  simp [MonomialOrder.sPolynomial] at h
  contrapose! h
  rcases h with ⟨h₁, h₂⟩
  rw [← eq_zero_iff, EmbeddingLike.map_eq_zero_iff] at h₁ h₂
  simp [h₁, h₂]
  rw [degree_eq_zero_iff] at h₁ h₂
  nth_rewrite 1 [h₁]
  nth_rewrite 2 [h₂]
  ring

/--
Let $f, h_1, \dots, h_m \in k[\mathbf{x}] \setminus \{0\}$, and
suppose
  $$f = c_1 h_1 + \cdots + c_m h_m, \quad \text{with } c_i \in k.$$

If $$\mathrm{lm}(h_1) = \mathrm{lm}(h_2) = \cdots = \mathrm{lm}(h_i) > \mathrm{lm}(f),$$ then
$$f = \sum_{1 \leq i < j \leq m} c_{i,j} S(h_i, h_j), \quad c_{i,j} \in k.$$
Furthermore, if $S(h_i, h_j) \ne 0$, then $\mathrm{lm}(h_i) > \mathrm{lm}(S(h_i, h_j))$.
-/
-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
lemma sPolynomial_decomposition {d : m.syn} {ι : Type*}
    {B : Finset ι} {g : ι → MvPolynomial σ R}
    (hd : ∀ b ∈ B,
      (m.toSyn <| m.degree <| g b) = d ∧ IsUnit (m.leadingCoeff <| g b) ∨ g b = 0)
    (hfd : (m.toSyn <| m.degree <| ∑ b ∈ B, g b) < d) :
    ∃ (c : ι → ι → R),
      ∑ b ∈ B, g b = ∑ b₁ ∈ B, ∑ b₂ ∈ B, (c b₁ b₂) • m.sPolynomial (g b₁) (g b₂) := by
  classical
  induction B using Finset.induction_on with
  | empty => simp
  | insert b B hb h =>
    by_cases hb0 : g b = 0
    · simp [Finset.sum_insert hb, hb0] at hd hfd ⊢
      exact h hd hfd
    simp [Finset.sum_insert hb, hb0] at hfd hd
    obtain ⟨⟨deg_gb_eq_d, isunit_gb⟩, hd⟩ := hd
    use fun b₁ b₂ ↦ if b₂ = b then ↑isunit_gb.unit⁻¹ else 0
    simp [Finset.sum_insert hb, hb]
    simp [← deg_gb_eq_d] at *
    clear d
    trans ∑ b' ∈ B, (g b' - (m.leadingCoeff (g b') * ↑isunit_gb.unit⁻¹) • g b)
    · rw [Finset.sum_sub_distrib, add_comm, sub_eq_add_neg,
        ← Finset.sum_smul, ← Finset.sum_mul, ← neg_smul]
      nth_rewrite 1 [← one_smul R <| g b]
      congr
      rw [← neg_mul, eq_comm]
      convert isunit_gb.mul_val_inv
      rw [← add_eq_zero_iff_neg_eq']
      trans (g b).coeff (m.degree <| g b) + ∑ i ∈ B, (g i).coeff (m.degree <| g b)
      · unfold leadingCoeff
        congr 1
        apply Finset.sum_congr rfl
        intro b' hb'
        rcases hd b' hb' with h | h <;> simp [h]
      · rw [← coeff_sum, ← coeff_add, ← notMem_support_iff]
        exact m.notMem_support_of_degree_lt hfd
    · apply Finset.sum_congr rfl
      intro b' hb'
      rw [sPolynomial]
      by_cases h : g b' = 0
      · simp [h]
      have := hd b' hb'
      simp [h] at this
      simp [this, smul_eq_C_mul, mul_sub, ← mul_assoc _ _ (g b), ← mul_assoc _ _ (g b'),]
      simp_rw [← C_mul]
      simp [mul_comm]

-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
lemma sPolynomial_decomposition' {d : m.syn} {ι : Type*}
    {B : Finset ι} (g : ι → MvPolynomial σ k)
    (hd : ∀ b ∈ B, (m.toSyn <| m.degree <| g b) = d ∨ g b = 0)
    (hfd : (m.toSyn <| m.degree <| ∑ b ∈ B, g b) < d) :
    ∃ (c : ι → ι → k),
      ∑ b ∈ B, g b = ∑ b₁ ∈ B, ∑ b₂ ∈ B, (c b₁ b₂) • m.sPolynomial (g b₁) (g b₂) := by
  refine m.sPolynomial_decomposition ?_ hfd
  simpa [and_or_right, em']

set_option maxHeartbeats 400000 in
/--
A basis $G = \{ g_1, \ldots, g_t \}$ for an ideal $I$ is a Gröbner basis if and only if $S(g_i, g_j) \to_G 0$ for all $i \neq j$.
-/
-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
theorem isGroebnerBasis_iff_isRemainder_sPolynomial_zero :
    m.IsGroebnerBasis G (Ideal.span G) ↔
    ∀ (g₁ g₂ : G), m.IsRemainder (m.sPolynomial g₁ g₂ : MvPolynomial σ k) G 0 := by
  classical
  constructor
  · intro h g₁ g₂
    rw [m.isGroebnerBasis_iff_subset_ideal_and_isRemainder_zero'] at h
    apply h.2
    apply m.sPolynomial_mem_ideal
    <;> exact Set.mem_of_mem_of_subset (by simp) h.1
  intro hG
  rw [isGroebnerBasis_iff_subset_ideal_and_isRemainder_zero']
  exists Ideal.subset_span
  intro p hp
  simp_rw [isRemainder_finset, add_zero]
  refine ⟨?_, by simp⟩
  apply Submodule.mem_span_finset.mp at hp
  obtain ⟨f, ⟨-, hf⟩⟩ := hp
  refine WellFoundedLT.induction
      (C := fun (a : m.syn) ↦
        (∃ (g : MvPolynomial σ k → MvPolynomial σ k),
          p = ∑ g' ∈ G, (g g') * g' ∧
          ∀ g' ∈ G, (m.toSyn <| m.degree <| g' * g g') ≤ a) →
        ∃ (g : MvPolynomial σ k → MvPolynomial σ k),
          p = ∑ g' ∈ G, (g g') * g' ∧
          ∀ g' ∈ G, (m.toSyn <| m.degree <| g' * g g') ≤ m.toSyn (m.degree p))
      (G.sup fun g' ↦ (m.toSyn <| m.degree <| g' * (f g'))) ?_ ?_
  · intro a h ⟨g, hg, hg₂⟩
    by_cases ha : m.toSyn (m.degree p) < a
    · simp_rw [← and_imp, ← exists_imp] at h
      apply h
      clear h
      let gg'deg := fun g' ↦ m.toSyn <| m.degree <| g g' * g'
      have hp := calc
        p = ∑ g' ∈ G, g g' * g' := hg
        _ = ∑ g' ∈ G,
              (if gg'deg g' = a then m.leadingTerm (g g') else 0) * g' +
            ∑ g' ∈ G,
              (if gg'deg g' = a then g g' - m.leadingTerm (g g') else g g') * g' := by
          simp [← Finset.sum_add_distrib, ← add_mul, ite_add_ite]
        _ = ∑ g' ∈ G,
              monomial (m.degree (g g')) (if gg'deg g' = a then m.leadingCoeff (g g') else 0) * g'
            + _ := by
          congr 2
          rw [funext_iff]
          intro x
          by_cases h : gg'deg x = a <;> simp [h, leadingTerm]

      have a_gt_zero : 0 < a := bot_lt_of_lt ha

      obtain ⟨c, hc⟩ := by
        apply m.sPolynomial_decomposition' (ι:=MvPolynomial σ k) (d:=a) (B:=G)
          (fun g' ↦ monomial (m.degree (g g'))
            (if gg'deg g' = a then m.leadingCoeff (g g') else 0) * g')
        · intro g' hg'
          simp
          by_cases hg'₂ : g' = 0 <;> simp [hg'₂]
          by_cases hg'₃ : g g' = 0 <;> simp [hg'₃]
          by_cases hg'₄ : gg'deg g' = a <;> simp [hg'₄]
          have := m.leadingCoeff_ne_zero_iff.mpr hg'₃
          rw [← hg'₄, EmbeddingLike.apply_eq_iff_eq,
            degree_mul (monomial_eq_zero.not.mpr this) hg'₂,
            degree_mul hg'₃ hg'₂, degree_monomial]
          simp [this]
        · contrapose! ha
          rw [hp, m.degree_add_of_lt]
          ·exact ha
          refine lt_of_lt_of_le ?_ ha
          apply lt_of_le_of_lt m.degree_sum_le
          rw [Finset.sup_lt_iff a_gt_zero]
          intro g' hg'
          by_cases hg'₂ : g' = 0
          · simp [hg'₂, a_gt_zero]
          by_cases hg'₃ : g g' = 0
          · simp [hg'₃, a_gt_zero]
          by_cases hg'₄ : gg'deg g' = a
          · simp [hg'₄]
            by_cases h : g g' - m.leadingTerm (g g') = 0
            · simp [h, a_gt_zero]
            refine lt_of_lt_of_le ?_ (hg₂ g' hg')
            rw [degree_mul h hg'₂, degree_mul hg'₂ hg'₃, add_comm,
              AddEquiv.map_add, AddEquiv.map_add, add_lt_add_iff_left]
            exact m.degree_sub_leadingTerm_lt_degree h
          · simp [hg'₄]
            apply lt_of_le_of_ne (mul_comm (g g') g' ▸ hg₂ g' hg')
            exact hg'₄

      simp_rw [hc, m.sPolynomial_mul_monomial] at hp
      rw [← G.sum_coe_sort] at hp
      conv at hp =>
        rhs
        arg 1
        arg 2
        intro g'
        rw [← G.sum_coe_sort]
      simp_rw [isRemainder_finset'₁] at hG
      simp [-Subtype.forall] at hG
      let q' (g'₁ g'₂ : G) := (hG g'₁ g'₂).choose
      have hq' (g'₁ g'₂ : G) := (hG g'₁ g'₂).choose_spec
      simp_rw [show ∀ (g'₁ g'₂), (hG g'₁ g'₂).choose = q' g'₁ g'₂ by intros; rfl] at hq'
      simp_rw [(hq' _ _).1] at hp
      clear_value q'
      replace hq' (g'₁ g'₂ : ↑G) := (hq' g'₁ g'₂).2
      clear hG

      simp_rw [Finset.mul_sum, ← mul_assoc, Finset.smul_sum,
        ←smul_mul_assoc, smul_monomial, Finset.sum_comm (t:=G),
        ← Finset.sum_mul, ← Finset.sum_add_distrib,
        ← add_mul] at hp
      letI g₂ := (?_ : MvPolynomial σ k → MvPolynomial σ k)
      replace hp : p = ∑ g' ∈ G, g₂ g' * g' := by exact hp

      refine ⟨(G.sup fun g' ↦ m.toSyn <| m.degree <| g₂ g' * g'), ⟨?_, ⟨g₂, ⟨hp, ?_⟩⟩⟩⟩
      · simp [g₂, Finset.sup_lt_iff a_gt_zero, add_mul]
        clear hp g₂
        intro g' hg'
        apply lt_of_le_of_lt degree_add_le
        apply max_lt
        · simp_rw [Finset.sum_mul]
          refine lt_of_le_of_lt m.degree_sum_le <| (Finset.sup_lt_iff a_gt_zero).mpr ?_
          simp
          intro g'₁ hg'₁
          refine lt_of_le_of_lt m.degree_sum_le <| (Finset.sup_lt_iff a_gt_zero).mpr ?_
          simp
          intro g'₂ hg'₂
          obtain ⟨hq', hq'0⟩ := hq' ⟨g'₁, hg'₁⟩ ⟨g'₂, hg'₂⟩
          replace hq' := hq' g' hg'
          by_cases hgg'₂ : gg'deg g'₂ ≠ a
          · simp [hgg'₂, a_gt_zero]
          by_cases hgg'₁ : gg'deg g'₁ ≠ a
          · simp [hgg'₁, a_gt_zero]
          by_cases hspoly : m.sPolynomial g'₁ g'₂ = 0
          · simp [hspoly] at hq'0
            simp [hq'0, a_gt_zero]
          simp at hq'
          simp
          rw [mul_assoc]
          apply lt_of_le_of_lt degree_mul_le
          rw [AddEquiv.map_add]
          refine add_lt_of_add_lt_right ?_ (degree_monomial_le _)
          apply lt_of_le_of_lt (add_le_add_left (mul_comm g' (q' _ _ g') ▸ hq') _)
          apply lt_of_lt_of_le (add_lt_add_left (m.degree_sPolynomial_lt_sup_degree hspoly) _)
          push_neg at hgg'₁ hgg'₂
          unfold gg'deg at hgg'₁ hgg'₂
          rw [← AddEquiv.map_add]
          have :
              (m.degree (g g'₁) + m.degree g'₁) ⊔ (m.degree (g g'₂) + m.degree g'₂)
                - m.degree g'₁ ⊔ m.degree g'₂
                + m.degree g'₁ ⊔ m.degree g'₂
              = (m.degree (g g'₁) + m.degree g'₁) ⊔ (m.degree (g g'₂) + m.degree g'₂) := by
            rw [Finsupp.ext_iff]
            intro x
            simp
            apply Nat.sub_add_cancel
            apply max_le_max <;> simp
          rw [this]
          rw [m.degree_mul'] at hgg'₁ hgg'₂
          · rw [← hgg'₁, m.toSyn.injective.eq_iff] at hgg'₂
            simp [← hgg'₁, hgg'₂]
          · contrapose! hgg'₂
            simp [hgg'₂, ne_of_lt a_gt_zero]
          · contrapose! hgg'₁
            simp [hgg'₁, ne_of_lt a_gt_zero]
        · by_cases h : gg'deg g' ≠ a
          · simp [h]
            exact lt_of_le_of_ne (mul_comm (g g') g' ▸ hg₂ g' hg') h
          push_neg at h
          simp [h]
          by_cases hLTgg' : g g' - m.leadingTerm (g g') = 0
          · simp [hLTgg', a_gt_zero]
          unfold gg'deg at h
          rw [← h] at ⊢ a_gt_zero
          apply ne_of_lt at a_gt_zero
          rw [ne_eq, eq_comm, toSyn_eq_zero_iff] at a_gt_zero
          obtain ⟨gg'_ne_zero, g_ne_zero⟩ := mul_ne_zero_iff.mp <|
            m.ne_zero_of_degree_ne_zero a_gt_zero
          rw [degree_mul hLTgg' g_ne_zero, AddEquiv.map_add,
            degree_mul gg'_ne_zero g_ne_zero, AddEquiv.map_add]
          simp [m.degree_sub_leadingTerm_lt_degree hLTgg']
      · intro g'
        rw [mul_comm]
        exact Finset.le_sup (α:=m.syn) (f:=fun g' ↦ m.toSyn <| m.degree <| g₂ g' * g')
    · exists g, hg
      exact fun g' hg' ↦ le_trans (hg₂ g' hg') (not_lt.mp ha)
  · exists f, hf.symm
    intro g' hg'
    -- why doesn't exact work here???
    apply Finset.le_sup hg'


alias buchberger_criterion := isGroebnerBasis_iff_isRemainder_sPolynomial_zero

-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
theorem isGroebnerBasis_iff_isRemainder_sPolynomial_zero' :
    m.IsGroebnerBasis G (Ideal.span G) ↔
    ∀ (g₁ g₂ : G) (r : MvPolynomial σ k),
      m.IsRemainder (m.sPolynomial g₁ g₂ : MvPolynomial σ k) G r → r = 0 := by
  constructor
  · intro h g₁ g₂ r hr
    apply (remainder_eq_zero_iff_mem_ideal_of_isGroebner' h hr).mpr
    rw [m.isGroebnerBasis_iff_subset_ideal_and_isRemainder_zero'] at h
    apply m.sPolynomial_mem_ideal
    <;> exact Set.mem_of_subset_of_mem h.1 (by simp)
  · rw [isGroebnerBasis_iff_isRemainder_sPolynomial_zero]
    intro h g₁ g₂
    obtain ⟨r, hr⟩ := m.div_set'' G (m.sPolynomial (R := k) ↑g₁ ↑g₂)
    rwa [h g₁ g₂ r hr] at hr

alias buchberger_criterion' := isGroebnerBasis_iff_isRemainder_sPolynomial_zero'

end Field
end MonomialOrder
