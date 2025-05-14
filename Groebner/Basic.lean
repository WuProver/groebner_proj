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

set_option linter.unusedTactic false

variable {σ : Type*} {m : MonomialOrder σ}
variable {s : σ →₀ ℕ} {k : Type*} [Field k] {R : Type*} [CommRing R]
variable (p : MvPolynomial σ k)
variable (G': Finset (MvPolynomial σ k)) (I : Ideal (MvPolynomial σ k))

/--
Let $I \subseteq k[x_1, \ldots, x_n]$ be an ideal. Then there exists a finite subset $G = \{g_1, \ldots, g_t\}$ of $I$ such that $G$ is a Gröbner basis for $I$.
-/
theorem exists_groebner_basis [Finite σ] :
  ∃ G' : Finset (MvPolynomial σ k), IsGroebnerBasis m G' ↑I := by
  have key : (Ideal.span (α:=MvPolynomial σ k) (m.leadingTerm '' ↑I)).FG :=
    (inferInstance : IsNoetherian _ _).noetherian _
  simp only [Ideal.fg_span_iff_fg_span_finset_subset, Set.subset_image_iff] at key
  rcases key with ⟨s, ⟨G,hGI, hGs⟩, hIs⟩
  obtain ⟨G', hG', hG'G, _⟩ := Set.finset_subset_preimage_of_finite_image (hGs.symm ▸ Finset.finite_toSet s)
  use G'
  constructor
  · exact hG'.trans hGI
  · rw [hIs, hG'G, hGs]



/--
Let $G = \{g_1, \dots, g_t\}$ be a Gröbner basis for an ideal $I \subseteq k[x_1, \dots, x_n]$ and let $f \in k[x_1, \dots, x_n]$. Then $f \in I$ if and only if the remainder on division of $f$ by $G$ is zero.
-/
theorem groebner_basis_isRemainder_zero_iff_mem_span {p : MvPolynomial σ R}
  {G' : Finset (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)}
  {r : MvPolynomial σ R}
  (hG' : ∀ g ∈ G', IsUnit (m.leadingCoeff g))
  (h : m.IsGroebnerBasis G' I)
  (hr : m.IsRemainder p G' r)
  : r = 0 ↔ p ∈ I := by
  constructor
  · intro h_zero
    rw[h_zero] at hr
    obtain ⟨⟨g, h_p, -⟩, -⟩ := hr
    rw [h_p]
    unfold MonomialOrder.IsGroebnerBasis at h
    have h₁: (Finsupp.linearCombination (MvPolynomial σ R) fun g' ↦ ↑g') g ∈ I := by
      rw [Finsupp.linearCombination_apply]
      rw[Finsupp.sum]
      apply Ideal.sum_mem I
      intro a h_a_in_support
      rcases h with ⟨h_G', h_span⟩
      have h₂: ↑a ∈ G' := by
        exact Finset.coe_mem a
      exact Submodule.smul_mem I (g a) (h_G' h₂)
    have h₂: 0 ∈ I := by
      exact Submodule.zero_mem I
    exact (Submodule.add_mem_iff_right I h₁).mpr h₂
  · intro h_p_mem
    by_contra hr_ne_zero
    have h₃: m.leadingTerm r ∉ Ideal.span (m.leadingTerm '' ↑G') := by
      nth_rewrite 1 [leadingTerm]
      apply IsRemainder_term_not_mem_leading_term_ideal hG' hr
      exact (m.degree_mem_support_iff r).mpr hr_ne_zero
    rcases h with ⟨h_G', h_span⟩
    obtain ⟨⟨q, h_p_eq_sum_r, h_r_reduced⟩, h_degree⟩ := hr
    have h₁: (Finsupp.linearCombination (MvPolynomial σ R) fun g' ↦ ↑g') q ∈ I := by
      rw [Finsupp.linearCombination_apply]
      rw[Finsupp.sum]
      apply Ideal.sum_mem I
      intro a h_a_in_support
      have h₂: ↑a ∈ G' := by
        exact Finset.coe_mem a
      exact Submodule.smul_mem I (q a) (h_G' h₂)
    rw[h_p_eq_sum_r] at h_p_mem
    have h₂: r ∈ I := by
      exact (Submodule.add_mem_iff_right I h₁).mp h_p_mem
    have h₄: m.leadingTerm r ∈ Ideal.span (m.leadingTerm '' ↑G') := by
      rw[←h_span]
      apply Ideal.subset_span
      apply Set.mem_image_of_mem
      exact h₂
    exact h₃ h₄

theorem groebner_basis_isRemainder_zero_iff_mem_span' {p : MvPolynomial σ k}
  {G' : Finset (MvPolynomial σ k)} {I : Ideal (MvPolynomial σ k)}
  {r : MvPolynomial σ k}
  (h : m.IsGroebnerBasis G' I)
  (hr : m.IsRemainder p G' r)
  : r = 0 ↔ p ∈ I := by
  classical
  rw [← m.IsGroebnerBasis_erase_zero] at h
  rw[← Finset.sdiff_singleton_eq_erase] at h
  rw [← isRemainder_sdiff_singleton_zero_iff_isRemainder] at hr
  apply groebner_basis_isRemainder_zero_iff_mem_span (G':= G'\{0})
  · intro g hg
    simp
    rw [Finset.mem_sdiff] at hg
    rcases hg with ⟨hg, h0⟩
    exact List.ne_of_not_mem_cons h0
  · exact h
  · simp
    exact hr

theorem groebner_basis_zero_isRemainder_iff_mem_span {p : MvPolynomial σ R}
  {G' : Finset (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)}
  (hG' : ∀ g ∈ G', IsUnit (m.leadingCoeff g))
  (h : m.IsGroebnerBasis G' I)
  : m.IsRemainder p G' 0 ↔ p ∈ I := by
  constructor
  · intro hr
    apply (groebner_basis_isRemainder_zero_iff_mem_span hG' h hr).mp rfl
  · intro hp
    have hor: ∀ g ∈ G', IsUnit (m.leadingCoeff g) ∨ g = 0 := by
      exact fun g a ↦ Or.symm (Or.inr (hG' g a))
    have h₁:  ∃ (r : MvPolynomial σ R), m.IsRemainder p G' r := by
      exact div_set' m hor p
    obtain ⟨r, hr⟩ := h₁
    have h₂: r = 0 := by
      exact (groebner_basis_isRemainder_zero_iff_mem_span hG' h hr).mpr hp
    rw [h₂] at hr
    exact hr

lemma groebner_basis_zero_isRemainder_iff_mem_span' {p : MvPolynomial σ k}
  {G' : Finset (MvPolynomial σ k)} {I : Ideal (MvPolynomial σ k)}
  (h : m.IsGroebnerBasis G' I) :
  p ∈ I ↔ m.IsRemainder p G' 0 := by
  classical
  have h_unit: ∀ g ∈ ↑(G'\{0}), IsUnit (m.leadingCoeff g) := by
      intro g hg
      rw [Finset.mem_sdiff] at hg
      rcases hg with ⟨hg, h0⟩
      simp
      exact List.ne_of_not_mem_cons h0
  constructor
  · intro hp
    rw [← m.IsGroebnerBasis_erase_zero] at h
    rw[← Finset.sdiff_singleton_eq_erase] at h
    have h_remainder: m.IsRemainder p ↑(G'\{0}) 0 := by
      apply (groebner_basis_zero_isRemainder_iff_mem_span h_unit h).mpr hp
    refine (isRemainder_sdiff_singleton_zero_iff_isRemainder m p (↑G') 0).mp ?_
    push_cast at h_remainder
    exact h_remainder
  · intro hr
    rw [← m.IsGroebnerBasis_erase_zero] at h
    rw[← Finset.sdiff_singleton_eq_erase] at h
    have h_remainder: m.IsRemainder p ↑(G'\{0}) 0 := by
      refine (isRemainder_of_insert_zero_iff_isRemainder m p (↑(G' \ {0})) 0).mp ?_
      push_cast
      simp
      exact (isRemainder_of_insert_zero_iff_isRemainder m p (↑G') 0).mpr hr
    apply (groebner_basis_zero_isRemainder_iff_mem_span h_unit h).mp
    exact h_remainder

lemma remainder_zero (p : MvPolynomial σ k) (hp : p ≠ 0) (B : Set (MvPolynomial σ k))
  (h : m.IsRemainder p B 0) : ∃ b ∈ B, b ≠ 0 ∧ m.degree b ≤ m.degree p := by
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
    obtain ⟨hgbne0, hbne0⟩ : g b ≠ 0 ∧ b ≠ 0 := by
      refine mul_ne_zero_iff.mp ?_
      contrapose! hb₂
      simp [hb₂]
    apply le_degree (m:=m) at hb₂
    rw [mul_comm b] at this
    apply le_antisymm this at hb₂
    simp at hb₂
    rw [degree_mul hgbne0 hbne0] at hb₂
    exact ⟨hbne0, le_of_add_le_right (le_of_eq hb₂)⟩

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
Let $G = \{g_1, \ldots, g_t\}$ be a finite subset of $k[x_1, \ldots, x_n]$. Then $G$ is a Gröbner basis for the ideal $I = \langle G \rangle$ if and only if  for every $f \in I$, the remainder of $f$ on division by $G$ is zero.
-/
theorem isGroebnerBasis_iff :
  m.IsGroebnerBasis G' I ↔ G'.toSet ⊆ I ∧ ∀ p ∈ I, m.IsRemainder p G' 0 := by
  -- uses groebner_basis_zero_isRemainder_iff_mem_span'
  have _uses := @groebner_basis_zero_isRemainder_iff_mem_span'.{0,0,0}
  classical
  constructor
  · intro h
    constructor
    · unfold MonomialOrder.IsGroebnerBasis at h
      rcases h with ⟨h_G', h_span⟩
      exact h_G'
    · intro p h_p_in_I
      rw[←groebner_basis_zero_isRemainder_iff_mem_span']
      norm_cast
      exact h
  · intro h
    rcases h with ⟨h_G', h_remainder⟩
    constructor
    · exact h_G'
    · have hG' : I = Ideal.span G' := by
        rw [←SetLike.coe_set_eq]
        norm_cast
        apply le_antisymm
        · intro p hp
          specialize h_remainder p hp
          have: ↑(Ideal.span G') ≤ ↑(I):= by
            apply Ideal.span_le.mpr
            intro p hp'
            rw [SetLike.mem_coe]
            exact h_G' hp'
          have h1: ↑(G': Set (MvPolynomial σ k)) ⊆ ↑(Ideal.span ↑G': Ideal (MvPolynomial σ k)) := by
            exact Ideal.subset_span
          apply (remainder_mem_ideal_iff h1 h_remainder).mp
          simp
        · exact Ideal.span_le.mpr h_G'
      rw [hG', ←SetLike.coe_set_eq]
      apply Set.eq_of_subset_of_subset
      · have h₁: Ideal.span (m.leadingTerm '' Ideal.span (α := MvPolynomial σ k) G')
          ≤ Ideal.span (α := MvPolynomial σ k) (m.leadingTerm '' G') := by
          apply Ideal.span_le.mpr
          intro p' hp
          rcases hp with ⟨p, hp', hp'₁⟩
          rw [←hp'₁, leadingTerm]

          have hG' : I = Ideal.span G' := by
            rw [←SetLike.coe_set_eq]
            norm_cast
          rw [←hG'] at hp'
          have hr: m.IsRemainder p (↑G') 0 := by
            exact h_remainder p hp'

          rw [SetLike.mem_coe]

          rw [leadingTerm_ideal_span_monomial', ← Set.image_image (monomial · 1) _ _, mem_ideal_span_monomial_image]
          intro j hj
          simp [MonomialOrder.leadingCoeff_eq_zero_iff] at hj
          simp [MonomialOrder.leadingCoeff_eq_zero_iff]
          obtain ⟨b, hbB, hb, hp⟩ := hj.1.symm ▸ m.remainder_zero p hj.2 G' hr
          rw [Finset.mem_coe] at hbB
          use b

        exact h₁
      · rw[←hG']
        apply Ideal.span_mono
        exact Set.image_mono h_G'



-- theorem isGroebnerBasis_iff' :
--   m.IsGroebnerBasis G' I ↔
--   G'.toSet ⊆ I ∧ ∀ p ∈ I, ∀ r, m.IsRemainder p G' r → r = 0 := by
--   sorry

/--
Let $G = \{g_1, \ldots, g_t\}$ be a Gröbner basis for an ideal $I \subseteq k[x_1, \ldots, x_n]$. Then $G$ is a basis for the vector space $I$ over $k$.
-/
theorem span_groebner_basis (h : m.IsGroebnerBasis G' I) : I = Ideal.span G' := by
  apply le_antisymm
  · intro p hp
    have h_remainder: m.IsRemainder p G' 0 := by
      exact (groebner_basis_zero_isRemainder_iff_mem_span' h).mp hp
    obtain ⟨⟨f, h_eq, h_deg⟩, h_remain⟩ := h_remainder
    rw[h_eq]
    simp
    rw [Finsupp.linearCombination_apply]
    apply Ideal.sum_mem
    intro g hg
    rcases g with ⟨g, gG'⟩
    simp
    have : g ∈ Ideal.span G':= by
      apply Ideal.subset_span
      exact gG'
    apply Ideal.mul_mem_left
    exact this

  · intro p hp
    have hG' : G'.toSet ⊆ I := by
      exact h.1
    have hI : Ideal.span ↑G' ≤ I := by
      apply Ideal.span_le.mpr
      intro p hp'
      rw [SetLike.mem_coe]
      exact hG' hp'
    exact hI hp

/--
Let $f, h_1, \dots, h_m \in k[\mathbf{x}] \setminus \{0\}$, and suppose $$f = c_1 h_1 + \cdots + c_m h_m, \quad \text{with } c_i \in k.$$ If $$\mathrm{lm}(h_1) = \mathrm{lm}(h_2) = \cdots = \mathrm{lm}(h_i) > \mathrm{lm}(f),$$ then $$f = \sum_{1 \leq i < j \leq m} c_{i,j} S(h_i, h_j), \quad c_{i,j} \in k.$$ Furthermore, if $S(h_i, h_j) \ne 0$, then $\mathrm{lm}(h_i) > \mathrm{lm}(S(h_i, h_j))$.
-/
lemma sPolynomial_decomposition (f: MvPolynomial σ k) (d: σ →₀ ℕ)
    (B: Finset (MvPolynomial σ k)) (c: MvPolynomial σ k → k) (hd: ∀ b ∈ B, (m.degree b) = d) (hfd: m.degree f ≺[m] d) (hf : f = ∑ b ∈  B, c b • b):
    ∃ (c': MvPolynomial σ k → MvPolynomial σ k → k), f = ∑ b₁ ∈  B, ∑ b₂ ∈  B, (c' b₁ b₂) • m.sPolynomial b₁ b₂ := by
  sorry

lemma degree_sub_sPolynomial (f : MvPolynomial σ R) : (m.degree (f - m.leadingTerm f) ≺[m] m.degree f) ∨ f - m.leadingTerm f = 0 :=
  sorry

@[simp]
theorem degree_eq_zero_iff{f : MvPolynomial σ R} :
    m.degree f = 0 ↔ f = C (m.leadingCoeff f) := by
    constructor
    · intro h
      sorry
    · intro h
      rw [h]
      simp [leadingCoeff]

lemma sPolynomial_ne_zero (f g : MvPolynomial σ R) (h : m.sPolynomial f g ≠ 0) :
    (0 < (m.toSyn <| m.degree f)) ∨  (0 < (m.toSyn <| m.degree g)) := by
    simp [MonomialOrder.sPolynomial] at h
    by_contra h_neg
    push_neg at h_neg
    rcases h_neg with ⟨h₁, h₂⟩
    have h2: m.toSyn (m.degree f) ≥  0 := by
      exact zero_le m (m.toSyn (m.degree f))
    have h0: m.toSyn (m.degree f) = 0 := by
      exact le_antisymm h₁ h2
    have h0': m.degree f = 0 := by
      exact (AddEquiv.map_eq_zero_iff m.toSyn).mp h0
    have h3:  m.toSyn (m.degree g) ≥  0 := by
      exact zero_le m (m.toSyn (m.degree g))
    have h4: m.toSyn (m.degree g) = 0 := by
      exact le_antisymm h₂ h3
    have h4': m.degree g = 0 := by
      exact (AddEquiv.map_eq_zero_iff m.toSyn).mp h4
    simp [h0', h4'] at h
    have h5: f = C (m.leadingCoeff f) := by
      exact degree_eq_zero_iff.mp h0'
    have h5': g = C (m.leadingCoeff g) := by
      exact degree_eq_zero_iff.mp h4'
    have: C (m.leadingCoeff g) * f - C (m.leadingCoeff f) * g = 0 := by
      simp [←h5, ←h5']
      ring
    ring_nf

/--
$h_1, h_2 \in k[\mathbf{x}], lm(h_1) = lm(h_2), S(h_1, h_2) \ne 0$, then $lm(S(h_1, h_2)) < lm(h_1)$.
-/
lemma sPolynomial_degree_lt (h₁ h₂: MvPolynomial σ k) (h: m.degree h₁ = m.degree h₂) (hs: m.sPolynomial h₁ h₂ ≠ 0) : m.degree (m.sPolynomial h₁ h₂) ≺[m] m.degree h₁ := by
  classical
  unfold MonomialOrder.sPolynomial
  simp [h]
  apply sPolynomial_ne_zero at hs
  simp [h] at hs

  have h2: (m.degree (h₂ - m.leadingTerm h₂)) ≺[m]  m.degree (h₂) := by
    refine (or_iff_left_iff_imp.mpr ?_).mp <| m.degree_sub_sPolynomial _
    simp_intro' hLT [hs]

  have h4: (m.degree (h₁ - m.leadingTerm h₁)) ≺[m]  m.degree (h₂) := by
    refine (or_iff_left_iff_imp.mpr ?_).mp <| h ▸ m.degree_sub_sPolynomial _
    simp_intro' hLT [hs]

  calc
    _ = m.toSyn (m.degree <|
        m.leadingCoeff h₁ • (h₂ - m.leadingTerm h₂) -
        m.leadingCoeff h₂ • (h₁ - m.leadingTerm h₁)) := by
      rw [←degree_neg]
      congr
      simp [leadingTerm, mul_sub_left_distrib, MvPolynomial.smul_eq_C_mul,
        C_mul_monomial, h, mul_comm (m.leadingCoeff h₂)]
    _ ≤ m.toSyn (m.degree _) ⊔ m.toSyn (m.degree _) := degree_sub_le
    _ < m.toSyn (m.degree h₂) := by
      simp
      constructor
      · exact lt_of_le_of_lt degree_smul_le h2
      · exact lt_of_le_of_lt degree_smul_le h4


/--
A basis $G = \{ g_1, \ldots, g_t \}$ for an ideal $I$ is a Gröbner basis if and only if $S(g_i, g_j) \to_G 0$ for all $i \neq j$.
-/
theorem buchberger_criterion {g₁ g₂ : MvPolynomial σ k}
  (hG: ∀ (g₁ g₂: G'), m.IsRemainder (m.sPolynomial g₁ g₂ : MvPolynomial σ k) G' 0) :
  m.IsGroebnerBasis G' (Ideal.span G') := by
  have _uses := @groebner_basis_isRemainder_zero_iff_mem_span.{0,0,0}
  have _uses := @isGroebnerBasis_iff.{0,0,0}
  have _uses := @sPolynomial_decomposition.{0,0,0}
  have _uses := @sPolynomial_degree_lt.{0,0,0}
  sorry
