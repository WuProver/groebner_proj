-- import Mathlib -- TODO: should be removed later
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.Data.Set.Finite.Basic
import Groebner.Defs
-- import Groebner.MonomialOrder
import Mathlib.Tactic.RewriteSearch
-- import Mathlib.Data.Set.Basic
import Groebner.Submodule

namespace Ideal

variable {R : Type*} [Semiring R]

-- lemma mem_span_iff (A : Set R) (p : R) :
-- p ∈ Ideal.span A ↔ ∃ (s : Finset A)(f : R → R), p = ∑ m in s, f m * m
-- :=by
--   sorry
-- lemma mem_span_iff' (A : Set R) (p : R) :
-- p ∈ Ideal.span A ↔ ∃ (s : Finset A)(f : A → R), p = ∑ m in s, f m * m
-- := by
--   sorry
-- lemma mem_span_iff'' (A : Set R) (p : R) :
-- p ∈ Ideal.span A ↔
-- ∃ (s : Finset R) (f : R → R), s.toSet ⊆ A ∧ p = ∑ m in s, f m * m
-- := by
--   sorry

/--
A subset $s \subseteq R$ has finitely generated span if and only if:
$\exists$ finite $s' \subseteq s$ such that $\mathsf{span}(s) = \mathsf{span}(s')$
-/
lemma fg_span_iff_fg_span_finset_subset (s : Set R) :
  (span s).FG ↔ ∃ (s' : Finset R), s'.toSet ⊆ s ∧ span s = span s' :=
  Submodule.fg_span_iff_fg_span_finset_subset R s
-- to Mathlib

/--
For any ring $R$, the span of the zero singleton set equals the zero submodule:
  $$
    \mathsf{span}_R \{(0 : R)\} = \bot
  $$
-/
-- submitted: https://github.com/leanprover-community/mathlib4/pull/24448
@[simp]
lemma span_singleton_zero : span {(0 : R)} = ⊥ :=
  Submodule.span_zero_singleton _

/--
For any subset $s \subseteq R$ of a ring $R$, inserting zero does not change the linear span:
  $$
    \mathsf{span}_R(\{0\} \cup s) = \mathsf{span}_R(s)
  $$
-/
-- submitted: https://github.com/leanprover-community/mathlib4/pull/24448
@[simp]
lemma span_insert_zero (s : Set R): span (insert 0 s) = span s :=
  Submodule.span_insert_zero

-- merged: https://github.com/leanprover-community/mathlib4/pull/24360
/--
For any subset $s \subseteq R$ of a ring $R$, removing zero does not change the linear span:
  $$
    \mathsf{span}_R(s \setminus \{0\}) = \mathsf{span}_R(s)
  $$
-/
@[simp]
lemma span_sdiff_singleton_zero (s : Set R): span (s \ {0}) = span s := Submodule.span_sdiff_singleton_zero

end Ideal

namespace MonomialOrder
open Ideal
open MvPolynomial
open Classical

variable {σ : Type*} {m : MonomialOrder σ} {s : σ →₀ ℕ}
variable {k : Type*} [Field k] variable (p p₁ p₂ : MvPolynomial σ k)
variable (B' G: Finset (MvPolynomial σ k)) (B: Set (MvPolynomial σ k))
variable (I : Ideal (MvPolynomial σ k))
variable {R : Type*} [CommSemiring R]

open Finsupp
open Finset
open Submodule
open Ideal
open Field

lemma leadingTerm_ideal_sdiff_singleton_zero (B: Set (MvPolynomial σ R)) :
  span (m.leadingTerm '' (B \ {0})) = span (m.leadingTerm '' B) :=
  m.leadingTerm_image_sdiff_singleton_zero B ▸ Ideal.span_sdiff_singleton_zero _

lemma leadingTerm_ideal_insert_zero (B: Set (MvPolynomial σ R)) :
  span (m.leadingTerm '' (insert 0 B)) = span (m.leadingTerm '' B) := by
  by_cases h : 0 ∈ B
  · rw [Set.insert_eq_of_mem h]
  · simp [leadingTerm_image_insert_zero]

lemma isGroebnerBasis_erase_zero (G : Finset (MvPolynomial σ R)) (I : Ideal (MvPolynomial σ R)) :
  m.IsGroebnerBasis (G.erase 0) I ↔ m.IsGroebnerBasis G I := by
  simp [IsGroebnerBasis, m.leadingTerm_ideal_sdiff_singleton_zero]

lemma isGroebnerBasis_union_singleton_zero (G : Finset (MvPolynomial σ R)) (I : Ideal (MvPolynomial σ R)) :
  m.IsGroebnerBasis (G ∪ {0}) I ↔ m.IsGroebnerBasis G I := by
  unfold IsGroebnerBasis
  congr! 1
  · constructor
    · intro h x hx
      apply h
      refine mem_coe.mpr ?_
      exact mem_union_left {0} hx
    · intro hGI
      push_cast
      rw [Set.union_subset_iff]
      constructor
      · exact hGI
      · exact Set.singleton_subset_iff.mpr (Submodule.zero_mem _)
  · simp [IsGroebnerBasis, m.leadingTerm_ideal_insert_zero]
/--
Let $G'' \subseteq R[x_1, \dots, x_n]$ be a set of polynomials such that
$$
\forall p \in G'',\ \operatorname{leadingCoeff}(p) \in R^\times.
$$
Then,
$$
\left\langle \operatorname{lt}(G'') \right\rangle = \left\langle x^{\deg(p)} \mid p \in G'' \right\rangle,
$$
-/
lemma leadingTerm_ideal_span_monomial {B: Set (MvPolynomial σ R)}
    (hB : ∀ p ∈ B, IsUnit (m.leadingCoeff p)) :
    span (m.leadingTerm '' B) = span ((fun p ↦ MvPolynomial.monomial (m.degree p) (1 : R)) '' B) := by
  apply le_antisymm
  all_goals
    rintro p hl
    simp_rw [MonomialOrder.leadingTerm, ← submodule_span_eq, mem_span_image_iff_exists_fun] at *
    rcases hl with ⟨t, ht, c, hc⟩
    rw [←hc]
    use t
  · split_ands
    · exact ht
    · use fun p ↦ (MvPolynomial.C (m.leadingCoeff ↑p : R) : MvPolynomial σ R) • c ↑p
      apply Finset.sum_congr rfl
      simp
      intro a ha
      rw [mul_assoc, mul_left_comm, MvPolynomial.C_mul_monomial, mul_one]
  · split_ands
    · exact ht
    · use fun p ↦ if hp : ↑p ∈ B then ((hB (↑p) (hp)).unit)⁻¹ • c ↑p else 0
      apply Finset.sum_congr rfl
      · simp
        intro a ha
        simp [Set.mem_of_mem_of_subset ha ht]
        rw [smul_mul_assoc, ←mul_smul_comm, MvPolynomial.smul_monomial, IsUnit.inv_smul]

/--
$$
\langle \mathrm{lt}(G) \rangle = \left\langle \left\{ x^t : t \in \{ \mathrm{multideg}(p) : p \in G \setminus \{0\} \} \right\} \right\rangle
$$
-/
lemma leadingTerm_ideal_span_monomial₀ {B: Set (MvPolynomial σ R)}
    (hB : ∀ p ∈ B, IsUnit (m.leadingCoeff p) ∨ p = 0) :
    span (m.leadingTerm '' B) =
    span ((fun p ↦ MvPolynomial.monomial (m.degree p) 1) '' (B \ {0})) := by
  calc
    _ = span (m.leadingTerm '' B \ {0}) := (Ideal.span_sdiff_singleton_zero _).symm
    _ = span (m.leadingTerm '' (B \ {0})) := by rw [m.leadingTerm_image_sdiff_singleton_zero]
    _ = _ := by
      apply leadingTerm_ideal_span_monomial
      simp_intro .. [or_iff_not_imp_right.mp (hB _ _)]

lemma leadingTerm_ideal_span_monomial' {B: Set (MvPolynomial σ k)} :
      span (m.leadingTerm '' B) =
      span ((fun p ↦ MvPolynomial.monomial (m.degree p) 1) '' (B \ {0})) := by
  apply leadingTerm_ideal_span_monomial₀
  simp [em']

/--
Let $G'' \subseteq R[x_1, \dots, x_n]$, let $I \subseteq R[x_1, \dots, x_n]$ be an ideal,
and let $p, r \in R[x_1, \dots, x_n]$. Suppose that:

  - $G'' \subseteq I$,
  - $r \in I$,
  - $r$ is the remainder of $p$ upon division by $G''$.

Then,
$$
p \in I.
$$
-/
lemma mem_ideal_of_remainder_mem_ideal {B: Set (MvPolynomial σ R)} {r : MvPolynomial σ R}
    {I : Ideal (MvPolynomial σ R)} {p : MvPolynomial σ R}
    (hBI : B ⊆ I) (hpBr : m.IsRemainder p B r) (hr : r ∈ I) :
    p ∈ I := by
  obtain ⟨⟨f, h_eq, h_deg⟩, h_remain⟩ := hpBr
  rw[h_eq]
  refine Ideal.add_mem _ ?_ ?_
  · rw [Finsupp.linearCombination_apply]
    apply Ideal.sum_mem
    intro b hb
    exact mul_mem_left _ _ (Set.mem_of_mem_of_subset (by simp) hBI)
  · exact hr

/--
Let $R$ be a commutative ring, and let $G'' \subseteq R[x_1, \dots, x_n]$, $I \subseteq R[x_1, \dots, x_n]$ be an ideal, and $p, r \in R[x_1, \dots, x_n]$.
Assume that:

  - $G'' \subseteq I$,
  - $r$ is the remainder of $p$ upon division by $G''$.

Then,
$$
r \in I \quad \Longleftrightarrow \quad p \in I.
$$
-/
lemma remainder_mem_ideal_iff {R : Type*} [CommRing R] {B: Set (MvPolynomial σ R)}
    {r : MvPolynomial σ R} {I : Ideal (MvPolynomial σ R)} {p : MvPolynomial σ R}
    (hBI : B ⊆ I) (hpBr : m.IsRemainder p B r) :
    r ∈ I ↔ p ∈ I := by
  refine ⟨mem_ideal_of_remainder_mem_ideal hBI hpBr, ?_⟩
  obtain ⟨⟨f, h_eq, h_deg⟩, h_remain⟩ := hpBr
  intro hp
  rw [← sub_eq_of_eq_add' h_eq]
  apply Ideal.sub_mem I hp
  -- (optional) to make it clearer: `rw [Finsupp.linearCombination_apply]`
  apply Ideal.sum_mem
  intro b hb
  exact mul_mem_left I _ (Set.mem_of_mem_of_subset (by simp) hBI)

/--
Let $I \subseteq k[x_i : i \in \sigma]$ be an ideal, and let $G \subseteq I$ be a finite subset.
Suppose that $r_1$ and $r_2$ are generalized remainders of a polynomial $p$ upon division by $G$.
Then,
$$
r_1 - r_2 \in I.
$$
-/
lemma remainder_sub_remainder_mem_ideal {R : Type*} [CommRing R]
    {B: Set (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)} {p r₁ r₂ : MvPolynomial σ R}
    (hBI : B ⊆ I) (hr₁ : m.IsRemainder p B r₁) (hr₂ : m.IsRemainder p B r₂) :
    r₁ - r₂ ∈ I := by
  obtain ⟨⟨f₁, h_eq₁, h_deg₁⟩, h_remain₁⟩ := hr₁
  obtain ⟨⟨f₂, h_eq₂, h_deg₂⟩, h_remain₂⟩ := hr₂
  rw [← sub_eq_of_eq_add' h_eq₁, ← sub_eq_of_eq_add' h_eq₂]
  simp
  apply Ideal.sub_mem I
  all_goals
    apply Ideal.sum_mem
    intro g hg
    exact mul_mem_left I _ (Set.mem_of_mem_of_subset (by simp) hBI)

-- lemma monomial_not_mem_leading_term_ideal{r : MvPolynomial σ k}
--   {G' : Set (MvPolynomial σ k)}
--   (h : ∀ g ∈ G', g ≠ 0 → ∀ s ∈ r.support, ¬ m.degree g ≤ s) :
--   ∀ s ∈ r.support, monomial s (1 : k) ∉ leading_term_ideal m G' := by
--   sorry

-- lemma term_not_mem_leading_term_ideal {r : MvPolynomial σ k}
-- {G' : Set (MvPolynomial σ k)}
-- (h : ∀ g ∈ G', g ≠ 0 → ∀ s ∈ r.support, ¬ m.degree g ≤ s)
-- : ∀ s ∈ r.support, monomial s (r.coeff s) ∉ leading_term_ideal m  G' := by
--   sorry

-- lemma not_mem_leading_term_ideal {r : MvPolynomial σ k}
-- {G' : Set (MvPolynomial σ k)}
-- (h : ∀ g ∈ G', g ≠ 0 → ∀ s ∈ r.support, ¬ m.degree g ≤ s)
-- (hr : r ≠ 0) :
-- r ∉ leading_term_ideal m G' := by
--  sorry

lemma isRemainder_term_not_mem_leading_term_ideal {p r : MvPolynomial σ R}
    {B : Set (MvPolynomial σ R)}
    (hB : ∀ p ∈ B, IsUnit (m.leadingCoeff p))
    (h : m.IsRemainder p B r) :
    ∀ s ∈ r.support, monomial s (r.coeff s) ∉ Ideal.span (m.leadingTerm '' B) := by
  intro s hs
  rw [leadingTerm_ideal_span_monomial hB, ← Set.image_image (monomial · 1) _ _, mem_ideal_span_monomial_image]
  have h1ne0: (1 : R) ≠ 0 := by
    by_contra h1eq0
    rw [MvPolynomial.mem_support_iff, ← mul_one <| r.coeff s, h1eq0, mul_zero] at hs
    exact hs rfl
  simp [MvPolynomial.mem_support_iff.mp hs]
  intro b hb
  unfold MonomialOrder.IsRemainder at h
  apply h.2 s hs b hb
  by_contra hq0
  specialize hB b hb
  simp [hq0, h1ne0.symm] at hB

lemma isRemainder_term_not_mem_leading_term_ideal₀ {p r : MvPolynomial σ R}
    {B : Set (MvPolynomial σ R)}
    (hB : ∀ p ∈ B, IsUnit (m.leadingCoeff p) ∨ p = 0)
    (h : m.IsRemainder p B r) :
    ∀ s ∈ r.support, monomial s (r.coeff s) ∉ Ideal.span (m.leadingTerm '' B) := by
  rw [← leadingTerm_ideal_sdiff_singleton_zero]
  rw [← m.isRemainder_sdiff_singleton_zero_iff_isRemainder] at h
  refine isRemainder_term_not_mem_leading_term_ideal ?_ h
  simp_intro .. [or_iff_not_imp_right.mp (hB _ _)]

lemma isRemainder_term_not_mem_leading_term_ideal' {p r : MvPolynomial σ k}
  {B : Set (MvPolynomial σ k)} (h : m.IsRemainder p B r):
∀ s ∈ r.support, monomial s (r.coeff s) ∉ Ideal.span (m.leadingTerm '' B) := by
  rw [←Ideal.span_sdiff_singleton_zero, ← m.leadingTerm_image_sdiff_singleton_zero]
  apply isRemainder_term_not_mem_leading_term_ideal
  simp
  rwa [←isRemainder_sdiff_singleton_zero_iff_isRemainder] at h

lemma monomial_not_mem_leading_term_ideal {r : MvPolynomial σ R}
    {B : Set (MvPolynomial σ R)}
    (hB : ∀ p ∈ B, IsUnit (m.leadingCoeff p))
    (h : ∀ c ∈ r.support, ∀ b ∈ B, ¬ (m.degree b ≤ c)) :
    ∀ s ∈ r.support, monomial s 1 ∉ Ideal.span (m.leadingTerm '' B) := by
  intro s hs
  rw [leadingTerm_ideal_span_monomial hB,
      ← Set.image_image (monomial · 1) _ _, mem_ideal_span_monomial_image]
  simp
  split_ands
  · by_contra h1eq0
    rw [MvPolynomial.mem_support_iff, ← mul_one <| r.coeff s, h1eq0, mul_zero] at hs
    exact hs rfl
  · intro b hb
    exact h s hs b hb

lemma isRemainder_monomial_not_mem_leading_term_ideal {p r : MvPolynomial σ R}
    {B : Set (MvPolynomial σ R)}
    (hB : ∀ p ∈ B, IsUnit (m.leadingCoeff p))
    (h : m.IsRemainder p B r) :
    ∀ s ∈ r.support, monomial s 1 ∉ Ideal.span (m.leadingTerm '' B) := by
  apply monomial_not_mem_leading_term_ideal hB
  intro c hc b hb
  have : Nontrivial R := by
    rw [nontrivial_iff_exists_ne 0]
    use 1
    by_contra h1eq0
    rw [MvPolynomial.mem_support_iff, ← mul_one <| r.coeff c, h1eq0, mul_zero] at hc
    exact hc rfl
  refine h.2 c hc b hb (m.leadingCoeff_ne_zero_iff.mp (hB _ hb).ne_zero)

lemma isRemainder_monomial_not_mem_leading_term_ideal₀ {p r : MvPolynomial σ R}
    {B : Set (MvPolynomial σ R)}
    (hB : ∀ p ∈ B, IsUnit (m.leadingCoeff p) ∨ p = 0)
    (h : m.IsRemainder p B r) :
    ∀ s ∈ r.support, monomial s 1 ∉ Ideal.span (m.leadingTerm '' B) := by
  rw [← leadingTerm_ideal_sdiff_singleton_zero]
  rw [← m.isRemainder_sdiff_singleton_zero_iff_isRemainder] at h
  refine m.isRemainder_monomial_not_mem_leading_term_ideal ?_ h
  simp_intro .. [or_iff_not_imp_right.mp (hB _ _)]

lemma isRemainder_monomial_not_mem_leading_term_ideal' {p r : MvPolynomial σ k}
  {B : Set (MvPolynomial σ k)} (h : m.IsRemainder p B r):
∀ s ∈ r.support, monomial s 1 ∉ Ideal.span (m.leadingTerm '' B) := by
  rw [←Ideal.span_sdiff_singleton_zero, ← m.leadingTerm_image_sdiff_singleton_zero]
  apply isRemainder_monomial_not_mem_leading_term_ideal
  simp
  rwa [←isRemainder_sdiff_singleton_zero_iff_isRemainder] at h

lemma sPolynomial_mem_ideal {R : Type*} [CommRing R]
    {I : Ideal <| MvPolynomial σ R} {p q : MvPolynomial σ R}
    (hp : p ∈ I) (hq : q ∈ I) : m.sPolynomial p q ∈ I :=
  sub_mem (mul_mem_left I _ hp) (mul_mem_left I _ hq)


-- lemma rem_monomial_not_mem_leading_term_ideal {p r : MvPolynomial σ k}
-- {G' : Finset (MvPolynomial σ k)} (h : IsRemainder p G' r):
-- ∀ s ∈ r.support, monomial s 1 ∉ leading_term_ideal G'.toSet := by
--   sorry

-- lemma rem_term_not_mem_leading_term_ideal {p r : MvPolynomial σ k}
-- {G' : Finset (MvPolynomial σ k)} (h : is_rem p G' r):
-- ∀ s ∈ r.support, monomial s (r.coeff s) ∉ leading_term_ideal G' := by

-- lemma rem_not_mem_leading_term_ideal {p r : MvPolynomial σ k}
-- {G' : Finset (MvPolynomial σ k)} (h : is_rem p G' r) (hr :r ≠ 0):
-- r ∉ leading_term_ideal G' := by

lemma isRemainder_sub_isRemainder_monomial_not_mem_leading_term_ideal
    {R : Type*} [CommRing R]
    {B : Set (MvPolynomial σ R)} {p r₁ r₂ : MvPolynomial σ R}
    (hB : ∀ p ∈ B, IsUnit (m.leadingCoeff p))
    (hr₁ : m.IsRemainder p B r₁) (hr₂ :  m.IsRemainder p B r₂) :
    ∀ s ∈ (r₁ - r₂).support, monomial s 1 ∉ Ideal.span (m.leadingTerm '' B) := by
  apply m.monomial_not_mem_leading_term_ideal hB
  intro c hc
  apply MvPolynomial.support_sub at hc
  rw [mem_union] at hc
  have {b} (hb : b ∈ B) : b ≠ 0 := by
    have : Nontrivial R := by
      by_contra h
      rw [not_nontrivial_iff_subsingleton] at h
      simp [Subsingleton.elim _ (0 : MvPolynomial σ R)] at hc
    rw [← m.leadingCoeff_ne_zero_iff]
    exact (hB b hb).ne_zero
  rcases hc with hc | hc
  · intro b hb
    exact hr₁.2 c hc b hb <| this hb
  · intro b hb
    exact hr₂.2 c hc b hb <| this hb

end MonomialOrder
