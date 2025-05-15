import Mathlib
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.RingTheory.Ideal.Span
import Groebner.SimpIntro

namespace MonomialOrder

open MvPolynomial
variable {σ : Type*} (m : MonomialOrder σ)

section CommSemiring
variable {R : Type*} [CommSemiring R]
variable (f p: MvPolynomial σ R) (B: Set (MvPolynomial σ R)) (r : MvPolynomial σ R)

/--
0 is less then any `σ →₀ ℕ` w.r.t. monomial order.
-/
@[simp]
lemma zero_le (a : m.syn) : 0 ≤ a := bot_le

-- #check Polynomial.degree_add_eq_left_of_degree_lt

-- lemma degree_add_eq_left_of_degree_lt
--   (h : m.degree p ≺[m] m.degree f) : m.degree (f + p) = m.degree f := by
--   exact degree_add_of_lt h

lemma degree_add_eq_right_of_degree_lt
  (h : m.degree f ≺[m] m.degree p) : m.degree (f + p) = m.degree p := by
  rw [add_comm]
  exact degree_add_of_lt h

lemma degree_sum_le {α : Type*} {s : Finset α} {f : α → MvPolynomial σ R} :
    (m.toSyn <| m.degree <| ∑ x ∈ s, f x) ≤ s.sup fun x => (m.toSyn <| m.degree <| f x) := by
  classical
  induction' s using Finset.induction_on with a A haA h
  · simp
  · simp
    by_contra h_neg
    push_neg at h_neg
    rcases h_neg with ⟨h1, h2⟩
    rw [Finset.sum_insert] at h2
    rw [Finset.sum_insert] at h1
    · have h3: m.toSyn (m.degree (f a + ∑ x ∈ A, f x)) ≤  m.toSyn (m.degree (f a)) ⊔ m.toSyn (m.degree (∑ x ∈ A, f x)) := by
        exact degree_add_le
      have h3': m.toSyn (m.degree (f a)) <  m.toSyn (m.degree (f a)) ⊔ m.toSyn (m.degree (∑ x ∈ A, f x)) := by
        exact gt_of_ge_of_gt h3 h1
      simp [lt_sup_iff] at h3'
      have h4: m.toSyn (m.degree (f a)) ⊔ m.toSyn (m.degree (∑ x ∈ A, f x)) ≤  m.toSyn (m.degree (∑ x ∈ A, f x)):=by
        simp [le_sup_iff]
        apply le_of_lt h3'
      have : m.toSyn (m.degree (f a + ∑ x ∈ A, f x)) ≤  m.toSyn (m.degree (∑ x ∈ A, f x)) := by
        exact
            Preorder.le_trans (m.toSyn (m.degree (f a + ∑ x ∈ A, f x)))
              (max (m.toSyn (m.degree (f a))) (m.toSyn (m.degree (∑ x ∈ A, f x))))
              (m.toSyn (m.degree (∑ x ∈ A, f x))) h3 h4
      have h5: (A.sup fun x ↦ m.toSyn (m.degree (f x))) < m.toSyn (m.degree (∑ x ∈ A, f x)) := by
        exact gt_of_ge_of_gt this h2
      have :  m.toSyn (m.degree (∑ x ∈ A, f x)) <  m.toSyn (m.degree (∑ x ∈ A, f x)):= by
        exact lt_of_le_of_lt h h5
      exact (lt_self_iff_false (m.toSyn (m.degree (∑ x ∈ A, f x)))).mp this
    · exact haA
    · exact haA

variable {m} in
lemma ne_zero_of_degree_ne_zero {f : MvPolynomial σ R} (h : m.degree f ≠ 0) : f ≠ 0 := by
  by_contra h'
  have: m.degree f = 0 := by
    simp [h']
  exact h this

lemma degree_mem_support_iff (f : MvPolynomial σ R) : m.degree f ∈ f.support ↔ f ≠ 0 :=
  mem_support_iff.trans coeff_degree_ne_zero_iff

/--
The leading term in a non-zero multivariate polynomial is the term of the polynomial's degree in
the polynomial. The leading term in the zero polynomial is defined as the zero polynomial.
-/
noncomputable def leadingTerm (f : MvPolynomial σ R) : MvPolynomial σ R :=
  monomial (m.degree f) (m.leadingCoeff f)

/--
Given a multivariate polynomial $p$ and a set $B$ of multivariate polynomials over a commutative
semiring $R$, and a monomial order. If there exists a $g : B \to R[X]$ with finite support, and a
multivriate polynomial $r$, such that

1. $p = \sum_{b\in B} g(b)b + r,$
2. degree of any non-zero $g(b)b$ where b\in B is less than or equal to the degree of $p$,
3. none of terms of $r$ is divisible by leading monomial of a non-zero elements of $B$,

then $r$ is called a **remainder** of $p$ on division by "divisors" $B$.

A statement that `r` is a remainder of `p` on division by `B` w.r.t. a monomial order `m` is
denoted as `m.IsRemainder p B r`.
-/
def IsRemainder :=
  (∃ (g : B →₀ MvPolynomial σ R),
    p = Finsupp.linearCombination _ (fun (b : B) ↦ (b : MvPolynomial σ R)) g + r ∧
    ∀ (b : B), m.degree ((b : MvPolynomial σ R) * (g b)) ≼[m] m.degree p) ∧
  ∀ c ∈ r.support, ∀ b ∈ B, b ≠ 0 → ¬ (m.degree b ≤ c)

open Classical

-- it may free you from coercion between different kinds of "sets",
-- "finite subsets", "finite subsets" of "sets", ...,
-- when you are dealing with different G''
/--
A variant of `IsRemainder` without coercion of a `Set (MvPolynomial σ R)`.
-/
lemma isRemainder_def' (p : MvPolynomial σ R) (B : Set (MvPolynomial σ R)) (r : MvPolynomial σ R)
  : m.IsRemainder p B r ↔ (∃ (g : MvPolynomial σ R →₀ MvPolynomial σ R),
      ↑g.support ⊆ B ∧
      p = Finsupp.linearCombination _ id g + r ∧
      ∀ b ∈ B, m.degree ((b : MvPolynomial σ R) * (g b)) ≼[m] m.degree p) ∧
      ∀ c ∈ r.support, ∀ g' ∈ B, g' ≠ 0 → ¬ (m.degree g' ≤ c) := by
  unfold IsRemainder
  constructor
  · intro ⟨⟨g, h₁, h₂⟩, h₃⟩
    split_ands
    · use {
        support := g.support,
        toFun := fun b => if hb : b ∈ B then g.toFun (⟨b, hb⟩) else 0,
        mem_support_toFun := by intro; simp; rfl
      }
      split_ands
      · simp
      · simp [h₁]
        congr 1
        simp [Finsupp.linearCombination_apply, Finsupp.sum]
        rfl
      · simp_intro' b hb
        convert h₂ ⟨b, hb⟩
    · exact h₃
  ·
    intro ⟨⟨g, hg, h₁, h₂⟩, h₃⟩
    split_ands
    ·
      use {
        support := (g.support.subtype (· ∈ B)),
        toFun := (g.toFun ·),
        mem_support_toFun := by intro; simp; rfl
      }
      split_ands
      · rw [h₁, eq_comm]
        congr 1
        simp [Finsupp.linearCombination_apply, Finsupp.sum]
        apply Finset.sum_nbij (↑·)
        · simp_intro' ..
        · simp_intro' b _ b₁ _ h [Subtype.eq_iff]
        · simp_intro' b hb
          exact Set.mem_of_subset_of_mem hg <| Finsupp.mem_support_iff.mpr hb
        · simp [DFunLike.coe]
      · simpa
    · exact h₃

/--
A variant of `IsRemainder` where `g : MvPolynomial σ R →₀ MvPolynomial σ R` is replaced with a
function `g : MvPolynomial σ R → MvPolynomial σ R` without limitation on its support.
-/
lemma isRemainder_def'' (p : MvPolynomial σ R) (B : Set (MvPolynomial σ R)) (r : MvPolynomial σ R)
  : m.IsRemainder p B r ↔
  (∃ (g : MvPolynomial σ R → MvPolynomial σ R) (B' : Finset (MvPolynomial σ R)),
      ↑B' ⊆ B ∧
      p = B'.sum (fun x => g x * x) + r ∧
      ∀ b' ∈ B', m.degree ((b' : MvPolynomial σ R) * (g b')) ≼[m] m.degree p) ∧
      ∀ c ∈ r.support, ∀ b ∈ B, b ≠ 0 → ¬ (m.degree b ≤ c) := by
  rw [isRemainder_def']
  constructor
  · intro ⟨⟨g, h₁, h₂, h₃⟩, h₄⟩
    refine ⟨?_, h₄⟩
    use g.toFun, g.support
    refine ⟨h₁, by rwa [Finsupp.linearCombination_apply, Finsupp.sum] at h₂, ?_⟩
    intro g' hg'
    exact h₃ g' (Set.mem_of_mem_of_subset hg' h₁)
  · intro ⟨⟨g, B', h₁, h₂, h₃⟩, h₄⟩
    split_ands
    · use Finsupp.onFinset B' (fun b' => if b' ∈ B' then g b' else 0) (by simp_intro' ..)
      split_ands
      · simp_intro' b' hb'
        exact Set.mem_of_mem_of_subset hb'.1 h₁
      · rw [Finsupp.linearCombination_apply, Finsupp.sum, h₂, Finsupp.support_onFinset]
        congr 1
        simp
        have h : B' = ({b' ∈ B' | b' ∈ B' ∧ ¬g b' = 0} ∩ B') ∪ ({b' ∈ B' | g b' = 0}) := by
          apply subset_antisymm
          · simp_intro' x hx [em']
          · simp_intro' x
            rintro (⟨_, hx⟩ | ⟨hx,_⟩) <;> exact hx
        have h' : Disjoint ({b' ∈ B' | b' ∈ B' ∧ ¬g b' = 0} ∩ B')  ({b' ∈ B' | g b' = 0}) := by
          unfold Disjoint
          simp_intro' s hs hs'
          by_contra h
          obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr h
          have hs := Finset.mem_of_subset hs hx
          have hs' := Finset.mem_of_subset hs' hx
          simp at hs hs'
          exact hs.1.2 hs'.2
        nth_rewrite 1 [h]
        rw [Finset.sum_union h']
        convert add_zero _
        convert Finset.sum_const_zero
        expose_names
        simp at h_1
        simp [h_1.2]
      · intro b hb
        by_cases hbB' : b ∈ B'
        · simp [hbB', h₃]
        · simp [hbB']
    · exact h₄

lemma isRemainder_finset (p : MvPolynomial σ R) (B' : Finset (MvPolynomial σ R)) (r : MvPolynomial σ R)
  : m.IsRemainder p B' r ↔
  (∃ (g : MvPolynomial σ R → MvPolynomial σ R),
      p = B'.sum (fun x => g x * x) + r ∧
      ∀ b' ∈ B', m.degree ((b' : MvPolynomial σ R) * (g b')) ≼[m] m.degree p) ∧
      ∀ c ∈ r.support, ∀ b ∈ B', b ≠ 0 → ¬ (m.degree b ≤ c) := by
  constructor
  · sorry
  · simp [isRemainder_def'']
    sorry



lemma isRemainder_finset' (p : MvPolynomial σ R) (B' : Finset (MvPolynomial σ R)) (r : MvPolynomial σ R)
    : m.IsRemainder p B' r ↔
      (∃ (g : MvPolynomial σ R → MvPolynomial σ R),
        p = B'.sum (fun x => g x * x) + r ∧
        ∀ b' ∈ B', (m.degree ((b' : MvPolynomial σ R) * (g b')) ≼[m] m.degree p) ∧
        (p = 0 → g = 0)
        ) ∧
      ∀ c ∈ r.support, ∀ b ∈ B', b ≠ 0 → ¬ (m.degree b ≤ c) := by
      sorry

/--
Remainders are preserved on insertion of the zero polynomial into the set of divisors.
-/
lemma isRemainder_of_insert_zero_iff_isRemainder (p : MvPolynomial σ R)
  (B : Set (MvPolynomial σ R)) (r : MvPolynomial σ R) :
  m.IsRemainder p (insert 0 B) r ↔ m.IsRemainder p B r := by
  constructor
  · by_cases hB : 0 ∈ B; simp only [Set.insert_eq_of_mem hB, imp_self]
    rw [isRemainder_def'', isRemainder_def'']
    intro ⟨⟨g, B', hB', h₁, h₂⟩, h₃⟩
    split_ands
    · use g, (B'.erase 0)
      split_ands
      · simp [hB']
      · rw [h₁]
        congr 1
        by_cases hB'0 : 0 ∈ B'
        · nth_rw 1 [← Finset.insert_erase hB'0]
          rw [Finset.sum_insert_zero (a:=0)]
          simp
        · rw [Finset.erase_eq_self.mpr hB'0]
      ·
        simp_intro' b' hb'
        exact h₂ b' hb'.2
    · intro c hc b hbB hb
      exact h₃ c hc b (by simp [hbB]) hb
  · rw [isRemainder_def', isRemainder_def']
    intro ⟨⟨g, hg, h₁, h₂⟩, h₃⟩
    split_ands
    · use g
      split_ands
      · exact subset_trans hg (Set.subset_insert _ _)
      · exact h₁
      · intro b hb
        by_cases hb0 : b = 0
        · simp [hb0]
        · exact h₂ b ((Set.mem_insert_iff.mp hb).resolve_left hb0)
    · intro c hc b hb hbne0
      exact h₃ c hc b ((Set.mem_insert_iff.mp hb).resolve_left hbne0) hbne0

/--
Remainders are preserved with the zero polynomial removed from the set of divisors.
-/
lemma isRemainder_sdiff_singleton_zero_iff_isRemainder (p : MvPolynomial σ R)
  (B : Set (MvPolynomial σ R)) (r : MvPolynomial σ R) :
  m.IsRemainder p (B \ {0}) r ↔ m.IsRemainder p B r := by
  by_cases h : 0 ∈ B
  · rw [←isRemainder_of_insert_zero_iff_isRemainder, show insert 0 (B \ {0}) = B by simp [h]]
  · simp [h]

/--
The leading term in a multivariate polynomial is zero if and only if this polynomial is zero.
-/
lemma lm_eq_zero_iff (p : MvPolynomial σ R): m.leadingTerm p = 0 ↔ p = 0 := by
  simp only [leadingTerm, monomial_eq_zero, leadingCoeff_eq_zero_iff]

lemma leadingTerm_image_sdiff_singleton_zero (B : Set (MvPolynomial σ R)) :
  m.leadingTerm '' (B \ {0}) = (m.leadingTerm '' B) \ {0} := by
  apply subset_antisymm
  · intro p
    simp
    intro q hq hq' hpq
    exact ⟨⟨q, hq, hpq⟩, hpq ▸ (m.lm_eq_zero_iff _).not.mpr hq'⟩
  · intro p
    simp
    intro q hq hpq hp
    rw [←hpq, MonomialOrder.lm_eq_zero_iff] at hp
    exact ⟨q, ⟨hq, hp⟩, hpq⟩

lemma leadingTerm_image_insert_zero (B : Set (MvPolynomial σ R)) :
  m.leadingTerm '' (insert (0 : MvPolynomial σ R) B) = insert 0 (m.leadingTerm '' B) := by
  unfold leadingTerm
  apply subset_antisymm
  · simp_intro' p hp
    rwa [Eq.comm (a := p) (b := 0)]
  · simp_intro' p hp
    rwa [Eq.comm (a := 0) (b := p)]

@[simp]
lemma leadingTerm_zero : m.leadingTerm (0 : MvPolynomial σ R) = 0 := by
  rw [lm_eq_zero_iff]

-- @[reducible]
-- def leading_term_ideal : Ideal (MvPolynomial σ R) := Ideal.span (leadingTerm m '' (G' : Set (MvPolynomial σ R)))

/--
Fix a monomial order on the polynomial ring $k[x_1, \ldots, x_n]$.A finite subset $G = \{g_1, \ldots, g_t\}$ of an ideal $I \subseteq k[x_1, \ldots, x_n]$, with $I \ne \{0\}$, is said to be a **Gröbner basis** (or standard basis) if
  $$
  \langle \operatorname{LT}(g_1), \ldots, \operatorname{LT}(g_t) \rangle = \langle \operatorname{LT}(I) \rangle.
  $$
  Using the convention that $\langle \emptyset \rangle = \{0\}$, we define the empty set $\emptyset$ to be the Gröbner basis of the zero ideal $\{0\}$.
-/
def IsGroebnerBasis {R : Type*} [CommSemiring R] (G': Finset (MvPolynomial σ R)) (I : Ideal (MvPolynomial σ R)) :=
  G'.toSet ⊆ I ∧
  Ideal.span (m.leadingTerm '' ↑I)
    = Ideal.span (m.leadingTerm '' G'.toSet)

end CommSemiring

section CommRing
open Classical
variable {R : Type*} [CommRing R] {s : σ →₀ ℕ}


/--
The $S$-polynomial of $f$ and $g$ is the combination
  $$
  S(f, g) = \frac{x^\gamma}{\mathrm{LT}(f)} \cdot f - \frac{x^\gamma}{\mathrm{LT}(g)} \cdot g.
  $$
-/
noncomputable def sPolynomial (f g : MvPolynomial σ R) : MvPolynomial σ R :=
  monomial (m.degree g - m.degree f) (m.leadingCoeff g) * f -
  monomial (m.degree f - m.degree g) (m.leadingCoeff f) * g

/--
the S-polynomial of $f$ and $g$ is antisymmetric:
  $$
    \Sph{f}{g} = -\Sph{g}{f}
  $$
-/
lemma sPolynomial_antisymm (f g : MvPolynomial σ R) :
   m.sPolynomial f g = - m.sPolynomial g f := by
   unfold sPolynomial
   exact
     Eq.symm
       (neg_sub ((monomial (m.degree f - m.degree g)) (m.leadingCoeff f) * g)
         ((monomial (m.degree g - m.degree f)) (m.leadingCoeff g) * f))

/--
  For any polynomial $g \in \MvPolynomial{\sigma}{R}$ and monomial order $m$,
  the S-polynomial with zero as first argument vanishes:
  $$
    \Sph{0}{g} = 0
  $$
-/
lemma sPolynomial_eq_zero_of_left_eq_zero (g : MvPolynomial σ R) :
  m.sPolynomial 0 g = 0 := by
  unfold sPolynomial
  simp only [zero_mul, sub_zero, leadingCoeff_zero, monomial_zero]
  exact CommMonoidWithZero.mul_zero ((monomial (m.degree g - m.degree 0)) (m.leadingCoeff g))

/--
  For any polynomial $g \in \MvPolynomial{\sigma}{R}$ and monomial order $m$,
  the S-polynomial with zero as second argument vanishes:
  $$
    \Sph{f}{0} = 0
  $$
-/
lemma sPolynomial_eq_zero_of_right_eq_zero' (f : MvPolynomial σ R) :
  m.sPolynomial f 0 = 0 := by
  rw [sPolynomial_antisymm, sPolynomial_eq_zero_of_left_eq_zero, neg_zero]

lemma sPolynomial_def (f g : MvPolynomial σ R) :
    m.sPolynomial f g =
      monomial (m.degree f ⊔ m.degree g - m.degree f) (m.leadingCoeff g) * f -
      monomial (m.degree f ⊔ m.degree g - m.degree g) (m.leadingCoeff f) * g := by
  rw [sPolynomial]
  congr 4
  <;> rw [Finsupp.ext_iff]
  <;> simp_intro' a
  <;> by_cases h : (m.degree f) a ≤ (m.degree g) a
  ·simp [h]
  ·simp [le_of_lt (not_le.mp h)]
  ·simp [h]
  ·simp [le_of_lt (not_le.mp h)]

/--
  Let $G'' \subseteq R[\mathbf{X}]$ be a set of polynomials where every nonzero element has a unit leading coefficient:
  $$
    \forall g \in G'',\ \big(\mathrm{IsUnit}(\LC_m(g)) \lor g = 0\big)
  $$
  Then for any polynomial $p \in R[\mathbf{X}]$, there exists a remainder $r$ satisfying:
  $$
    \mathsf{IsRemainder}_m\,p\,G''\,r
  $$
  where $\LC_m(g)$ denotes the leading coefficient of $g$ under monomial order $m$.
-/
theorem div_set' {B : Set (MvPolynomial σ R)}
    (hB : ∀ b ∈ B, (IsUnit (m.leadingCoeff b) ∨ b = 0)) (p : MvPolynomial σ R) :
    ∃ (r : MvPolynomial σ R), m.IsRemainder p B r := by
  have hB₁ : ∀ b ∈ B \ {0}, IsUnit (m.leadingCoeff b) := by
    intro b hb
    obtain ⟨hb₁, hb₂⟩ := hb
    obtain (h1 | h2) := hB b hb₁
    · exact h1
    · contradiction
  obtain ⟨g, r, h⟩ := MonomialOrder.div_set hB₁ p
  exists r
  refine (isRemainder_sdiff_singleton_zero_iff_isRemainder m p B r).mp ?_
  rcases h with ⟨h₁, h₂, h₃⟩
  unfold IsRemainder
  simp at *
  split_ands
  · use g
  · exact h₃

-- this part is some lemma about leadingTerm
theorem toSyn_eq_zero_iff (σ: Type*) (m : MonomialOrder σ) (a: σ →₀ ℕ) :
    m.toSyn a =0 ↔ a = 0 := by
  constructor
  · intro h
    exact (AddEquiv.map_eq_zero_iff m.toSyn).mp h
  · intro h
    exact (AddEquiv.map_eq_zero_iff m.toSyn).mpr h

theorem degree_eq_zero_iff{f : MvPolynomial σ R} :
    m.degree f = 0 ↔ f = C (m.leadingCoeff f) := by
  constructor
  · intro h
    simp [leadingCoeff]
    apply MonomialOrder.eq_C_of_degree_eq_zero h
  · intro h
    rw [h]
    simp [leadingCoeff]

lemma leadingTerm_degree_eq (f : MvPolynomial σ R) :
  m.degree (m.leadingTerm f) = m.degree f := by
    classical
    by_cases h : f = 0 <;> simp [leadingTerm,h]
    have : m.leadingCoeff f != 0 := by
      simp [leadingCoeff, h]
    simp [MonomialOrder.degree_monomial]
    exact fun a ↦ False.elim (h a)

lemma leadingTerm_degree_eq' (f : MvPolynomial σ R) :
  m.toSyn (m.degree (m.leadingTerm f)) = m.toSyn (m.degree f) := by
    classical
    by_cases h : f = 0 <;> simp [leadingTerm,h]
    have : m.leadingCoeff f != 0 := by
      simp [leadingCoeff, h]
    simp [MonomialOrder.degree_monomial]
    exact fun a ↦ False.elim (h a)

lemma degree_sub_leadingTerm (f : MvPolynomial σ R) :
    (m.degree (f - m.leadingTerm f) ≺[m] m.degree f) ∨ (f - m.leadingTerm f = 0) := by
  by_cases h : f - m.leadingTerm f = 0
  · right
    exact h
  · left
    push_neg at h
    have hc : (f - m.leadingTerm f).coeff (m.degree f) = 0 := by
      rw [coeff_sub]
      simp [coeff_monomial, leadingTerm]
      simp [leadingCoeff]
    have h1: m.toSyn ( m.degree (f - m.leadingTerm f)) ≠  m.toSyn (m.degree f) := by
      simp [degree_eq_zero_iff]
      by_contra h
      have hin: m.degree (f - m.leadingTerm f) ∈ (f - m.leadingTerm f).support := by
        (expose_names; exact (degree_mem_support_iff m (f - m.leadingTerm f)).mpr h_1)
      rw [h] at hin
      have : (f - m.leadingTerm f).coeff (m.degree f) ≠  0 := by
        refine mem_support_iff.mp ?_
        exact hin
      exact this hc
    have h₃: m.toSyn (m.degree (f - m.leadingTerm f)) ≤  m.toSyn (m.degree f) := by
      have h₃': m.toSyn (m.degree (f - m.leadingTerm f)) ≤  m.toSyn (m.degree f) ⊔ m.toSyn (m.degree (m.leadingTerm f)) := by
        apply degree_sub_le
      have h₃'':  m.toSyn (m.degree f) = m.toSyn (m.degree (m.leadingTerm f)) := by
        exact Eq.symm (leadingTerm_degree_eq' m f)
      have h3:  m.toSyn (m.degree f) ⊔ m.toSyn (m.degree (m.leadingTerm f)) = m.toSyn (m.degree f) := by
        simp [max_le_iff, h₃'']
      exact le_of_le_of_eq h₃' h3
    exact lt_of_le_of_ne h₃ h1


variable {m} in
lemma degree_sPolynomial_lt_sup_degre_lt_degree {f : MvPolynomial σ R} (h : f - m.leadingTerm f ≠ 0) :
    m.degree (f - m.leadingTerm f) ≺[m] m.degree f :=
  (or_iff_left h).mp <| m.degree_sub_leadingTerm f

lemma degree_sub_leadingTerm_lt_iff {f : MvPolynomial σ R} :
    m.degree (f - m.leadingTerm f) ≺[m] m.degree f ↔ m.degree f ≠ 0 := by
  classical
  constructor
  · intro h
    by_contra h'
    simp [h'] at h
    have : m.toSyn (m.degree (f - m.leadingTerm f)) ≥ 0 := by
      exact zero_le m (m.toSyn (m.degree (f - m.leadingTerm f)))
    apply not_le_of_lt h this
  · intro h
    by_cases hl: f - m.leadingTerm f = 0
    · simp [hl]
      have h1: m.toSyn (m.degree f) ≥ 0 := by
        exact zero_le m (m.toSyn (m.degree f))
      have h2: m.toSyn (m.degree f) ≠ 0 := by
        exact (AddEquiv.map_ne_zero_iff m.toSyn).mpr h
      exact lt_of_le_of_ne h1 (id (Ne.symm h2))
    · exact degree_sPolynomial_lt_sup_degre_lt_degree hl

lemma degree_sPolynomial (f g : MvPolynomial σ R) :
    ((m.degree <| m.sPolynomial f g) ≺[m] m.degree f ⊔ m.degree g) ∨ m.sPolynomial f g = 0 := by
  by_cases hf : m.degree f = 0 



variable {m} in
lemma degree_sPolynomial_lt_sup_degree [NoZeroDivisors R] {f g : MvPolynomial σ R} (h : m.sPolynomial f g ≠ 0) :
    (m.degree <| m.sPolynomial f g) ≺[m] m.degree f ⊔ m.degree g :=
  (or_iff_left h).mp <| m.degree_sPolynomial f g

/-- Monomial degree of product -/
lemma degree_mul' [NoZeroDivisors R] {f g : MvPolynomial σ R} (hf : f * g ≠ 0) :
    m.degree (f * g) = m.degree f + m.degree g := by
  rw [mul_ne_zero_iff] at hf
  exact m.degree_mul hf.1 hf.2

end CommRing

section Field

variable {k : Type*} [Field k]

/--
Let $k$ be a field, and let $G'' \subseteq k[x_i : i \in \sigma]$ be a set of polynomials.
Then for any $p \in k[x_i : i \in \sigma]$, there exists a generalized remainder $r$ of $p$ upon division by $G''$.
-/
theorem div_set'' (B : Set (MvPolynomial σ k))
    (p : MvPolynomial σ k) :
    ∃ (r : MvPolynomial σ k), m.IsRemainder p B r := by
  apply div_set'
  simp [em']

lemma sPolynomial_mul_monomial (p₁ p₂ : MvPolynomial σ k) (d₁ d₂ : σ →₀ ℕ) (c₁ c₂ : k) :
    m.sPolynomial ((monomial d₁ c₁) * p₁) ((monomial d₂ c₂) * p₂) =
      monomial ((d₁ + m.degree p₁) ⊔ (d₂ + m.degree p₂) - m.degree p₁ ⊔ m.degree p₂) (c₁ * c₂) *
      m.sPolynomial p₁ p₂ := by
  classical
  simp only [sPolynomial_def]
  by_cases hc1 : c₁ = 0
  · by_cases hc2 : c₂ = 0
    · simp [hc1, hc2]
    · simp [hc1]
  · by_cases hc2 : c₂ = 0
    · simp [hc2]
    · by_cases hp1 : p₁ = 0
      · simp [hp1]
      · by_cases hp2 : p₂ = 0
        · simp [hp2]
        · have eq1: m.leadingCoeff ((monomial d₁) c₁ * p₁) =  c₁ * m.leadingCoeff p₁ := by
            rw [MonomialOrder.leadingCoeff_mul]
            simp
            · simp [hc1]
            · exact hp1
          have eq2: m.leadingCoeff ((monomial d₂) c₂ * p₂) =  c₂ * m.leadingCoeff p₂ := by
            rw [MonomialOrder.leadingCoeff_mul]
            simp
            · simp [hc2]
            · exact hp2
          have eq3: m.degree ((monomial d₁) c₁ * p₁) = d₁ + m.degree p₁ := by
            rw [MonomialOrder.degree_mul]
            simp
            ·
              simp [degree_monomial]
              exact fun a ↦ False.elim (hc1 a)
            · simp [hc1]
            · exact hp1
          have eq4: m.degree ((monomial d₂) c₂ * p₂) = d₂ + m.degree p₂ := by
            rw [MonomialOrder.degree_mul]
            simp
            · simp [degree_monomial]
              exact fun a ↦ False.elim (hc2 a)
            · simp [hc2]
            · exact hp2
          simp_rw [eq1, eq2, eq3, eq4]
          have : monomial ((d₁ + m.degree p₁) ⊔ (d₂ + m.degree p₂) - (d₁ + m.degree p₁)) (c₂ * m.leadingCoeff p₂) = (c₂ * m.leadingCoeff p₂) • monomial ((d₁ + m.degree p₁) ⊔ (d₂ + m.degree p₂) - (d₁ + m.degree p₁)) 1:= by
            sorry
          simp [this]
          ring_nf
          sorry

end Field
