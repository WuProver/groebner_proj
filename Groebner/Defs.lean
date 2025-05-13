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

end CommRing

section Field

/--
Let $k$ be a field, and let $G'' \subseteq k[x_i : i \in \sigma]$ be a set of polynomials.
Then for any $p \in k[x_i : i \in \sigma]$, there exists a generalized remainder $r$ of $p$ upon division by $G''$.
-/
theorem div_set'' {k : Type*} [Field k] {B : Set (MvPolynomial σ k)}
    (p : MvPolynomial σ k) :
    ∃ (r : MvPolynomial σ k), m.IsRemainder p B r := by
  apply div_set'
  simp [em']


end Field
