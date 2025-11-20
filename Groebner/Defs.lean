import Mathlib
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.Finset.Functor
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.RingTheory.Ideal.Span
import Groebner.Indentation

namespace MonomialOrder

open MvPolynomial
variable {σ : Type*} (m : MonomialOrder σ)

section CommSemiring
variable {R : Type*} [CommSemiring R]
variable (f p : MvPolynomial σ R) (B : Set (MvPolynomial σ R)) (r : MvPolynomial σ R)

/--
0 is less then any `σ →₀ ℕ` w.r.t. monomial order.
-/
-- merged: https://github.com/leanprover-community/mathlib4/pull/24361
@[simp]
lemma zero_le._mathlib (a : m.syn) : 0 ≤ a := bot_le

-- merged: https://github.com/leanprover-community/mathlib4/pull/26062
lemma toSyn_eq_zero_iff._mathlib (a : σ →₀ ℕ) :
    m.toSyn a = 0 ↔ a = 0 := AddEquiv.map_eq_zero_iff m.toSyn

-- merged: https://github.com/leanprover-community/mathlib4/pull/26062
lemma toSyn_lt_iff_ne_zero._mathlib {a : m.syn} :
    0 < a ↔ a ≠ 0 := bot_lt_iff_ne_bot


-- #check Polynomial.degree_add_eq_left_of_degree_lt

-- lemma degree_add_eq_left_of_degree_lt
--   (h : m.degree p ≺[m] m.degree f) : m.degree (f + p) = m.degree f := by
--   exact degree_add_of_lt h

-- merged: https://github.com/leanprover-community/mathlib4/pull/26000
lemma degree_eq_zero_iff._mathlib_ {f : MvPolynomial σ R} :
    m.degree f = 0 ↔ f = C (m.leadingCoeff f) := by
  constructor
  · intro h
    apply MonomialOrder.eq_C_of_degree_eq_zero h
  · intro h
    rw [h]
    simp

-- merged: https://github.com/leanprover-community/mathlib4/pull/26000
variable {f p} in
lemma degree_add_eq_right_of_lt._mathlib_
    (h : m.degree f ≺[m] m.degree p) : m.degree (f + p) = m.degree p := by
  rw [add_comm]
  exact degree_add_of_lt h

-- merged: https://github.com/leanprover-community/mathlib4/pull/26000
lemma degree_sum_le._mathlib_ {α : Type*} {s : Finset α} {f : α → MvPolynomial σ R} :
    (m.toSyn <| m.degree <| ∑ x ∈ s, f x) ≤ s.sup fun x => (m.toSyn <| m.degree <| f x) := by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s haA h =>
    rw [Finset.sum_cons, Finset.sup_cons]
    exact le_trans m.degree_add_le (max_le_max le_rfl h)

-- merged: https://github.com/leanprover-community/mathlib4/pull/26000
variable {m} in
lemma ne_zero_of_degree_ne_zero._mathlib_ {f : MvPolynomial σ R} (h : m.degree f ≠ 0) : f ≠ 0 := by
  rintro rfl
  exact h m.degree_zero

-- merged: https://github.com/leanprover-community/mathlib4/pull/26000
lemma degree_mem_support_iff._mathlib_ (f : MvPolynomial σ R) : m.degree f ∈ f.support ↔ f ≠ 0 :=
  mem_support_iff.trans coeff_degree_ne_zero_iff

/--
The leading term in a non-zero multivariate polynomial is the term of the polynomial's degree in
the polynomial. The leading term in the zero polynomial is defined as the zero polynomial.
-/
-- submitted: https://github.com/leanprover-community/mathlib4/pull/26039
noncomputable def leadingTerm (f : MvPolynomial σ R) : MvPolynomial σ R :=
  monomial (m.degree f) (m.leadingCoeff f)

/--
Given a multivariate polynomial $f$ and a set $B$ of multivariate polynomials over a commutative
semiring $R$, and a monomial order. If there exists a $g : B \to R[X]$ with finite support, and a
multivriate polynomial $r$, such that

1. $f = \sum_{b\in B} g(b)b + r$
2. degree of any non-zero $g(b)b$ where b\in B is less than or equal to the degree of $p$,
3. none of terms of $r$ is divisible by leading monomial of a non-zero elements of $B$,

then $r$ is called a **remainder** of $p$ on division by "divisors" $B$.

A statement that `r` is a remainder of `p` on division by `B` w.r.t. a monomial order `m` is
denoted as `m.IsRemainder p B r`.
-/
-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
def IsRemainder :=
  (∃ (g : B →₀ MvPolynomial σ R),
    f = Finsupp.linearCombination _ (fun (b : B) ↦ (b : MvPolynomial σ R)) g + r ∧
    ∀ (b : B), m.degree ((b : MvPolynomial σ R) * (g b)) ≼[m] m.degree f) ∧
  ∀ c ∈ r.support, ∀ b ∈ B, b ≠ 0 → ¬ (m.degree b ≤ c)

theorem isRemainder_range {ι : Type*} (b : ι → MvPolynomial σ R) (r : MvPolynomial σ R) :
    m.IsRemainder p (Set.range b) r ↔
      (∃ g : ι →₀ MvPolynomial σ R,
        p = Finsupp.linearCombination _ b g + r ∧
        ∀ i : ι, m.degree (b i * g i) ≼[m] m.degree p) ∧
      ∀ c ∈ r.support, ∀ i : ι, b i ≠ 0 → ¬ (m.degree (b i) ≤ c) := by
  classical
  constructor
  · rintro ⟨⟨g, h₁, h₂⟩, h₃⟩
    -- map an element in range of `b` to one of its indexes (whose type is `ι`)
    let f : (↑(Set.range b)) ↪ ι := {
      toFun := Set.rangeSplitting b,
      inj' := Set.rangeSplitting_injective b
    }
    split_ands
    · use Finsupp.embDomain f g
      split_ands
      · ext
        simp [h₁, Finsupp.linearCombination_apply, Finsupp.sum]
        congr
        simp [f, Set.apply_rangeSplitting]
      · intro i
        specialize h₂ ⟨b i, Set.mem_range_self i⟩
        simp at h₂
        by_cases h' : (Finsupp.embDomain f g) i = 0
        · simp [h']
        simp at h'
        convert h₂
        generalize_proofs hbi
        convert_to g.embDomain f (hbi.choose) = _
        · simp [Finsupp.embDomain_eq_mapDomain, Finsupp.mapDomain, Finsupp.single_apply] at ⊢ h'
          congr
          ext
          congr
          obtain ⟨a, ha, ha'⟩ := Finset.exists_ne_zero_of_sum_ne_zero h'
          simp [f] at ha'
          convert_to i = Set.rangeSplitting b ⟨b i, hbi⟩
          simp [← ha'.1, Set.apply_rangeSplitting]
        · exact Finsupp.embDomain_apply f g ⟨b i, hbi⟩
    · intro i hi b hb
      aesop
  · rintro ⟨⟨g, h₁, h₂⟩, h₃⟩
    refine ⟨?_, ?_⟩
    · let b_support : Finset (Set.range b) :=
        (g.support.biUnion fun i ↦
          {⟨b i, Set.mem_range_self i⟩})
      let b' : ι → Set.range b := fun i ↦ ⟨b i, Set.mem_range_self i⟩
      let g' : Set.range b → MvPolynomial σ R :=
        fun x ↦ Finset.sum (g.support.filter fun i ↦ b' i = x) fun i ↦ g i
      have mem_support : ∀ x, g' x ≠ 0 → x ∈ b_support := by
        intro x hx
        obtain ⟨i, hi, hb'x⟩ : ∃ i ∈ g.support, b' i = x := by
          contrapose! hx
          simp [g']
          rw [Finset.sum_filter]
          suffices (g.support.filter (fun i => b' i = x)) = ∅ by
            rw [← Finset.sum_filter, this, Finset.sum_empty]
          ext i
          simp at hx
          simp
          exact hx i
        simp [b_support, Finset.mem_biUnion]
        use i
        constructor
        · exact Finsupp.mem_support_iff.mp hi
        · exact hb'x.symm
      use Finsupp.onFinset b_support g' mem_support
      split_ands
      · simp [h₁, Finsupp.linearCombination_apply, Finsupp.sum]
        congr
        calc
          ∑ x ∈ g.support, g x * b x
            = ∑ x ∈ g.support, g x * (b' x : MvPolynomial σ R) := by rfl
          _ = ∑ y ∈ Finset.image b' g.support,
              (∑ x ∈ g.support.filter (b' · = y), g x) * (y : MvPolynomial σ R) := by
            rw [Finset.sum_image']
            intro y hy
            rw [Finset.sum_filter]
            ext x
            congr
            calc
              (∑ a ∈ g.support, if b' a = b' y then g a else 0) * ↑(b' y) =
                  (∑ j ∈ g.support.filter (fun j ↦ b' j = b' y), g j) * ↑(b' y) := by
                congr 1
                simp [Finset.sum_filter]
              _ = ∑ j ∈ g.support.filter (fun j ↦ b' j = b' y), g j * ↑(b' y) :=
                Finset.sum_mul ({j ∈ g.support | b' j = b' y}) ⇑g ↑(b' y)
              _ = ∑ j ∈ g.support.filter (fun j ↦ b' j = b' y), g j * ↑(b' j) := by
                apply Finset.sum_congr rfl
                intro j hj
                congr 2
                exact (Finset.mem_filter.mp hj).2.symm
          _ = ∑ y ∈ Finset.image b' g.support, g' y * (y : MvPolynomial σ R) := by rfl
          _ = ∑ y ∈ b_support, g' y * (y : MvPolynomial σ R) := by
            congr
            ext y
            simp [b_support, Eq.comm (a:=y), b']
          _ = ∑ x ∈ (Finsupp.onFinset b_support g' mem_support).support, g' x * ↑x := by
            rw [Finsupp.support_onFinset, Finset.sum_filter]
            congr
            ext x
            by_cases hx : g' x = 0 <;> simp [hx]
      · intro b1
        simp [Finsupp.onFinset, g']
        rw [Finset.mul_sum]
        have sum_eq : (∑ i ∈ g.support.filter (fun i => b' i = b1), ↑b1 * g i) =
            (∑ i ∈ g.support.filter (fun i => b' i = b1), b i * g i) := by
          refine Finset.sum_congr rfl fun i hi ↦ ?_
          rw [Finset.mem_filter] at hi
          congr
          exact Subtype.eq_iff.mp hi.2.symm
        rw [sum_eq]
        have degree_le : ∀ i ∈ g.support.filter (fun i => b' i = b1),
            m.degree (b i * g i) ≼[m] m.degree p := by
          intro i hi
          rw [Finset.mem_filter] at hi
          exact h₂ i
        trans (g.support.filter fun i ↦ b' i = b1).sup fun i ↦ m.toSyn (m.degree (b i * g i))
        · exact m.degree_sum_le
        · exact Finset.sup_le (fun i hi ↦ degree_le i hi)
    · aesop

theorem isRemainder_range_fin {ι : Type*} [Fintype ι] (b : ι → MvPolynomial σ R)
    (r : MvPolynomial σ R) :
      m.IsRemainder p (Set.range b) r ↔
      (∃ g : ι → MvPolynomial σ R,
          p = ∑ i : ι, (b i * g i) + r ∧
          ∀ i : ι, m.degree (b i * g i) ≼[m] m.degree p) ∧
        ∀ c ∈ r.support, ∀ i : ι, b i ≠ 0 → ¬ (m.degree (b i) ≤ c) := by
  classical
  rw [isRemainder_range]
  constructor
  · rintro ⟨⟨g, h₁, h₂⟩, h₃⟩
    split_ands
    · use g.toFun
      split_ands
      · simp [Finsupp.linearCombination_apply, Finsupp.sum] at h₁
        rw [h₁]
        congr 1
        have h₁: ∑ i, b i * g.toFun i = ∑ i, b i * g i  := by
          apply Finset.sum_congr rfl
          intro i _
          congr 1
        simp [h₁]
        have : (∑ i : ι, b i * g i) = ∑ x ∈ g.support, b x * g x := by
          refine Eq.symm (Fintype.sum_subset ?_)
          intro _ h
          contrapose! h
          simp [Finsupp.notMem_support_iff.mp h]
        rw [this]
        simp_rw [mul_comm (g _) (b _)]
      · exact h₂
    · exact h₃
  · rintro ⟨⟨g, h₁, h₂⟩, h₃⟩
    split_ands
    · use Finsupp.onFinset Finset.univ (fun i => g i) (by simp_intro ..)
      split_ands
      · simp [h₁]
        simp [Finsupp.linearCombination_apply, Finsupp.sum]
        have : (∑ i : ι, b i * g i) = ∑ x ∈ Finset.univ, b x * g x := by
          rfl
        rw [this]
        congr 1
        have support_eq : (Finsupp.onFinset Finset.univ (fun i ↦ g i) (by simp)).support =
          Finset.univ.filter (fun i => g i ≠ 0) := by
          ext i
          simp [Finsupp.mem_support_iff, Finsupp.onFinset_apply]
        rw [support_eq]

        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : g i = 0 <;> simp [hi]
        exact CommMonoid.mul_comm (b i) (g i)
      · intro i
        exact h₂ i
    · aesop

open Classical

-- it may free you from coercion between different kinds of "sets",
-- "finite subsets", "finite subsets" of "sets", ...,
-- when you are dealing with different G''
/--
A variant of `IsRemainder` without coercion of a `Set (MvPolynomial σ R)`.
-/
-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
lemma isRemainder_def' (p : MvPolynomial σ R) (B : Set (MvPolynomial σ R)) (r : MvPolynomial σ R) :
    m.IsRemainder p B r ↔
      (∃ (g : MvPolynomial σ R →₀ MvPolynomial σ R),
        ↑g.support ⊆ B ∧
        p = Finsupp.linearCombination _ id g + r ∧
        ∀ b ∈ B, m.degree ((b : MvPolynomial σ R) * (g b)) ≼[m] m.degree p) ∧
      ∀ c ∈ r.support, ∀ g' ∈ B, g' ≠ 0 → ¬ (m.degree g' ≤ c) := by
  constructor
  · intro ⟨⟨g, h₁, h₂⟩, h₃⟩
    split_ands
    · use g.mapDomain Subtype.val
      split_ands
      · exact subset_trans (Finset.coe_subset.mpr Finsupp.mapDomain_support) (by simp)
      · simp [h₁]
      · intro b hb
        rw [show b = ↑(Subtype.mk b hb) by rfl, Finsupp.mapDomain_apply (by simp)]
        exact h₂ ⟨b, hb⟩
    · exact h₃
  · intro ⟨⟨g, hg, h₁, h₂⟩, h₃⟩
    split_ands
    · use {
        support := (g.support.subtype (· ∈ B)),
        toFun := (g.toFun ·),
        mem_support_toFun := by intro; simp; rfl
      }
      split_ands
      · rw [h₁, eq_comm]
        congr 1
        simp [Finsupp.linearCombination_apply, Finsupp.sum]
        apply Finset.sum_nbij (↑·)
        · simp_intro ..
        · simp_intro b _ b₁ _ h [Subtype.eq_iff]
        · simp_intro b hb
          exact Set.mem_of_subset_of_mem hg <| Finsupp.mem_support_iff.mpr hb
        · simp [DFunLike.coe]
      · simpa
    · exact h₃

/--
A variant of `IsRemainder` where `g : MvPolynomial σ R →₀ MvPolynomial σ R` is replaced with a
function `g : MvPolynomial σ R → MvPolynomial σ R` without limitation on its support.
-/
-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
lemma isRemainder_def'' (p : MvPolynomial σ R) (B : Set (MvPolynomial σ R)) (r : MvPolynomial σ R) :
    m.IsRemainder p B r ↔
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
    · use Finsupp.onFinset B' (fun b' => if b' ∈ B' then g b' else 0) (by simp_intro ..)
      split_ands
      · simp_intro b' hb'
        exact Set.mem_of_mem_of_subset hb'.1 h₁
      · rw [Finsupp.linearCombination_apply, Finsupp.sum, h₂, Finsupp.support_onFinset]
        congr 1
        simp [Finset.filter_and, Finset.filter_mem_eq_inter,
          Finset.inter_self, Finset.inter_filter, Finset.filter_inter]
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro b' _
        by_cases hb' : g b' = 0 <;> simp [hb']
      · intro b hb
        by_cases hbB' : b ∈ B'
        · simp [hbB', h₃]
        · simp [hbB']
    · exact h₄

-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
lemma isRemainder_finset (p : MvPolynomial σ R) (B' : Finset (MvPolynomial σ R))
    (r : MvPolynomial σ R) :
      m.IsRemainder p B' r ↔
        (∃ (g : MvPolynomial σ R → MvPolynomial σ R),
          p = B'.sum (fun x => g x * x) + r ∧
          ∀ b' ∈ B', m.degree ((b' : MvPolynomial σ R) * (g b')) ≼[m] m.degree p) ∧
        ∀ c ∈ r.support, ∀ b ∈ B', b ≠ 0 → ¬ (m.degree b ≤ c) := by
  constructor
  · rw [isRemainder_def']
    intro ⟨⟨g, hgsup, hsum, hg⟩, hr⟩
    split_ands
    · use g.toFun
      split_ands
      · simp [Finsupp.linearCombination_apply, Finsupp.sum] at hsum
        rw [hsum]
        congr 1
        apply Finset.sum_subset hgsup
        simp_intro ..
      · exact hg
    · exact hr
  · rw [isRemainder_def'']
    intro ⟨⟨g, hsum, hg⟩, hr⟩
    refine ⟨?_, hr⟩
    use fun b' ↦ if b' ∈ B' then g b' else 0
    use B'
    split_ands
    · rfl
    · simp [hsum]
    · simp_intro .. [hg]

/--
Remainders are preserved on insertion of the zero polynomial into the set of divisors.
-/
-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
lemma isRemainder_insert_zero_iff_isRemainder (p : MvPolynomial σ R)
    (B : Set (MvPolynomial σ R)) (r : MvPolynomial σ R) :
    m.IsRemainder p (insert 0 B) r ↔ m.IsRemainder p B r := by
  constructor
  · by_cases hB : 0 ∈ B
    · simp only [Set.insert_eq_of_mem hB, imp_self]
    simp_rw [isRemainder_def'']
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
      · simp_intro b' hb'
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
-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
lemma isRemainder_sdiff_singleton_zero_iff_isRemainder (p : MvPolynomial σ R)
    (B : Set (MvPolynomial σ R)) (r : MvPolynomial σ R) :
    m.IsRemainder p (B \ {0}) r ↔ m.IsRemainder p B r := by
  by_cases h : 0 ∈ B
  · rw [←isRemainder_insert_zero_iff_isRemainder, show insert 0 (B \ {0}) = B by simp [h]]
  · simp [h]

-- theorem degree_mul_of_isUnit_left {f g : MvPolynomial σ R}
--     (hf : ∀ b ∈ B, IsUnit (m.leadingCoeff f)) (hg : g ≠ 0) :
--     m.degree (f * g) = m.degree f + m.degree g := degree_mul_of_isRegular_left (IsUnit.isRegular hf) hg

-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
variable {m B} in
lemma isRemainder_zero {r : MvPolynomial σ R} (hB : ∀ b ∈ B, IsRegular (m.leadingCoeff b))
    (h : m.IsRemainder 0 B r) : r = 0 := by
  unfold IsRemainder at h
  obtain ⟨⟨g, h0sumg, hg⟩, hr⟩ := h
  conv at hg =>
    intro b
    simp
    rw [← m.eq_zero_iff, AddEquiv.map_eq_zero_iff, mul_comm]
  simp [Finsupp.linearCombination_apply, Finsupp.sum] at h0sumg
  have rdeg0 : m.degree r = 0 := by
    apply congrArg m.degree at h0sumg
    contrapose! h0sumg
    simp [-ne_eq]
    rw [ne_comm, ← AddEquiv.map_ne_zero_iff m.toSyn, ← m.toSyn_lt_iff_ne_zero, add_comm]
    rw [← AddEquiv.map_ne_zero_iff m.toSyn, ← m.toSyn_lt_iff_ne_zero] at h0sumg
    rwa [degree_add_of_lt]
    apply lt_of_le_of_lt m.degree_sum_le
    simp [hg]
    exact lt_of_le_of_lt Finset.sup_const_le h0sumg
  contrapose! hr
  use 0
  split_ands
  · rw [m.degree_eq_zero_iff.mp rdeg0]; simp [hr]
  contrapose! h0sumg
  simp at h0sumg
  suffices ∀ b : B, g b * ↑b = 0 by simp [this, hr.symm]
  intro b
  suffices g b = 0 ∨ b.1 = 0 by by_cases h : g b = 0; simp [h]; simp [this.resolve_left h]
  rw [or_iff_not_imp_right]
  intro hb
  specialize hg b
  specialize h0sumg b b.2 hb
  contrapose! hg
  rw [m.degree_mul_of_isRegular_right hg <| hB ↑b (by simp)]
  simp [h0sumg]

-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
variable {m B} in
lemma isRemainder_zero₀ {r : MvPolynomial σ R} (hB : ∀ b ∈ B, IsRegular (m.leadingCoeff b) ∨ b = 0)
    (h : m.IsRemainder 0 B r) : r = 0 := by
  rw [← m.isRemainder_sdiff_singleton_zero_iff_isRemainder] at h
  refine m.isRemainder_zero ?_ h
  simp_intro .. [or_iff_not_imp_right.mp (hB _ _)]

-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
variable {m B} in
lemma isRemainder_zero' [IsCancelMulZero R] {r : MvPolynomial σ R} (h : m.IsRemainder 0 B r) :
    r = 0 := by
  refine isRemainder_zero₀ ?_ h
  intro b _
  rw [or_iff_not_imp_right]
  intro hb
  exact isRegular_of_ne_zero <| leadingCoeff_ne_zero_iff.mpr hb

-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
lemma isRemainder_finset₁ (p : MvPolynomial σ R) (B' : Finset (MvPolynomial σ R))
    (hB' : ∀ b' ∈ B', IsRegular (m.leadingCoeff b'))
    (r : MvPolynomial σ R) :
    m.IsRemainder p B' r ↔
      (∃ (g : MvPolynomial σ R → MvPolynomial σ R),
        p = B'.sum (fun x => g x * x) + r ∧
        (∀ b' ∈ B', m.degree ((b' : MvPolynomial σ R) * (g b')) ≼[m] m.degree p) ∧
        (p = 0 → g = 0)
      ) ∧
      ∀ c ∈ r.support, ∀ b ∈ B', b ≠ 0 → ¬ (m.degree b ≤ c) := by
  constructor
  · by_cases hp0 : p = 0
    · rw [hp0]
      intro h
      apply m.isRemainder_zero hB' at h
      simp [h]
    rw [isRemainder_finset]
    rintro ⟨⟨g, h₁, h₂⟩, h₃⟩
    exact ⟨⟨g, h₁, h₂, by simp [hp0]⟩, h₃⟩
  · rintro ⟨⟨g, h₁, h₂, -⟩, h₃⟩
    rw [isRemainder_finset]
    exact ⟨⟨g, h₁, h₂⟩, h₃⟩

-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
lemma isRemainder_finset₀₁ (p : MvPolynomial σ R) (B' : Finset (MvPolynomial σ R))
    (hB' : ∀ b' ∈ B', IsRegular (m.leadingCoeff b') ∨ b' = 0)
    (r : MvPolynomial σ R) :
    m.IsRemainder p B' r ↔
      (∃ (g : MvPolynomial σ R → MvPolynomial σ R),
        p = B'.sum (fun x => g x * x) + r ∧
        (∀ b' ∈ B', m.degree ((b' : MvPolynomial σ R) * (g b')) ≼[m] m.degree p) ∧
        (p = 0 → g = 0)
      ) ∧
      ∀ c ∈ r.support, ∀ b ∈ B', b ≠ 0 → ¬ (m.degree b ≤ c) := by
  constructor
  · by_cases hp0 : p = 0
    · rw [hp0]
      intro h
      apply m.isRemainder_zero₀ hB' at h
      simp [h]
    rw [isRemainder_finset]
    rintro ⟨⟨g, h₁, h₂⟩, h₃⟩
    exact ⟨⟨g, h₁, h₂, by simp [hp0]⟩, h₃⟩
  · rintro ⟨⟨g, h₁, h₂, -⟩, h₃⟩
    rw [isRemainder_finset]
    exact ⟨⟨g, h₁, h₂⟩, h₃⟩

-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
lemma isRemainder_finset'₁ [IsCancelMulZero R] (p : MvPolynomial σ R)
    (B' : Finset (MvPolynomial σ R))
    (r : MvPolynomial σ R) :
    m.IsRemainder p B' r ↔
      (∃ (g : MvPolynomial σ R → MvPolynomial σ R),
        p = B'.sum (fun x => g x * x) + r ∧
        (∀ b' ∈ B', m.degree ((b' : MvPolynomial σ R) * (g b')) ≼[m] m.degree p) ∧
        (p = 0 → g = 0)
      ) ∧
      ∀ c ∈ r.support, ∀ b ∈ B', b ≠ 0 → ¬ (m.degree b ≤ c) := by
  constructor
  · by_cases hp0 : p = 0
    · rw [hp0]
      intro h
      apply m.isRemainder_zero' at h
      simp [h]
    rw [isRemainder_finset]
    rintro ⟨⟨g, h₁, h₂⟩, h₃⟩
    exact ⟨⟨g, h₁, h₂, by simp [hp0]⟩, h₃⟩
  · rintro ⟨⟨g, h₁, h₂, -⟩, h₃⟩
    rw [isRemainder_finset]
    exact ⟨⟨g, h₁, h₂⟩, h₃⟩

theorem isRemainder_def'₁ [IsCancelMulZero R] (p : MvPolynomial σ R) (B : Set (MvPolynomial σ R))
    (r : MvPolynomial σ R) : m.IsRemainder p B r ↔
      (∃ (g : MvPolynomial σ R →₀ MvPolynomial σ R),
        ↑g.support ⊆ B ∧
        p = Finsupp.linearCombination _ id g + r ∧
        ∀ b ∈ B, m.degree ((b : MvPolynomial σ R) * (g b)) ≼[m] m.degree p ∧
        (p = 0 → g = 0)) ∧
      ∀ c ∈ r.support, ∀ g' ∈ B, g' ≠ 0 → ¬ (m.degree g' ≤ c) := by
  by_cases h : p ≠ 0
  · simp [isRemainder_def', h]
  push_neg at h
  rw [h]
  constructor
  · intro h'
    simp [isRemainder_zero' h']
    use 0
    simp
  · intro h'
    rw [isRemainder_def']
    aesop

/--
The leading term in a multivariate polynomial is zero if and only if this polynomial is zero.
-/
-- submitted: https://github.com/leanprover-community/mathlib4/pull/26039
@[simp]
lemma leadingTerm_eq_zero_iff (p : MvPolynomial σ R) : m.leadingTerm p = 0 ↔ p = 0 := by
  simp only [leadingTerm, monomial_eq_zero, leadingCoeff_eq_zero_iff]

-- submitted: https://github.com/leanprover-community/mathlib4/pull/26039
@[simp]
lemma leadingTerm_zero : m.leadingTerm (0 : MvPolynomial σ R) = 0 := by
  rw [leadingTerm_eq_zero_iff]

-- submitted: https://github.com/leanprover-community/mathlib4/pull/26039
lemma image_leadingTerm_sdiff_singleton_zero (B : Set (MvPolynomial σ R)) :
    m.leadingTerm '' (B \ {0}) = (m.leadingTerm '' B) \ {0} := by
  apply subset_antisymm
  · intro p
    simp
    intro q hq hq' hpq
    exact ⟨⟨q, hq, hpq⟩, hpq ▸ (m.leadingTerm_eq_zero_iff _).not.mpr hq'⟩
  · intro p
    simp
    intro q hq hpq hp
    rw [←hpq, MonomialOrder.leadingTerm_eq_zero_iff] at hp
    exact ⟨q, ⟨hq, hp⟩, hpq⟩

-- submitted: https://github.com/leanprover-community/mathlib4/pull/26039
lemma image_leadingTerm_insert_zero (B : Set (MvPolynomial σ R)) :
    m.leadingTerm '' (insert (0 : MvPolynomial σ R) B) = insert 0 (m.leadingTerm '' B) := by
  unfold leadingTerm
  apply subset_antisymm
  · simp_intro p hp
    rwa [Eq.comm (a := p) (b := 0)]
  · simp_intro p hp
    rwa [Eq.comm (a := 0) (b := p)]

/--
Fix a monomial order on the polynomial ring $k[x_1, \ldots, x_n]$.A finite subset
$G = \{g_1, \ldots, g_t\}$ of an ideal $I \subseteq k[x_1, \ldots, x_n]$,
with $I \ne \{0\}$, is said to be a **Gröbner basis** (or standard basis) if
  $$
  \langle \operatorname{LT}(g_1), \ldots, \operatorname{LT}(g_t) \rangle =
  \langle \operatorname{LT}(I) \rangle.
  $$
Using the convention that $\langle \emptyset \rangle = \{0\}$, we define the empty set $\emptyset$
to be the Gröbner basis of the zero ideal $\{0\}$.
-/
-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
def IsGroebnerBasis {R : Type*} [CommSemiring R] (G : Set (MvPolynomial σ R))
    (I : Ideal (MvPolynomial σ R)) :=
  G ⊆ I ∧ Ideal.span (m.leadingTerm '' ↑I) = Ideal.span (m.leadingTerm '' G)

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
-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
noncomputable def sPolynomial (f g : MvPolynomial σ R) : MvPolynomial σ R :=
  monomial (m.degree g - m.degree f) (m.leadingCoeff g) * f -
  monomial (m.degree f - m.degree g) (m.leadingCoeff f) * g

/--
the S-polynomial of $f$ and $g$ is antisymmetric:
  $$
    \Sph{f}{g} = -\Sph{g}{f}
  $$
-/
-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
lemma sPolynomial_antisymm (f g : MvPolynomial σ R) :
    m.sPolynomial f g = - m.sPolynomial g f :=
  Eq.symm (neg_sub (_ * g) (_ * f))

/--
For any polynomial $g \in \MvPolynomial{\sigma}{R}$ and monomial order $m$,
  the S-polynomial with zero as first argument vanishes:
  $$
    \Sph{0}{g} = 0
  $$
-/
-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
@[simp]
lemma sPolynomial_left_zero (g : MvPolynomial σ R) :
    m.sPolynomial 0 g = 0 := by
  simp [sPolynomial]

/--
For any polynomial $g \in \MvPolynomial{\sigma}{R}$ and monomial order $m$,
  the S-polynomial with zero as second argument vanishes:
  $$
    \Sph{f}{0} = 0
  $$
-/
-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
@[simp]
lemma sPolynomial_right_zero (f : MvPolynomial σ R) :
    m.sPolynomial f 0 = 0 := by
  rw [sPolynomial_antisymm, sPolynomial_left_zero, neg_zero]

-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
lemma sPolynomial_def (f g : MvPolynomial σ R) :
    m.sPolynomial f g =
      monomial (m.degree f ⊔ m.degree g - m.degree f) (m.leadingCoeff g) * f -
      monomial (m.degree f ⊔ m.degree g - m.degree g) (m.leadingCoeff f) * g := by
  unfold sPolynomial
  congr 4
  all_goals
    rw [Finsupp.ext_iff]
    simp_intro a
    by_cases h : (m.degree f) a ≤ (m.degree g) a
    ·simp [h]
    ·simp [le_of_lt (not_le.mp h)]

-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
@[simp]
lemma sPolynomial_self (f : MvPolynomial σ R) : m.sPolynomial f f = 0 := sub_self _

-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
theorem div_set' {B : Set (MvPolynomial σ R)}
    (hB : ∀ b ∈ B, IsUnit <| m.leadingCoeff b) (p : MvPolynomial σ R) :
    ∃ (r : MvPolynomial σ R), m.IsRemainder p B r := by
  obtain ⟨g, r, h⟩ := MonomialOrder.div_set hB p
  use r
  split_ands
  · use g
    exact ⟨h.1, h.2.1⟩
  · intro c hc b hb _
    exact h.2.2 c hc b hb

/--
Let $G'' \subseteq R[\mathbf{X}]$ be a set of polynomials where every nonzero element has a unit
leading coefficient:
  $$
    \forall g \in G'',\ \big(\mathrm{IsUnit}(\LC_m(g)) \lor g = 0\big)
  $$
  Then for any polynomial $p \in R[\mathbf{X}]$, there exists a remainder $r$ satisfying:
  $$
    \mathsf{IsRemainder}_m\,p\,G''\,r
  $$
  where $\LC_m(g)$ denotes the leading coefficient of $g$ under monomial order $m$.
-/
-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
theorem div_set'₀ {B : Set (MvPolynomial σ R)}
    (hB : ∀ b ∈ B, (IsUnit (m.leadingCoeff b) ∨ b = 0)) (p : MvPolynomial σ R) :
    ∃ (r : MvPolynomial σ R), m.IsRemainder p B r := by
  have hB₁ : ∀ b ∈ B \ {0}, IsUnit (m.leadingCoeff b) := by
    simp_intro .. [or_iff_not_imp_right.mp (hB _ _)]
  obtain ⟨r, h⟩ := m.div_set' hB₁ p
  exists r
  rwa [← m.isRemainder_sdiff_singleton_zero_iff_isRemainder]

-- the following part is some lemma about leadingTerm

-- submitted: https://github.com/leanprover-community/mathlib4/pull/26039
@[simp]
lemma degree_leadingTerm (f : MvPolynomial σ R) :
    m.degree (m.leadingTerm f) = m.degree f := by
  classical
  by_cases h : f = 0 <;> simp [leadingTerm,h]
  have : m.leadingCoeff f != 0 := by
    simp [leadingCoeff, h]
  simp [MonomialOrder.degree_monomial]
  exact fun a ↦ False.elim (h a)

@[simp]
lemma leadingCoeff_leadingTerm (f : MvPolynomial σ R) :
    m.leadingCoeff (m.leadingTerm f) = m.leadingCoeff f := by
  simp [leadingTerm, leadingCoeff_monomial]

-- submitted: https://github.com/leanprover-community/mathlib4/pull/26039
theorem degree_sub_leadingTerm_le (f : MvPolynomial σ R) :
    m.degree (f - m.leadingTerm f) ≼[m] m.degree f := by
  apply le_trans degree_sub_le
  simp [degree_leadingTerm]

-- submitted: https://github.com/leanprover-community/mathlib4/pull/26039
lemma degree_sub_leadingTerm (f : MvPolynomial σ R) :
    m.degree (f - m.leadingTerm f) ≺[m] m.degree f ∨ f - m.leadingTerm f = 0 := by
  classical
  rw [or_iff_not_imp_right]
  intro h
  apply lt_of_le_of_ne (m.degree_sub_leadingTerm_le f) ?_
  simp_intro h'
  apply m.degree_mem_support at h
  rw [h', mem_support_iff] at h
  simp [leadingTerm, leadingCoeff] at h

-- submitted: https://github.com/leanprover-community/mathlib4/pull/26039
variable {m} in
lemma degree_sub_leadingTerm_lt_degree {f : MvPolynomial σ R} (h : f - m.leadingTerm f ≠ 0) :
    m.degree (f - m.leadingTerm f) ≺[m] m.degree f :=
  (or_iff_left h).mp <| m.degree_sub_leadingTerm f

-- submitted: https://github.com/leanprover-community/mathlib4/pull/26039
lemma degree_sub_leadingTerm_lt_iff {f : MvPolynomial σ R} :
    m.degree (f - m.leadingTerm f) ≺[m] m.degree f ↔ m.degree f ≠ 0 := by
  constructor
  · intro h h'
    simp [h'] at h
    exact not_lt_bot h
  · intro h
    by_cases hl : f - m.leadingTerm f = 0
    · simpa [hl, toSyn_lt_iff_ne_zero]
    · exact m.degree_sub_leadingTerm_lt_degree hl

-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
lemma degree_sPolynomial_le (f g : MvPolynomial σ R) :
    ((m.degree <| m.sPolynomial f g) ≼[m] m.degree f ⊔ m.degree g) := by
  classical
  by_cases hf_zero: f = 0
  · simp [hf_zero]
  by_cases hg_zero: g = 0
  · simp [hg_zero]
  simp [sPolynomial_def]
  calc
    _ ≤ _ ⊔ _ := degree_sub_le
    _ ≤  m.toSyn (m.degree _ + m.degree _) ⊔ m.toSyn (m.degree _ + m.degree _) :=
      sup_le_sup degree_mul_le degree_mul_le
    _ ≤ (m.toSyn <| m.degree f ⊔ m.degree g - m.degree f + m.degree f) ⊔
          (m.toSyn <| m.degree f ⊔ m.degree g - m.degree g + m.degree g) := by
      simp_rw [degree_monomial]
      simp [hg_zero, hf_zero]
    _ ≤ m.toSyn (m.degree f ⊔ m.degree g) := by
      simp
      constructor
      all_goals
        apply le_of_eq
        simp_rw [← AddEquiv.map_add, (AddEquiv.injective m.toSyn).eq_iff, Finsupp.ext_iff]
        intro a
        exact Nat.sub_add_cancel <| by simp

-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
lemma coeff_sPolynomial_sup_eq_zero (f g : MvPolynomial σ R) :
    (m.sPolynomial f g).coeff (m.degree f ⊔ m.degree g) = 0 := by
  by_cases hf0 : f = 0
  · simp [hf0]
  by_cases hg0 : g = 0
  · simp [hg0]
  classical
  rw [sPolynomial_def, coeff_sub]
  have : m.degree f ⊔ m.degree g = m.degree f ⊔ m.degree g - m.degree f + m.degree f := by
    rw [Finsupp.ext_iff]
    exact fun _ ↦ (Nat.sub_add_cancel <| by simp).symm
  nth_rewrite 1 [this, coeff_monomial_mul]
  have : m.degree f ⊔ m.degree g = m.degree f ⊔ m.degree g - m.degree g + m.degree g := by
    rw [Finsupp.ext_iff]
    exact fun _ ↦ (Nat.sub_add_cancel <| by simp).symm
  nth_rewrite 1 [this, coeff_monomial_mul]
  unfold leadingCoeff
  ring

-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
lemma degree_sPolynomial (f g : MvPolynomial σ R) :
    (m.degree <| m.sPolynomial f g) ≺[m] m.degree f ⊔ m.degree g ∨ m.sPolynomial f g = 0 := by
  classical
  by_cases hf : m.degree f = 0 ∧ m.degree g = 0
  · rcases hf with ⟨h₁, h₂⟩
    right
    simp [sPolynomial_def, h₁, h₂]
    nth_rewrite 1 [degree_eq_zero_iff.mp h₁]
    nth_rewrite 2 [degree_eq_zero_iff.mp h₂]
    ring
  · by_cases hs: m.sPolynomial f g = 0
    · simp [hs]
    by_cases hf_zero: f = 0
    · simp [hf_zero]
    by_cases hg_zero: g = 0
    · simp [hg_zero]
    left
    have h1: m.toSyn (m.degree (m.sPolynomial f g)) ≤  m.toSyn (m.degree f ⊔ m.degree g) :=
      degree_sPolynomial_le m f g
    have h3: m.toSyn (m.degree (m.sPolynomial f g)) ≠ m.toSyn (m.degree f ⊔ m.degree g) := by
      simp
      by_contra h
      have: coeff (m.degree (m.sPolynomial f g)) (m.sPolynomial f g) ≠ 0 :=
        coeff_degree_ne_zero_iff.mpr hs
      rw [h] at this
      exact this (m.coeff_sPolynomial_sup_eq_zero _ _)
    exact lt_of_le_of_ne h1 h3

-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
variable {m} in
lemma degree_sPolynomial_lt_sup_degree {f g : MvPolynomial σ R} (h : m.sPolynomial f g ≠ 0) :
    (m.degree <| m.sPolynomial f g) ≺[m] m.degree f ⊔ m.degree g :=
  (or_iff_left h).mp <| m.degree_sPolynomial f g

/--
$h_1, h_2 \in k[\mathbf{x}], lm(h_1) = lm(h_2), S(h_1, h_2) \ne 0$, then
$lm(S(h_1, h_2)) < lm(h_1)$.
-/
-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
lemma sPolynomial_lt_of_degree_ne_zero_of_degree_eq {f g : MvPolynomial σ R}
    (h : m.degree f = m.degree g) (hs : m.sPolynomial f g ≠ 0) :
    m.degree (m.sPolynomial f g) ≺[m] m.degree f := by
  convert m.degree_sPolynomial f g
  simp [h, hs]

/-- Monomial degree of product -/
@[simp]
lemma degree_mul' [NoZeroDivisors R] {f g : MvPolynomial σ R} (hf : f * g ≠ 0) :
    m.degree (f * g) = m.degree f + m.degree g := by
  rw [mul_ne_zero_iff] at hf
  exact m.degree_mul hf.1 hf.2

lemma notMem_support_of_degree_lt {f g : MvPolynomial σ R} (h : m.degree f ≺[m] m.degree g) :
    m.degree g ∉ f.support := by
  simp [coeff_eq_zero_of_lt h]

-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
lemma sPolynomial_mul_monomial [IsCancelMulZero R] (p₁ p₂ : MvPolynomial σ R) (d₁ d₂ : σ →₀ ℕ)
    (c₁ c₂ : R) :
    m.sPolynomial ((monomial d₁ c₁) * p₁) ((monomial d₂ c₂) * p₂) =
      monomial ((d₁ + m.degree p₁) ⊔ (d₂ + m.degree p₂) - m.degree p₁ ⊔ m.degree p₂) (c₁ * c₂) *
      m.sPolynomial p₁ p₂ := by
  classical
  simp only [sPolynomial_def]
  by_cases hc1 : c₁ = 0
  · by_cases hc2 : c₂ = 0 <;> simp [hc1, hc2]
  by_cases hc2 : c₂ = 0
  · simp [hc2]
  by_cases hp1 : p₁ = 0
  · simp [hp1]
  by_cases hp2 : p₂ = 0
  · simp [hp2]
  have hm1 := (monomial_eq_zero (s:=d₁)).not.mpr hc1
  have hm2 := (monomial_eq_zero (s:=d₂)).not.mpr hc2
  simp_rw [m.degree_mul hm1 hp1, m.degree_mul hm2 hp2,
    mul_sub, ← mul_assoc _ _ p₁, ← mul_assoc _ _ p₂, monomial_mul,
    m.leadingCoeff_mul hm1 hp1, m.leadingCoeff_mul hm2 hp2, m.leadingCoeff_monomial,
    degree_monomial]
  simp [hc1, hc2]
  congr 2
  all_goals
    congr 1
    · congr 1
      simp [Finsupp.ext_iff]
      intro a
      rw [Nat.sub_add_sub_cancel (by rw [Nat.max_le]; simp) (by simp)]
      rw [← Nat.sub_add_comm (by simp)]
      nth_rewrite 3 [add_comm _ <| (m.degree _) a]
      rw [Nat.add_sub_add_right]
    · ring

end CommRing

section Field

variable {k : Type*} [Field k]

/--
Let $k$ be a field, and let $G'' \subseteq k[x_i : i \in \sigma]$ be a set of polynomials.
Then for any $p \in k[x_i : i \in \sigma]$, there exists a generalized remainder $r$ of $p$ upon division by $G''$.
-/
-- submitted: https://github.com/leanprover-community/mathlib4/pull/29203
theorem div_set'' (B : Set (MvPolynomial σ k))
    (p : MvPolynomial σ k) :
    ∃ (r : MvPolynomial σ k), m.IsRemainder p B r := by
  apply div_set'₀
  simp [em']

end Field

end MonomialOrder
-- #min_imports
