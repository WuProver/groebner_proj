/-
Copyright (c) 2025 Junyu Guo and Hao Shen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyu Guo, Hao Shen
-/
module

public import Mathlib
public import Groebner.MonomialOrder
public import Groebner.MonomialOrderEmbedding
public import Groebner.ToMathlib.Finsupp
public import Groebner.Ideal

/-! # Remainder

The following definition is abstracted from the "remainder" as in `MonomialOrder.div_set`. And more
properties of it is covered in this file.

* `MonomialOrder.IsRemainder m f B r`: Given a multivariate polynomial `f` and a "divisors" set `B`
  of with respect to a monomial order `m`. A polynomial `r` is called a remainder of `f` on
  division by `B` if there exists:

  1. Finite linear combination:
    `f = ∑ (g(b) * b) + r`;
  2. Degree condition:
     For each `b ∈ B`, the degree (with bot) of `g(b) * b` ≤ the degree (with bot) of `f` w.r.t.
     monomial order `m`;
  3. Remainder irreducibility:
    No term of `r` is divisible by the leading monomial of any non-zero `b ∈ B`.

And there're also some equivalent variants.

* `MonomialOrder.IsRemainder.isRemainder_def'`: A variant of `MonomialOrder.IsRemainder`
  without coercion of a `Set (MvPolynomial σ R)`.

* `MonomialOrder.IsRemainder.isRemainder_def''`: A variant of `MonomialOrder.IsRemainder` where
  `g : MvPolynomial σ R →₀ MvPolynomial σ R` is replaced with a
  function `g : MvPolynomial σ R → MvPolynomial σ R` without limitation on its support.

* `MonomialOrder.IsRemainder.isRemainder_iff_degree`: A variant where the degree condition is
  formalized with `m.degree`, which matches the statement of `MonomialOrder.div_set`.

* `MonomialOrder.IsRemainder.isRemainder_range`: A variant of `MonomialOrder.IsRemainder` where
  divisors are given as a family of polynomials.

There exists a remainder when the polynomial ring is communitive and any divisor either has an
invertible leading coefficient or is 0.

* `MonomialOrder.IsRemainder.exists_isRemainder`.

## Naming convention

Some theorems with an argument in type `Set (MvPolynomial σ R)` and a hypothesis that leading
coefficients of all polynomials in the set are invertible have 2 variants, named as following
respectively:

* without suffix `'` or `₀`: any polynomial `b` in the set has an invertible leading coefficient
  (`IsUnit (m.leadingCoeff p)`);
* with suffix `₀`: any polynomial `b` in the set either has an invertible leading coefficient or is
  equal to 0 (`IsUnit (m.leadingCoeff p) ∨ b = 0`);
* with suffix `'`: no hypotheses on leading coefficients, while requiring `R` to be a field
  (`Field k`, where the ring is denoted as `k` instead).

## Implementation notes

The definition of remainder makes sense when `R` is a communitive ring and any polynomial in `B`
either has an invertible leading coefficient or is 0, while for simplicity we try to formalize
it without applying these restrictions as its hypotheses.

We try to adjust its formal definition s.t. it corresponds with the informal definition well when
the above condition holds, while keeps simple and still shares some common properties without these
hypotheses.

* Degree condition is formalized as
  ```lean
  m.toWithBotSyn (m.withBotDegree b.val) + m.toWithBotSyn (m.withBotDegree (g b)) ≤
    m.toWithBotSyn (m.withBotDegree f)
  ```
  instead of `m.withBotDegree (b.val * g b) ≼'[m] m.withBotDegree f`.

  If `IsRemainder` was formalized with the latter one, some properties would require polynomials in
  `B` to have non-zero divisor leading coefficients since they need
  `m.withBotDegree (b.val * g b) = m.withBotDegree (b.val) + m.withBotDegree (g b)` with this
  formalization of `IsRemainder`. They no longer require this if `IsRemainder` is formalized with
  former one.

* Remainder irreducibility is formalized as `∀ c ∈ r.support, ∀ b ∈ B, b ≠ 0 → ¬ (m.degree b ≤ c)`,
  where `¬ (m.degree b ≤ c)` is sufficient but unnecessary for the indivisibility between the
  leading term of `b` (`m.leadingTerm b`) and the term of `r` with exponents `c`
  (`monomial c (b.coeff c)`).

## Reference : [Cox2015]

-/

@[expose] public section

namespace MonomialOrder

open MvPolynomial

/-- Given a multivariate polynomial `f` and a set `B` of multivariate polynomials over `R`.
A polynomial `r` is called a remainder of `f` on division by `B` with respect to a monomial order
`m`, if there exists `g : B →₀ R[X]` and a polynomial `r` s.t.

1. Finite linear combination:
  `f = ∑ (g(b) * b) + r`;
2. Degree condition:
  For eacho `b ∈ B`, the degree (with bot) of `g(b) * b` ≤ the degree (with bot) of `f` w.r.t. `m`;
3. Remainder irreducibility:
  No term of `r` is divisible by the leading monomial of any non-zero `b ∈ B`.

The definition of remainder makes sense when `R` is a communitive ring and any polynomial in `B`
either has an invertible leading coefficient or is 0. See the implementation note for the
formalization unaligned with the informal definition when not in this case.
-/
def IsRemainder {σ : Type*} (m : MonomialOrder σ) {R : Type*} [CommSemiring R]
    (f : MvPolynomial σ R) (B : Set (MvPolynomial σ R)) (r : MvPolynomial σ R) :=
  (∃ (g : B →₀ MvPolynomial σ R),
    f = Finsupp.linearCombination _ (fun (b : B) ↦ b.val) g + r ∧
    ∀ (b : B),
      m.toWithBotSyn (m.withBotDegree b.val) + m.toWithBotSyn (m.withBotDegree (g b)) ≤
        m.toWithBotSyn (m.withBotDegree f)) ∧
  ∀ c ∈ r.support, ∀ b ∈ B, b ≠ 0 → ¬ (m.degree b ≤ c)

namespace IsRemainder

section CommSemiring
variable {σ : Type*} {m : MonomialOrder σ}

variable {R : Type*} [CommSemiring R]
variable (f p : MvPolynomial σ R) (B : Set (MvPolynomial σ R)) (r : MvPolynomial σ R)

theorem isRemainder_def (p : MvPolynomial σ R) (B : Set (MvPolynomial σ R))
    (r : MvPolynomial σ R) : m.IsRemainder p B r ↔
      (∃ (g : B → MvPolynomial σ R) (B' : Finset B),
        p = B'.sum (fun x => g x * x) + r  ∧
        ∀ b ∈ B',
          m.toWithBotSyn (m.withBotDegree b.val) + m.toWithBotSyn (m.withBotDegree (g b)) ≤
            m.toWithBotSyn (m.withBotDegree p)) ∧
      ∀ c ∈ r.support, ∀ g' ∈ B, g' ≠ 0 → ¬ (m.degree g' ≤ c) := by
  classical
  apply and_congr_left
  rintro -
  constructor
  · intro ⟨g, h₂, h₃⟩
    use g.toFun, g.support
    refine ⟨by rwa [Finsupp.linearCombination_apply, Finsupp.sum] at h₂, ?_⟩
    intro g' hg'
    exact h₃ g'
  · intro ⟨g, B', h₂, h₃⟩
    use Finsupp.onFinset B' (fun b' => if b' ∈ B' then g b' else 0) (by simp_intro ..)
    split_ands
    · rw [Finsupp.linearCombination_apply, Finsupp.sum, h₂, Finsupp.support_onFinset]
      congr 1
      simp? [Finset.filter_and, Finset.filter_mem_eq_inter, Finset.inter_self, Finset.inter_filter,
          Finset.filter_inter] says
        simp only [ne_eq, ite_eq_right_iff, Classical.not_imp, Finset.filter_and,
          Finset.filter_mem_eq_inter, Finset.inter_self, Finset.inter_filter,
          Finsupp.onFinset_apply, smul_eq_mul, ite_mul, zero_mul, Finset.sum_ite_mem,
          Finset.filter_inter]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro b' _
      by_cases hb' : g b' = 0 <;> simp [hb']
    · intro b
      by_cases hbB' : b ∈ B' <;> simp [hbB', h₃]

/--
A variant of `MonomialOrder.IsRemainder` without coercion of a `Set (MvPolynomial σ R)`.
-/
theorem isRemainder_def' (p : MvPolynomial σ R) (B : Set (MvPolynomial σ R))
    (r : MvPolynomial σ R) : m.IsRemainder p B r ↔
      (∃ (g : MvPolynomial σ R →₀ MvPolynomial σ R),
        ↑g.support ⊆ B ∧
        p = Finsupp.linearCombination _ id g + r ∧
        ∀ b ∈ B,
          m.toWithBotSyn (m.withBotDegree b) + m.toWithBotSyn (m.withBotDegree (g b)) ≤
            m.toWithBotSyn (m.withBotDegree p)) ∧
      ∀ c ∈ r.support, ∀ g' ∈ B, g' ≠ 0 → ¬ (m.degree g' ≤ c) := by
  apply and_congr_left'
  rw [Function.Surjective.exists (Finsupp.restrictSupportEquiv B (MvPolynomial σ R)).surjective]
  conv in Finsupp.linearCombination _ _ _ =>
    -- simp? [Finsupp.linearCombination,
    --   Finsupp.sum_subtypeDomain_index (p := (· ∈ B)) (h := fun a b ↦ b * a) x.2] says
    simp only [Finsupp.linearCombination, Finsupp.restrictSupportEquiv_apply, Finsupp.coe_lsum,
      LinearMap.coe_smulRight, LinearMap.id_coe, id_eq, smul_eq_mul,
      Finsupp.sum_subtypeDomain_index (p := (· ∈ B)) (h := fun a b ↦ b * a) x.2]
  simp [Subtype.exists, exists_prop, -exists_and_left, and_assoc, Finsupp.linearCombination]

/--
A variant of `MonomialOrder.IsRemainder` where `g : MvPolynomial σ R →₀ MvPolynomial σ R` is
replaced with a function `g : MvPolynomial σ R → MvPolynomial σ R` without limitation on its
support.
-/
theorem isRemainder_def'' (p : MvPolynomial σ R) (B : Set (MvPolynomial σ R))
    (r : MvPolynomial σ R) :
    m.IsRemainder p B r ↔
      (∃ (g : MvPolynomial σ R → MvPolynomial σ R) (B' : Finset (MvPolynomial σ R)),
        ↑B' ⊆ B ∧
        p = B'.sum (fun x => g x * x) + r ∧
        ∀ b' ∈ B',
          m.toWithBotSyn (m.withBotDegree (b' : MvPolynomial σ R)) +
          m.toWithBotSyn (m.withBotDegree (g b')) ≤
            m.toWithBotSyn (m.withBotDegree p)) ∧
      ∀ c ∈ r.support, ∀ b ∈ B, b ≠ 0 → ¬ (m.degree b ≤ c) := by
  classical
  rw [isRemainder_def']
  apply and_congr_left
  rintro -
  constructor
  · intro ⟨g, h₁, h₂, h₃⟩
    use g.toFun, g.support
    refine ⟨h₁, by rwa [Finsupp.linearCombination_apply, Finsupp.sum] at h₂, ?_⟩
    intro g' hg'
    exact h₃ g' (Set.mem_of_mem_of_subset hg' h₁)
  · intro ⟨g, B', h₁, h₂, h₃⟩
    use Finsupp.onFinset B' (fun b' => if b' ∈ B' then g b' else 0) (by simp_intro ..)
    split_ands
    · simp_intro b' hb'
      exact Set.mem_of_mem_of_subset hb'.1 h₁
    · rw [Finsupp.linearCombination_apply, Finsupp.sum, h₂, Finsupp.support_onFinset]
      congr 1
      simp? [Finset.filter_and, Finset.filter_mem_eq_inter, Finset.inter_self, Finset.inter_filter,
          Finset.filter_inter] says
        simp only [ne_eq, ite_eq_right_iff, Classical.not_imp, Finset.filter_and,
          Finset.filter_mem_eq_inter, Finset.inter_self, Finset.inter_filter,
          Finsupp.onFinset_apply, id_eq, smul_eq_mul, ite_mul, zero_mul, Finset.sum_ite_mem,
          Finset.filter_inter]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro b' _
      by_cases hb' : g b' = 0 <;> simp [hb']
    · intro b hb
      by_cases hbB' : b ∈ B' <;> simp [hbB', h₃]

/--
A variant of `MonomialOrder.IsRemainder_def'` where `B` is `Finset (MvPolynomial σ R)`.
-/
theorem isRemainder_finset (p : MvPolynomial σ R) (B' : Finset (MvPolynomial σ R))
    (r : MvPolynomial σ R) : m.IsRemainder p B' r ↔
      (∃ (g : MvPolynomial σ R → MvPolynomial σ R),
        p = B'.sum (fun x => g x * x) + r ∧
        ∀ b' ∈ B',
          m.toWithBotSyn (m.withBotDegree (b' : MvPolynomial σ R)) +
          m.toWithBotSyn (m.withBotDegree (g b')) ≤
            m.toWithBotSyn (m.withBotDegree p)) ∧
      ∀ c ∈ r.support, ∀ b ∈ B', b ≠ 0 → ¬ (m.degree b ≤ c) := by
  classical
  constructor
  · rw [isRemainder_def']
    intro ⟨⟨g, hgsup, hsum, hg⟩, hr⟩
    refine ⟨?_, hr⟩
    use g.toFun
    refine ⟨?_, hg⟩
    simp? [Finsupp.linearCombination_apply, Finsupp.sum]  at hsum says
      simp only [Finsupp.linearCombination_apply, Finsupp.sum, id_eq, smul_eq_mul] at hsum
    rw [hsum]
    congr 1
    apply Finset.sum_subset hgsup
    simp_intro ..
  · rw [isRemainder_def'']
    intro ⟨⟨g, hsum, hg⟩, hr⟩
    refine ⟨?_, hr⟩
    use fun b' ↦ if b' ∈ B' then g b' else 0
    use B'
    split_ands
    · rfl
    · simp [hsum]
    · simp_intro .. [hg]

theorem isRemainder_iff_exists_isRemainder_finset (p : MvPolynomial σ R)
    (B : Set (MvPolynomial σ R)) (r : MvPolynomial σ R) :
    m.IsRemainder p B r ↔
      (∃ (B' : Finset (MvPolynomial σ R)), ↑B' ⊆ B ∧ m.IsRemainder p B' r) ∧
        ∀ c ∈ r.support, ∀ b ∈ B, b ≠ 0 → ¬ (m.degree b ≤ c) := by
  simp_rw [isRemainder_def'' (B := B), isRemainder_finset]
  constructor
  · rintro ⟨⟨g, B', hB'B, hsum, hdeg⟩, hdeg'⟩
    refine ⟨⟨↑B', hB'B, ?_⟩ , hdeg'⟩
    refine ⟨⟨g, hsum, hdeg⟩, fun _ h _ hb ↦ hdeg' _ h _ (hB'B hb)⟩
  · rintro ⟨⟨B', hB'B, ⟨⟨g, hsum, hdeg⟩, -⟩⟩, hdeg'⟩
    exact ⟨⟨g, B', hB'B, hsum, hdeg⟩, hdeg'⟩

/-- `r` is a remainder of a family of polynomials, if and only if it is a remainder with properities
defined in `MonomialOrder.div` with this family of polynomials given as a map from indexes to them.

It is a variant of `MonomialOrder.IsRemainder` where divisors are given as a map from indexes to
polynomials. -/
theorem isRemainder_range {ι : Type*} (f : MvPolynomial σ R)
    (b : ι → MvPolynomial σ R) (r : MvPolynomial σ R) :
    m.IsRemainder f (Set.range b) r ↔
      (∃ g : ι →₀ MvPolynomial σ R,
        f = Finsupp.linearCombination _ b g + r ∧
        ∀ i : ι,
          m.toWithBotSyn (m.withBotDegree (b i : MvPolynomial σ R)) +
          m.toWithBotSyn (m.withBotDegree (g i)) ≤
            m.toWithBotSyn (m.withBotDegree f)) ∧
      ∀ c ∈ r.support, ∀ i : ι, b i ≠ 0 → ¬ (m.degree (b i) ≤ c) := by
  classical
  constructor
  · rintro ⟨⟨g, h₁, h₂⟩, h₃⟩
    let idx : Set.range b ↪ ι := {
      toFun := Set.rangeSplitting b,
      inj' := Set.rangeSplitting_injective b
    }
    split_ands
    · use Finsupp.embDomain idx g
      split_ands
      · simp [h₁, idx]
      · intro i
        specialize h₂ ⟨b i, Set.mem_range_self i⟩
        wlog! h' : (Finsupp.embDomain idx g) i ≠ 0
        · simp [h']
        convert h₂
        generalize_proofs hbi
        rw [Finsupp.embDomain_apply, Ne.dite_ne_right_iff fun h ↦ by simpa [h] using h'] at h'
        rw [Finsupp.embDomain_apply, dite_cond_eq_true (by simp [h'])]
        generalize_proofs h'
        rw! (occs := [2, 3]) [← h'.choose_spec]
        simp [idx, Set.apply_rangeSplitting]
    · intro i hi b hb
      aesop
  · rintro ⟨⟨g, h₁, h₂⟩, h₃⟩
    constructor
    · letI b'_range : Finset (Set.range b) := g.support.image (Set.rangeFactorization b)
      letI g' (x : Set.range b) : MvPolynomial σ R := (g.support.filter (b · = x)).sum g
      have mem_support (x) (hx : g' x ≠ 0) : x ∈ b'_range := by
        contrapose! hx
        simp? [b'_range, Set.rangeFactorization_eq_iff]  at hx says
          simp only [Finset.mem_image, Finsupp.mem_support_iff, ne_eq,
            Set.rangeFactorization_eq_iff, not_exists, not_and, b'_range] at hx
        apply Finset.sum_eq_zero
        simp? says simp only [Finset.mem_filter, Finsupp.mem_support_iff, ne_eq, and_imp]
        tauto
      use Finsupp.onFinset b'_range g' mem_support
      split_ands
      · simp? [h₁, Finsupp.linearCombination_apply, Finsupp.sum] says
          simp only [h₁, Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul,
            Finsupp.onFinset_apply]
        congr
        rw [eq_comm, Finset.sum_subset (s₂ := b'_range) (by simp) (by simp_intro ..)]
        unfold b'_range g'
        apply Finset.sum_image'
        simp? [Finset.sum_mul] says
          simp only [Finsupp.mem_support_iff, ne_eq, Set.rangeFactorization_coe, Finset.sum_mul,
            Set.rangeFactorization_eq_rangeFactorization_iff]
        intro _ _
        apply Finset.sum_congr rfl
        simp_intro ..
      · intro b1
        rw [Finsupp.onFinset]
        apply le_trans (add_le_add_right m.withBotDegree_sum_le _)
        have := (m.toWithBotSyn (m.withBotDegree b1.val) + ·)
        rw [Finset.comp_sup_eq_sup_comp_of_is_total (m.toWithBotSyn (m.withBotDegree b1.val) + ·)]
        · simp_rw [Finset.sup_le_iff, Finset.mem_filter]
          rintro _ ⟨-, h⟩
          simp [← h, h₂]
        · simp_intro _ _ _ [add_le_add]
        simp
    · aesop

theorem isRemainder_range_fintype {ι : Type*} [Fintype ι] (b : ι → MvPolynomial σ R)
    (r : MvPolynomial σ R) :
      m.IsRemainder p (Set.range b) r ↔
      (∃ g : ι → MvPolynomial σ R,
          p = ∑ i : ι, (b i * g i) + r ∧
          ∀ i : ι,
            m.toWithBotSyn (m.withBotDegree (b i)) + m.toWithBotSyn (m.withBotDegree (g i)) ≤
            m.toWithBotSyn (m.withBotDegree p)) ∧
        ∀ c ∈ r.support, ∀ i : ι, b i ≠ 0 → ¬ (m.degree (b i) ≤ c) := by
  simp [IsRemainder.isRemainder_range,
    Function.Surjective.exists (Finsupp.equivFunOnFinite.surjective),
    Finsupp.linearCombination, Finsupp.sum_fintype, mul_comm]

/--
Remainders are preserved on insertion of the zero polynomial into the set of divisors.
-/
@[simp]
theorem isRemainder_insert_zero_iff_isRemainder (p : MvPolynomial σ R)
    (B : Set (MvPolynomial σ R)) (r : MvPolynomial σ R) :
    m.IsRemainder p (insert 0 B) r ↔ m.IsRemainder p B r := by
  unfold IsRemainder
  convert and_congr_left' ?_
  · aesop
  rw [(Finsupp.comapDomain_surjective (f := (⟨·.val, by simp⟩ : B → ↑(insert 0 B))) ?_).exists]
  on_goal 2 => simp [Function.Injective]
  congr! with g
  on_goal 2 => aesop
  rw [Finsupp.linearCombination_comapDomain, Finsupp.linearCombination_apply, Finsupp.sum]
  convert (g.support.sum_preimage ..).symm
  intro x hx hx'
  simp [or_iff_not_imp_right.mp x.prop (by simpa using hx')]

/--
Remainders are preserved with the zero polynomial removed from the set of divisors.
-/
@[simp]
theorem isRemainder_sdiff_singleton_zero_iff_isRemainder (p : MvPolynomial σ R)
  (B : Set (MvPolynomial σ R)) (r : MvPolynomial σ R) :
  m.IsRemainder p (B \ {0}) r ↔ m.IsRemainder p B r := by
  by_cases h : 0 ∈ B
  · rw [←isRemainder_insert_zero_iff_isRemainder, show insert 0 (B \ {0}) = B by simp [h]]
  · simp [h]

variable {B} in
theorem isRemainder_zero {r : MvPolynomial σ R}
    (h : m.IsRemainder 0 B r) : r = 0 := by
  classical
  unfold IsRemainder at h
  obtain ⟨⟨g, h0sumg, hg⟩, hr⟩ := h
  rw [h0sumg, eq_comm]
  convert zero_add r
  apply Finset.sum_eq_zero (f := fun x ↦ g x * x.val)
  intro x _
  specialize hg x
  simp? at hg says
    simp only [withBotDegree_zero, toWithBotSyn_apply_bot, le_bot_iff, WithBot.add_eq_bot,
      toWithBotSyn_apply_eq_bot_iff, withBotDegree_eq_bot_iff] at hg
  rcases hg with hg | hg <;> simp [hg]

@[simp]
theorem isRemainder_zero_iff :
    m.IsRemainder 0 B r ↔ r = 0 := by
  refine ⟨isRemainder_zero, fun h ↦ ?_⟩
  exact ⟨⟨0, by simp [h]⟩, by simp [h]⟩

theorem isRemainder_iff_degree (hB : ∀ b ∈ B, m.leadingCoeff b ∈ nonZeroDivisors _) :
    m.IsRemainder f B r ↔
    (∃ (g : B →₀ MvPolynomial σ R),
      f = Finsupp.linearCombination _ (fun (b : B) ↦ b.val) g + r ∧
      ∀ (b : B), m.degree (b.val * (g b)) ≼[m] m.degree f) ∧
    ∀ c ∈ r.support, ∀ b ∈ B, b ≠ 0 → ¬ (m.degree b ≤ c) := by
  classical
  wlog! hf : f = 0
  · simp_rw [IsRemainder, ← map_add,
        ← m.withBotDegree_mul_of_left_mem_nonZeroDivisors (hB _ (Subtype.prop _)),
       withBotDegree_le_withBotDegree_iff]
    simp? [hf, -mem_support_iff] says
      simp only [hf, IsEmpty.forall_iff, and_true, Subtype.forall, ne_eq]
  simp_rw [hf, isRemainder_zero_iff]
  constructor
  · intro h
    exact ⟨⟨0, by simp [h]⟩, by simp [h]⟩
  rintro ⟨⟨g, h0sumg, hg⟩, hr⟩
  simp_rw [m.degree_zero, m.toSyn.map_zero, ← m.eq_zero_iff, AddEquiv.map_eq_zero_iff,
    mul_comm _ (g _)] at hg
  simp_rw [Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul] at h0sumg
  have h_deg_r_eq_0 : m.degree r = 0 := by
    apply congrArg m.degree at h0sumg
    contrapose! h0sumg
    rw [degree_zero, ne_comm, ← AddEquiv.map_ne_zero_iff m.toSyn, ← m.toSyn_lt_iff_ne_zero]
    rw [← AddEquiv.map_ne_zero_iff m.toSyn, ← m.toSyn_lt_iff_ne_zero] at h0sumg
    rwa [degree_add_eq_right_of_lt]
    apply lt_of_le_of_lt m.degree_sum_le
    simpa [hg] using lt_of_le_of_lt Finset.sup_const_le h0sumg
  by_contra! hr0
  suffices ∀ b, g b * b = 0 by simp [this, hr0.symm] at h0sumg
  intro b
  by_contra! hgb
  obtain ⟨h_gb_ne_0, h_b_ne_0⟩ := ne_zero_and_ne_zero_of_mul hgb
  rw [m.degree_eq_zero_iff.mp h_deg_r_eq_0, support_C, ite_cond_eq_false _ _ (by simp [hr0])] at hr
  specialize hr 0 (by simp) b b.2 h_b_ne_0
  specialize hg b
  rw [m.degree_mul_of_right_mem_nonZeroDivisors h_gb_ne_0 (hB b b.2)] at hg
  rw [← hg] at hr
  simp at hr

lemma mem_ideal_of_mem_ideal {B : Set (MvPolynomial σ R)} {r : MvPolynomial σ R}
    {I : Ideal (MvPolynomial σ R)} {p : MvPolynomial σ R}
    (hBI : B ⊆ I) (hpBr : m.IsRemainder p B r) (hr : r ∈ I) :
    p ∈ I := by
  obtain ⟨⟨f, h_eq, h_deg⟩, h_remain⟩ := hpBr
  rw [h_eq]
  refine Ideal.add_mem _ ?_ hr
  rw [Finsupp.linearCombination_apply]
  apply Ideal.sum_mem
  exact fun _ _ ↦ Ideal.mul_mem_left _ _ (Set.mem_of_mem_of_subset (by simp) hBI)

lemma term_notMem_span_span_monomial {p r : MvPolynomial σ R}
    {B : Set (MvPolynomial σ R)} (h : m.IsRemainder p B r) :
    ∀ s ∈ r.support, monomial s (r.coeff s) ∉
      Ideal.span ((fun p ↦ monomial (m.degree p) 1) '' (B \ {0})) := by
  classical
  intro s hs
  rw [← Set.image_image (monomial · 1) _ _, mem_ideal_span_monomial_image]
  simp? [MvPolynomial.mem_support_iff.mp hs] says
    simp only [mem_support_iff, coeff_monomial, ne_eq, ite_eq_right_iff,
      MvPolynomial.mem_support_iff.mp hs, imp_false, Decidable.not_not, Set.mem_image, Set.mem_diff,
      Set.mem_singleton_iff, exists_exists_and_eq_and, forall_eq', not_exists, not_and, and_imp]
  intro b hb
  unfold MonomialOrder.IsRemainder at h
  exact h.2 _ hs b hb

lemma term_notMem_span_leadingTerm {p r : MvPolynomial σ R}
    {B : Set (MvPolynomial σ R)} (h : m.IsRemainder p B r) :
    ∀ s ∈ r.support, monomial s (r.coeff s) ∉ Ideal.span (m.leadingTerm '' B) := by
  classical
  intro s hs
  apply not_imp_not.mpr ((m.span_leadingTerm_le_span_monomial (B := B)) ·)
  exact term_notMem_span_span_monomial h s hs

lemma _root_.MvPolynomial.monomial_notMem_span_monomial {r : MvPolynomial σ R}
    {B : Set (MvPolynomial σ R)}
    (h : ∀ c ∈ r.support, ∀ b ∈ B, ¬ (m.degree b ≤ c)) :
    ∀ s ∈ r.support, monomial s (1 : R) ∉ Ideal.span ((fun p ↦ monomial (m.degree p) 1) '' B) := by
  classical
  wlog! _ : Nontrivial R
  · simp [Subsingleton.eq_zero (α := R)]
  intro s hs
  rw [← Set.image_image (monomial · 1) _ _, mem_ideal_span_monomial_image]
  simpa using h s hs

lemma _root_.MvPolynomial.monomial_notMem_span_leadingTerm {r : MvPolynomial σ R}
    {B : Set (MvPolynomial σ R)}
    (h : ∀ c ∈ r.support, ∀ b ∈ B, ¬ (m.degree b ≤ c)) :
    ∀ s ∈ r.support, monomial s 1 ∉ Ideal.span (m.leadingTerm '' B) := by
  classical
  intro s hs
  apply not_imp_not.mpr ((m.span_leadingTerm_le_span_monomial (B := B)) ·)
  apply not_imp_not.mpr (Ideal.span_mono (Set.image_mono <| Set.diff_subset (t := {0})) ·)
  exact monomial_notMem_span_monomial h s hs

variable {f r B} in
lemma withBotDegree_remainder_le (h : m.IsRemainder f B r) :
    m.withBotDegree r ≼'[m] m.withBotDegree f := by
  wlog! hf : f ≠ 0
  · -- simp [hf, isRemainder_zero_iff] at h; simp [hf, h] -- "flexible" linter doesn't work here?
    simp [hf, isRemainder_zero_iff .. |>.mp <| hf ▸ h]
  wlog! hr : r ≠ 0
  · simp [hr]
  obtain ⟨g, hsum, h⟩ := h.1
  apply congrArg (m.toWithBotSyn <| m.withBotDegree ·) at hsum
  contrapose! hsum
  apply ne_of_lt
  rw [withBotDegree_add_of_right_lt]
  · exact hsum
  apply lt_of_le_of_lt withBotDegree_sum_le
  rw [Finset.sup_lt_iff (bot_lt_iff_ne_bot.mpr (by simpa))]
  simp? [-mem_support_iff, -Subtype.forall] says
    simp only [Finsupp.mem_support_iff, ne_eq, LinearMap.coe_smulRight, LinearMap.id_coe, id_eq,
      smul_eq_mul]
  rintro b -
  apply lt_of_le_of_lt <| m.withBotDegree_mul_le (g b) b
  simpa [add_comm] using lt_of_le_of_lt (h b) hsum

variable {p B r} in
lemma exists_withBotDegree_le_withBotDegree
    (h : m.IsRemainder p B r) (hfr : m.withBotDegree p ≠ m.withBotDegree r) :
    ∃ b ∈ B, m.withBotDegree b ≤ m.withBotDegree p := by
  classical
  rw [ne_eq, ← m.toWithBotSyn.apply_eq_iff_eq, eq_comm,
    ← ne_eq, ne_iff_lt_iff_le.mpr <| withBotDegree_remainder_le h] at hfr
  wlog! hp : p ≠ 0
  · rw [hp, isRemainder_zero_iff] at h
    simp [h, hp] at hfr
  rw [isRemainder_def''] at h
  rcases h with ⟨⟨g, B', h₁, hsum, h₃⟩, h₄⟩
  have : m.degree p ∈ p.support := m.degree_mem_support hp
  nth_rw 1 [hsum] at this
  apply Finset.mem_of_subset support_add at this
  rw [Finset.mem_union] at this
  rcases this with this | this
  on_goal 2 =>
    apply m.le_withBotDegree at this
    rw [← withBotDegree_eq_coe_degree_iff _ |>.mpr hp, ← not_lt] at this
    contradiction
  obtain ⟨b, hb⟩ := Finset.mem_biUnion.mp <| Finset.mem_of_subset support_sum this
  use b
  refine ⟨h₁ hb.1, ?_⟩
  rcases hb with ⟨hb₁, hb₂⟩
  obtain hgbne0 : g b ≠ 0 := by
    contrapose! hb₂
    simp [hb₂]
  apply le_withBotDegree (m:=m) at hb₂
  rw [← withBotDegree_eq_coe_degree_iff _ |>.mpr hp] at hb₂
  apply le_trans' (m.withBotDegree_mul_le' ..) at hb₂
  rw [add_comm] at hb₂
  apply le_antisymm (add_comm (m.toWithBotSyn <| m.withBotDegree b) _ ▸ h₃ b hb₁) at hb₂
  simp only [← map_add, EmbeddingLike.apply_eq_iff_eq] at hb₂
  rw [← hb₂]
  exact WithBot.le_self_add (m.withBotDegree_eq_bot_iff _ |>.not.mpr hgbne0) _

variable {p B r} in
lemma exists_withBotDegree_le_withBotDegree₀
    (h : m.IsRemainder p B r) (hfr : m.withBotDegree p ≠ m.withBotDegree r) :
    ∃ b ∈ B, b ≠ 0 ∧ m.withBotDegree b ≤ m.withBotDegree p := by
  rw [← isRemainder_sdiff_singleton_zero_iff_isRemainder] at h
  simpa only [← and_assoc] using h.exists_withBotDegree_le_withBotDegree hfr

variable {p B r} in
lemma withBotDegree_eq_withBotDegree_iff_leadingTerm_eq_leadingTerm (h : m.IsRemainder p B r) :
    m.withBotDegree r = m.withBotDegree p ↔ m.leadingTerm r = m.leadingTerm p := by
  wlog! hB0 : 0 ∉ B
  · apply this (h := isRemainder_sdiff_singleton_zero_iff_isRemainder .. |>.mpr h)
    simp
  wlog! hp : p ≠ 0
  · simp [hp]
  constructor
  on_goal 2 =>
    intro h
    rw [← m.withBotDegree_leadingTerm r, ← m.withBotDegree_leadingTerm p, h]
  intro deg_eq
  have deg_eq' := m.withBotDegree_eq_withBotDegree_iff .. |>.mp deg_eq |>.1
  simp_rw [m.leadingTerm_eq_leadingTerm_iff, leadingCoeff, deg_eq', and_true]
  obtain ⟨⟨g, hg, hg'⟩, h⟩ := h
  nth_rw 3 [hg]
  rw [coeff_add]
  convert eq_comm.mp <| zero_add (coeff (m.degree p) r)
  rw [Finsupp.linearCombination_apply, Finsupp.sum, coeff_sum]
  apply Finset.sum_eq_zero
  rintro g' -
  wlog! hgg' : g g' * g'.val ≠ 0
  · simp [hgg']
  apply m.coeff_eq_zero_of_lt
  rw [smul_eq_mul, ← m.withBotDegree_lt_withBotDegree_iff_of_ne_zero _ _ hgg']
  apply lt_of_le_of_lt (m.withBotDegree_mul_le' ..)
  rw [add_comm]
  apply lt_of_le_of_ne (hg' g')
  specialize h (m.degree r)
    (by simpa [← m.withBotDegree_eq_bot_iff .. |>.not, ← deg_eq, withBotDegree_eq_bot_iff] using hp)
    g' g'.2 (by contrapose! hgg'; simp [hgg'])
  contrapose! h
  rw [← m.toWithBotSyn.map_add, m.toWithBotSyn.apply_eq_iff_eq,
    m.withBotDegree_eq_coe_degree_iff .. |>.mpr hp,
    m.withBotDegree_eq_coe_degree_iff g'.val |>.mpr (by contrapose! hgg'; simp [hgg']),
    m.withBotDegree_eq_coe_degree_iff (g g') |>.mpr (by contrapose! hgg'; simp [hgg']),
    ← WithBot.coe_add, WithBot.coe_eq_coe] at h
  simp [deg_eq', ← h]

variable {p B} in
lemma exists_degree_le_degree_of_zero (hp : p ≠ 0) (h : m.IsRemainder p B 0) :
    ∃ b ∈ B, m.degree b ≤ m.degree p := by
  obtain ⟨b, hbB, hb⟩ := exists_withBotDegree_le_withBotDegree (r := 0) h (by simpa)
  use b, hbB
  wlog! hb0 : b ≠ 0
  · simp [hb0]
  simpa [(withBotDegree_eq_coe_degree_iff _).mpr _, hb0, hp] using hb

@[simp, nontriviality]
lemma of_subsingleton [Subsingleton (MvPolynomial σ R)]
    {p r : MvPolynomial σ R} {s : Set (MvPolynomial σ R)} :
    m.IsRemainder p s r := by
  simp [IsRemainder, Subsingleton.eq_zero (α := MvPolynomial σ R)]

lemma _root_.MonomialOrder.Embedding.isRemainder_killCompl_of_isRemainder_rename
    {σ' σ} {m' : MonomialOrder σ'} {m : MonomialOrder σ}
    (e : Embedding m' m) {p : MvPolynomial σ' R} {B : Set (MvPolynomial σ' R)}
    {r : MvPolynomial σ R} (h : m.IsRemainder (p.rename e) (rename e '' B) r) :
    m'.IsRemainder p B (r.killCompl e.coe_injective) := by
  classical
  rw [isRemainder_def'] at h ⊢
  obtain ⟨⟨g, hg, hsum, hdeg⟩, hdeg'⟩ := h
  constructor
  · use g.mapDomain (killCompl e.coe_injective) |>.mapRange (killCompl e.coe_injective) (by simp)
    split_ands
    · apply subset_trans (SetLike.coe_subset_coe.mpr Finsupp.support_mapRange)
      apply subset_trans (SetLike.coe_subset_coe.mpr Finsupp.mapDomain_support)
      apply Set.image_mono (f := killCompl e.coe_injective) at hg
      simp_rw [← Set.image_comp, ← AlgHom.coe_comp,
        MvPolynomial.killCompl_comp_rename e.coe_injective, AlgHom.coe_id, Set.image_id] at hg
      rwa [Finset.coe_image]
    · apply congrArg (killCompl e.coe_injective) at hsum
      rw [← Function.comp_apply (f := killCompl e.coe_injective), ← AlgHom.coe_comp,
        killCompl_comp_rename, AlgHom.coe_id, id] at hsum
      simp [hsum, Finsupp.linearCombination]
      rw [Finsupp.sum_mapRange_index (by simp), g.sum_mapDomain_index (by simp) (by simp [add_mul]),
        map_finsuppSum]
      simp
    · intro b hb
      specialize hdeg (b.rename e) (Set.mem_image_of_mem _ hb)
      rw [← e.withBotDegree_add_withBotDegree_le_withBotDegree_iff']
      apply le_trans' hdeg
      nth_rw 2 [← b.killCompl_rename_app e.coe_injective]
      rw [Finsupp.mapRange_apply, g.mapDomain_apply' (rename e '' B) hg]
      · apply add_le_add_right
        exact withBotDegree_rename_killCompl_le_withBotDegree ..
      · apply Set.InjOn.image_of_comp
        simp
      · exact Set.mem_image_of_mem _ hb
  intro c hc g' hg' hg'0
  rw [support_killCompl] at hc
  specialize hdeg' (c.mapDomain e) (by simpa using hc) (g'.rename e) (Set.mem_image_of_mem _ hg')
    (by simpa)
  rwa [e.degree_rename, Finsupp.mapDomain_le_mapDomain_iff_le e.coe_injective] at hdeg'

lemma _root_.MonomialOrder.Embedding.isRemainder_rename_of_isRemainder {σ' σ}
    {m' : MonomialOrder σ'} {m : MonomialOrder σ}
    (e : Embedding m' m) {p : MvPolynomial σ' R} {B : Set (MvPolynomial σ' R)}
    {r : MvPolynomial σ' R} (h : m'.IsRemainder p B r) :
    m.IsRemainder (p.rename e) (rename e '' B) (r.rename e) := by
  classical
  rw [isRemainder_def'] at h ⊢
  obtain ⟨⟨g, hg, hsum, hdeg⟩, hdeg'⟩ := h
  constructor
  · use g.mapDomain (rename e) |>.mapRange (rename e) (by simp)
    split_ands
    · apply subset_trans (SetLike.coe_subset_coe.mpr Finsupp.support_mapRange)
      apply subset_trans (SetLike.coe_subset_coe.mpr Finsupp.mapDomain_support)
      rw [Finset.coe_image]
      exact Set.image_mono hg
    · simp [hsum, Finsupp.linearCombination]
      rw [Finsupp.sum_mapRange_index (by simp),
        Finsupp.sum_mapDomain_index_inj <| rename_injective _ e.coe_injective]
      simp_rw [← map_mul, map_finsuppSum]
    · simpa [← map_mul, Finsupp.mapDomain_apply (rename_injective _ e.coe_injective)] using hdeg
  · simpa [e.coe_injective, MvPolynomial.support_rename_of_injective, Embedding.degree_rename,
      Finsupp.mapDomain_le_mapDomain_iff_le] using hdeg'

lemma _root_.MonomialOrder.Embedding.isRemainder_iff_isRemainder_rename {σ' σ}
    {m' : MonomialOrder σ'} {m : MonomialOrder σ}
    (e : Embedding m' m) (p : MvPolynomial σ' R) {B : Set (MvPolynomial σ' R)}
    (r : MvPolynomial σ' R) :
    m'.IsRemainder p B r ↔
      m.IsRemainder (p.rename e) (rename e '' B) (r.rename e) :=
  ⟨e.isRemainder_rename_of_isRemainder,
    (by simpa using e.isRemainder_killCompl_of_isRemainder_rename ·)⟩

end CommSemiring

section CommRing

variable {σ : Type*} {m : MonomialOrder σ} {R : Type*} [CommRing R]

theorem exists_isRemainder {B : Set (MvPolynomial σ R)}
    (hB : ∀ b ∈ B, IsUnit <| m.leadingCoeff b) (p : MvPolynomial σ R) :
    ∃ (r : MvPolynomial σ R), m.IsRemainder p B r := by
  classical
  obtain ⟨g, r, h⟩ := MonomialOrder.div_set hB p
  use r
  rw [isRemainder_iff_degree (hB := fun _ h ↦ (hB _ h).mem_nonZeroDivisors)]
  split_ands
  · use g
    exact ⟨h.1, h.2.1⟩
  · intro c hc b hb _
    exact h.2.2 c hc b hb

/-- A variant of `div_set'` including `0` -/
theorem exists_isRemainder₀ {B : Set (MvPolynomial σ R)}
    (hB : ∀ b ∈ B, (IsUnit (m.leadingCoeff b) ∨ b = 0)) (p : MvPolynomial σ R) :
    ∃ (r : MvPolynomial σ R), m.IsRemainder p B r := by
  have hB₁ : ∀ b ∈ B \ {0}, IsUnit (m.leadingCoeff b) := by
    simp_intro .. [or_iff_not_imp_right.mp (hB _ _)]
  obtain ⟨r, h⟩ := exists_isRemainder hB₁ p
  exists r
  rwa [← isRemainder_sdiff_singleton_zero_iff_isRemainder]

lemma mem_ideal_iff {B : Set (MvPolynomial σ R)}
    {r : MvPolynomial σ R} {I : Ideal (MvPolynomial σ R)} {p : MvPolynomial σ R}
    (hBI : B ⊆ I) (hpBr : m.IsRemainder p B r) : r ∈ I ↔ p ∈ I := by
  refine ⟨mem_ideal_of_mem_ideal hBI hpBr, ?_⟩
  obtain ⟨⟨f, h_eq, h_deg⟩, h_remain⟩ := hpBr
  intro hp
  rw [← sub_eq_of_eq_add' h_eq]
  apply Ideal.sub_mem I hp
  apply Ideal.sum_mem
  exact fun _ _ ↦ Ideal.mul_mem_left I _ (Set.mem_of_mem_of_subset (by simp) hBI)

lemma sub_mem_ideal_of_isRemainder_of_subset_ideal
    {B : Set (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)} {p r₁ r₂ : MvPolynomial σ R}
    (hBI : B ⊆ I) (hr₁ : m.IsRemainder p B r₁) (hr₂ : m.IsRemainder p B r₂) :
    r₁ - r₂ ∈ I := by
  obtain ⟨⟨f₁, h_eq₁, h_deg₁⟩, h_remain₁⟩ := hr₁
  obtain ⟨⟨f₂, h_eq₂, h_deg₂⟩, h_remain₂⟩ := hr₂
  rw [← sub_eq_of_eq_add' h_eq₁, ← sub_eq_of_eq_add' h_eq₂]
  simp? says simp only [sub_sub_sub_cancel_left]
  apply Ideal.sub_mem I
  all_goals
    apply Ideal.sum_mem
    intro g hg
    exact Ideal.mul_mem_left I _ (Set.mem_of_mem_of_subset (by simp) hBI)

lemma sub_monomial_notMem_span_leadingTerm
    {B : Set (MvPolynomial σ R)} {p r₁ r₂ : MvPolynomial σ R}
    (hr₁ : m.IsRemainder p B r₁) (hr₂ : m.IsRemainder p B r₂) :
    ∀ s ∈ (r₁ - r₂).support, monomial s 1 ∉ Ideal.span (m.leadingTerm '' B) := by
  classical
  wlog! hB0 : 0 ∉ B
  · rw [← isRemainder_sdiff_singleton_zero_iff_isRemainder] at hr₁ hr₂
    specialize this hr₁ hr₂ (by simp)
    rwa [← span_leadingTerm_sdiff_singleton_zero]
  apply monomial_notMem_span_leadingTerm
  intro c hc
  apply MvPolynomial.support_sub at hc
  rw [Finset.mem_union] at hc
  rcases hc with hc | hc
  · intro b hb
    exact hr₁.2 c hc b hb (hB0 <| · ▸ hb)
  · intro b hb
    exact hr₂.2 c hc b hb (hB0 <| · ▸ hb)

end CommRing

section Field

variable {k : Type*} [Field k] {σ : Type*} {m : MonomialOrder σ}

/-- A variant of `div_set'` in field -/
theorem exists_isRemainder' (B : Set (MvPolynomial σ k))
    (p : MvPolynomial σ k) :
    ∃ (r : MvPolynomial σ k), m.IsRemainder p B r := by
  apply exists_isRemainder₀
  simp [em']

end Field

end IsRemainder

end MonomialOrder
