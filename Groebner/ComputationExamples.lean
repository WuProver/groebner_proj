import Groebner.ToMathlib.List
import Groebner.Groebner

open MonomialOrder
variable {σ} {R} [CommSemiring R] {m : MonomialOrder σ} (p : MvPolynomial σ R)
namespace MonomialOrder

theorem isRemainder_range_fin {ι : Type*} [Fintype ι] (b : ι → MvPolynomial σ R)
    (r : MvPolynomial σ R) :
      m.IsRemainder p (Set.range b) r ↔
      (∃ g : ι → MvPolynomial σ R,
          p = ∑ i : ι, (b i * g i) + r ∧
          ∀ i : ι, m.withBotDegree (b i) + m.withBotDegree (g i) ≼'[m] m.withBotDegree p) ∧
        ∀ c ∈ r.support, ∀ i : ι, b i ≠ 0 → ¬ (m.degree (b i) ≤ c) := by
  classical
  rw [IsRemainder.isRemainder_range]
  constructor
  · rintro ⟨⟨g, h₁, h₂⟩, h₃⟩
    split_ands
    · use g
      split_ands
      · simp [Finsupp.linearCombination_apply, Finsupp.sum] at h₁
        rw [h₁]
        congr 1
        have : (∑ i : ι, b i * g i) = ∑ x ∈ g.support, b x * g x := by
          refine Eq.symm (Fintype.sum_subset ?_)
          intro _ h
          contrapose! h
          simp [Finsupp.notMem_support_iff.mp h]
        rw [this]
        simp_rw [mul_comm (g _) (b _)]
      · simpa using h₂
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
      · simpa using h₂
    · aesop

set_option linter.unusedSimpArgs false in
example : sorry := by

  have : ({1, 2, 3} : Set Nat) = Set.range (?_ : List Nat).get := by
    simp only [← Set.range_get_nil, ← Set.range_get_singleton, ← Set.range_get_cons_list]
    exact rfl

  have : ({1, 2, 3} : Finset Nat) = Set.range (?_ : List Nat).get := by
    simp only [← List.toFinset_nil, ← List.toFinset_cons, ← List.toFinset_singleton]
    have := Set.range_list_get_eq_toFinset_toSet (α := Nat) [1,2,3]
    have := this.symm
    -- fail if Set.range_list_get_eq_toFinset_toSet is classical. WHY?????????????????
    -- rw [← Set.range_list_get_eq_toFinset_toSet]
    convert (Set.range_list_get_eq_toFinset_toSet _).symm

  sorry

open MvPolynomial MonomialOrder

set_option linter.unusedSimpArgs false in
example :
    lex.IsRemainder (X 0 ^ 2 + X 1 ^ 3 + X 2 ^ 4 + X 3 ^ 5: MvPolynomial (Fin 4) ℚ)
      {X 0, X 1, X 2, X 3} 0 := by
  -- convert set to `Set.image list.get`
  simp only [← Set.range_get_nil, ← Set.range_get_singleton, ← Set.range_get_cons_list]
  -- use index
  rw [isRemainder_range_fin, ← exists_and_right]
  use [X 0, X 1 ^ 2, X 2 ^ 3, X 3 ^ 4].get
  split_ands
  · split_ands
    · simp [Fin.univ_succ, -List.get_eq_getElem, List.get] -- convert sum to add
      try grind-- PIT, we will rely on reflection
  · intro i
    fin_cases i
    all_goals {
      simp [-List.get_eq_getElem, List.get]
      try sorry -- compare degree
    }
  · simp -- here the remainder is 0, whose support set is empty, so `simp` solves it...

set_option linter.unusedSimpArgs false in
example :
    lex.IsRemainder (X 0 ^ 2 + X 1 ^ 3 + X 2 ^ 4 + X 3 ^ 5: MvPolynomial (Fin 6) ℚ)
      {X 3, X 4 + X 5} (X 0 ^ 2 + X 1 ^ 3 + X 2 ^ 4) := by
  -- convert set to `Set.image list.get`
  simp only [← Set.range_get_nil, ← Set.range_get_singleton, ← Set.range_get_cons_list]
  -- use index
  rw [isRemainder_range_fin, ← exists_and_right]
  use [X 3 ^ 4, 0].get
  split_ands
  · simp [Fin.univ_succ, -List.get_eq_getElem, List.get] -- convert sum to add
    try grind-- PIT, we will rely on reflection later
  · intro i
    fin_cases i
    all_goals {
      simp [-List.get_eq_getElem, List.get]
      try sorry -- compare degree
    }
  · sorry -- we will rely on reflection
