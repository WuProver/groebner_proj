module

public import Mathlib
public import Groebner.ToMathlib.PropLemma
public import Groebner.ToMathlib.MvPolynomial

open MvPolynomial
namespace MonomialOrder
variable {σ : Type*} {m : MonomialOrder σ}

/- S-polynomial merged:
- https://github.com/leanprover-community/mathlib4/pull/32344,
- https://github.com/leanprover-community/mathlib4/pull/32788. -/

@[expose] public section

section misc

variable {R : Type*} [CommSemiring R] (f g : MvPolynomial σ R)

-- merged: https://github.com/leanprover-community/mathlib4/pull/34765
@[deprecated (since := "2026-08-16")]
alias leadingCoeff_mul' := leadingCoeff_mul

-- merged: https://github.com/leanprover-community/mathlib4/pull/34758
@[deprecated (since := "2026-08-16")]
alias degree_mul_le' := toSyn_degree_mul_le

lemma sPolynomial_decomposition_of_degree_sum_smul_le₀ {R} [CommRing R] {d : m.syn} {ι : Type*}
    {B : Finset ι} {c : ι → R} {g : ι → MvPolynomial σ R}
    (hd : ∀ b ∈ B,
      (m.toSyn <| m.degree <| g b) = d ∧ IsUnit (m.leadingCoeff <| g b) ∨ g b = 0)
    (hfd : (m.toSyn <| m.degree <| ∑ b ∈ B, c b • g b) < d) :
    ∃ (c' : ι → ι → R),
      ∑ b ∈ B, c b • g b = ∑ b₁ ∈ B, ∑ b₂ ∈ B, (c' b₁ b₂) • m.sPolynomial (g b₁) (g b₂) := by
  classical
  classical
  induction B using Finset.induction_on with
  | empty => simp
  | insert b B hb h =>
    by_cases hb0 : g b = 0
    · simp_all
    simp? [Finset.sum_insert hb, hb0] at hfd hd says
      simp only [Finset.sum_insert hb, Finset.mem_insert, forall_eq_or_imp, hb0, or_false] at hfd hd
    obtain ⟨⟨rfl, isunit_gb⟩, hd⟩ := hd
    use fun b₁ b₂ ↦ if b₂ = b then c b₁ * ↑isunit_gb.unit⁻¹ else 0
    simp? [Finset.sum_insert hb, hb] says
      simp only [Finset.sum_insert hb, ite_smul, zero_smul, ↓reduceIte, Finset.sum_ite_eq', hb,
        add_zero, sPolynomial_self, smul_zero, zero_add]
    simp only [m.toSyn.injective.eq_iff] at *
    trans ∑ b' ∈ B, (c b' • g b' - (c b' * m.leadingCoeff (g b') * ↑isunit_gb.unit⁻¹) • g b)
    · suffices (-(∑ i ∈ B, c i * m.leadingCoeff (g i))) = c b * m.leadingCoeff (g b) by
        rw [add_comm, Finset.sum_sub_distrib, sub_eq_add_neg, ← Finset.sum_smul, ← Finset.sum_mul,
          ← neg_smul, ← neg_mul, this, mul_assoc, isunit_gb.mul_val_inv, mul_one]
      rw [← add_eq_zero_iff_neg_eq']
      trans c b * (g b).coeff (m.degree <| g b) + ∑ i ∈ B, c i * (g i).coeff (m.degree <| g b)
      · unfold leadingCoeff
        congr 1
        apply Finset.sum_congr rfl
        intro b' hb'
        rcases hd b' hb' with h | h <;> simp [h]
      · simp_rw [← MvPolynomial.coeff_C_mul, ← smul_eq_C_mul]
        rw [← coeff_sum, ← coeff_add, ← notMem_support_iff]
        exact m.notMem_support_of_degree_lt hfd
    · apply Finset.sum_congr rfl
      intro b' hb'
      rw [sPolynomial]
      obtain (⟨h, -⟩ | h) := hd b' hb'
      · simp [h, ← smul_eq_C_mul, smul_sub, ← mul_smul,
          (mul_assoc ..).trans (congrArg (c b' * ·) isunit_gb.val_inv_mul),
          mul_right_comm (b := m.leadingCoeff (g b'))]
      · simp [h]

lemma sPolynomial_decomposition_of_degree_sum_smul_le {R} [CommRing R] {d : m.syn} {ι : Type*}
    {B : Finset ι} {c : ι → R} {g : ι → MvPolynomial σ R}
    (hB : ∀ b ∈ B, IsUnit (m.leadingCoeff <| g b))
    (hd : ∀ b ∈ B, (m.toSyn <| m.degree <| g b) = d)
    (hfd : (m.toSyn <| m.degree <| ∑ b ∈ B, c b • g b) < d) :
    ∃ (c' : ι → ι → R),
      ∑ b ∈ B, c b • g b = ∑ b₁ ∈ B, ∑ b₂ ∈ B, (c' b₁ b₂) • m.sPolynomial (g b₁) (g b₂) :=
  sPolynomial_decomposition_of_degree_sum_smul_le₀ (fun _ h ↦ Or.intro_left _ ⟨hd _ h, hB _ h⟩) hfd

lemma sPolynomial_decomposition_of_degree_sum_le {R} [CommRing R] {d : m.syn} {ι : Type*}
    {B : Finset ι} {g : ι → MvPolynomial σ R}
    (hd : ∀ b ∈ B,
      (m.toSyn <| m.degree <| g b) = d ∧ IsUnit (m.leadingCoeff <| g b) ∨ g b = 0)
    (hfd : (m.toSyn <| m.degree <| ∑ b ∈ B, g b) < d) :
    ∃ (c : ι → ι → R),
      ∑ b ∈ B, g b = ∑ b₁ ∈ B, ∑ b₂ ∈ B, (c b₁ b₂) • m.sPolynomial (g b₁) (g b₂) := by
  simpa using
    sPolynomial_decomposition_of_degree_sum_smul_le₀ (c := fun _ ↦ 1) hd (by simpa using hfd)

lemma sPolynomial_monomial_mul_of_mem_nonZeroDivisors {R} [CommRing R]
    {p₁ p₂ : MvPolynomial σ R}
    (hp₁ : m.leadingCoeff p₁ ∈ nonZeroDivisors _)
    (hp₂ : m.leadingCoeff p₂ ∈ nonZeroDivisors _)
    (d₁ d₂ : σ →₀ ℕ)
    (c₁ c₂ : R) :
    m.sPolynomial ((monomial d₁ c₁) * p₁) ((monomial d₂ c₂) * p₂) =
      monomial ((d₁ + m.degree p₁) ⊔ (d₂ + m.degree p₂) - m.degree p₁ ⊔ m.degree p₂) (c₁ * c₂) *
      m.sPolynomial p₁ p₂ := by
  classical
  simp only [sPolynomial_def]
  wlog! +distrib H : c₁ ≠ 0 ∧ c₂ ≠ 0
  · (obtain rfl | rfl := H) <;> simp
  rcases H with ⟨hc1, hc2⟩
  have hm1 := (monomial_eq_zero (s := d₁)).not.mpr hc1
  have hm2 := (monomial_eq_zero (s := d₂)).not.mpr hc2
  simp_rw [m.degree_mul_of_right_mem_nonZeroDivisors hm1 hp₁,
    m.degree_mul_of_right_mem_nonZeroDivisors hm2 hp₂,
    mul_sub, ← mul_assoc _ _ p₁, ← mul_assoc _ _ p₂, monomial_mul_monomial,
    m.leadingCoeff_mul_of_right_mem_nonZeroDivisors hp₁,
    m.leadingCoeff_mul_of_right_mem_nonZeroDivisors hp₂,
    m.leadingCoeff_monomial, degree_monomial, hc1, hc2, reduceIte, mul_right_comm, mul_comm c₂ c₁]
  rw [tsub_add_tsub_cancel (sup_le_sup (self_le_add_left _ _) (self_le_add_left _ _)) (by simp),
    tsub_add_tsub_cancel (sup_le_sup (self_le_add_left _ _) (self_le_add_left _ _)) (by simp),
    tsub_add_eq_add_tsub le_sup_left, tsub_add_eq_add_tsub le_sup_right,
    add_comm d₁, add_comm d₂, add_tsub_add_eq_tsub_right, add_tsub_add_eq_tsub_right]

lemma sPolynomial_monomial_mul_of_mem_nonZeroDivisors' {R} [CommRing R]
    {p₁ p₂ : MvPolynomial σ R}
    (hp₁ : m.leadingCoeff p₁ ∈ nonZeroDivisors _)
    (hp₂ : m.leadingCoeff p₂ ∈ nonZeroDivisors _)
    (d₁ d₂ : σ →₀ ℕ)
    (c₁ c₂ : R) :
    m.sPolynomial (monomial d₁ c₁ * p₁) (monomial d₂ c₂ * p₂) =
      monomial (m.degree (monomial d₁ c₁ * p₁) ⊔ m.degree (monomial d₂ c₂ * p₂) -
          m.degree p₁ ⊔ m.degree p₂) (c₁ * c₂) *
      m.sPolynomial p₁ p₂ := by
  classical
  wlog! +distrib H : c₁ ≠ 0 ∧ c₂ ≠ 0
  · (obtain rfl | rfl := H) <;> simp
  simp [H, hp₁, hp₂, degree_mul_of_right_mem_nonZeroDivisors,
    sPolynomial_monomial_mul_of_mem_nonZeroDivisors, degree_monomial]


lemma leadingCoeff_mul_of_left_mem_nonZeroDivisors' {f g : MvPolynomial σ R}
    (hf : m.leadingCoeff f ∈ nonZeroDivisors _) :
    m.leadingCoeff (f * g) = m.leadingCoeff f * m.leadingCoeff g := by
  by_cases hg : g = 0
  · simp [hg]
  simp only [leadingCoeff, degree_mul_of_left_mem_nonZeroDivisors hf hg, coeff_mul_of_degree_add]

lemma leadingCoeff_mul_of_right_mem_nonZeroDivisors' {f g : MvPolynomial σ R}
    (hg : m.leadingCoeff g ∈ nonZeroDivisors _) :
    m.leadingCoeff (f * g) = m.leadingCoeff f * m.leadingCoeff g := by
  by_cases hf : f = 0
  · simp [hf]
  simp only [leadingCoeff, degree_mul_of_right_mem_nonZeroDivisors hf hg, coeff_mul_of_degree_add]

lemma support_add_of_leadingTerm_add_leadingTerm_eq_zero
    {p q : MvPolynomial σ R}
    (h : m.leadingTerm p + m.leadingTerm q = 0) :
    ∀ a ∈ (p + q).support,
      (a ∈ p.support ∧ a ≺[m] m.degree p) ∨
      (a ∈ q.support ∧ a ≺[m] m.degree q) := by
  classical
  intro a ha
  wlog! +distrib hpq : p ≠ 0 ∧ q ≠ 0
  · rcases hpq with h' | h'
    · simp [h'] at h
      simp [h, h'] at ha
    · simp [h'] at h
      simp [h, h'] at ha
  unfold leadingTerm at h
  by_cases! hpq' : m.degree p ≠ m.degree q
  · apply congrArg (coeff (m.degree q)) at h
    simp [hpq', hpq] at h
  rw [hpq', ← map_add, monomial_eq_zero] at h
  unfold leadingCoeff at h
  rcases Finset.mem_union.mp <| support_add (p := p) (q := q) ha with h' | h'
  on_goal 1 => left
  on_goal 2 => right
  all_goals
    exists h'
    apply lt_of_le_of_ne (m.le_degree_of_mem_support h')
    by_contra!
    rw [m.toSyn.apply_eq_iff_eq] at this
    subst this
    simp [hpq' ▸ h, hpq'] at ha

@[simp]
lemma leadingTerm_neg {R} [CommRing R] (p : MvPolynomial σ R) :
    m.leadingTerm (-p) = - m.leadingTerm p := by
  simp [leadingTerm]

lemma support_sub_of_leadingTerm_eq_leadingTerm {R} [CommRing R]
    {p q : MvPolynomial σ R}
    (h : m.leadingTerm p = m.leadingTerm q) :
    ∀ a ∈ (p - q).support,
      (a ∈ p.support ∧ a ≺[m] m.degree p) ∨
      (a ∈ q.support ∧ a ≺[m] m.degree q) := by
  classical
  convert m.support_add_of_leadingTerm_add_leadingTerm_eq_zero (p := p) (q := -q) ?_
  · simp [-MvPolynomial.mem_support_iff, ← sub_eq_add_neg, degree_neg, support_neg]
  simp [h]

end misc

section killCompl

lemma degree_rename_killCompl_le_degree {σ' R : Type*} [CommSemiring R]
    {f : σ' → σ} (hf : f.Injective) {p : MvPolynomial σ R} :
    m.degree ((p.killCompl hf).rename f) ≼[m] m.degree p :=
  m.degree_le_degree_of_support_subset (support_rename_killCompl_subset hf)

end killCompl

section WithBotDegree

section Semiring

variable {R : Type*} [CommSemiring R] (f g : MvPolynomial σ R)

@[deprecated (since := "2026-08-16")]
alias withBotDegree_mul_le' := toWithBotSyn_withBotDegree_mul_le

lemma withBotDegree_le_withBotDegree_iff' :
    m.withBotDegree f ≤ m.withBotDegree g ↔
      (m.degree f ≤ m.degree g ∧ (g = 0 → f = 0)) := by
  classical
  wlog! +distrib h : f ≠ 0 ∧ g ≠ 0
  · rcases h with h | h
    · simp [h]
    · simp_rw [h]
      aesop
  simp [m.withBotDegree_eq, h]

lemma withBotDegree_rename_killCompl_le_withBotDegree {σ'} {f : σ' → σ}
    (hf : f.Injective) (p : MvPolynomial σ R) :
    m.withBotDegree ((p.killCompl hf).rename f) ≼'[m] m.withBotDegree p :=
  m.withBotDegree_le_withBotDegree_of_support_subset (support_rename_killCompl_subset hf)

end Semiring

end WithBotDegree

end

end MonomialOrder
