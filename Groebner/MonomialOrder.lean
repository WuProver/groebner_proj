module

public import Mathlib
public import Groebner.ToMathlib.AddEquiv
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

-- submitted: https://github.com/leanprover-community/mathlib4/pull/34758
@[simp]
lemma monic_leadingTerm (p : MvPolynomial σ R) :
    m.Monic (m.leadingTerm p) ↔ m.Monic p := by simp [leadingTerm, Monic]

-- submitted: https://github.com/leanprover-community/mathlib4/pull/34758
lemma support_leadingTerm (p : MvPolynomial σ R) [Decidable (p = 0)] :
    support (m.leadingTerm p) = if p = 0 then ∅ else {m.degree p} := by
  classical
  simp [leadingTerm, support_monomial]

-- submitted: https://github.com/leanprover-community/mathlib4/pull/34758
lemma support_leadingTerm' {p : MvPolynomial σ R} (hp : p ≠ 0) :
    support (m.leadingTerm p) = {m.degree p} := by
  classical
  simp [leadingTerm, support_monomial, hp]

-- submitted: https://github.com/leanprover-community/mathlib4/pull/34758
lemma le_degree_of_mem_support {p : MvPolynomial σ R} {a : σ →₀ ℕ}
    (ha : a ∈ p.support) : a ≼[m] m.degree p := by
  simp [degree, Finset.le_sup ha]

-- submitted: https://github.com/leanprover-community/mathlib4/pull/34758
lemma leadingTerm_eq_leadingTerm_iff {p q : MvPolynomial σ R} :
    m.leadingTerm p = m.leadingTerm q ↔
    m.leadingCoeff p = m.leadingCoeff q ∧ m.degree p = m.degree q := by
  rw [leadingTerm, leadingTerm, monomial_eq_monomial_iff]
  aesop

-- submitted: https://github.com/leanprover-community/mathlib4/pull/34758
@[simp]
lemma monic_one' : m.Monic (1 : MvPolynomial σ R) := monic_one

-- submitted: https://github.com/leanprover-community/mathlib4/pull/34758
@[simp, nontriviality]
lemma monic_of_subsingleton [Subsingleton (MvPolynomial σ R)] (p : MvPolynomial σ R) :
    m.Monic p := by
  simp [Subsingleton.eq_one (α := MvPolynomial σ R)]

-- submitted: https://github.com/leanprover-community/mathlib4/pull/34758
lemma degree_le_degree_of_support_subset {p q : MvPolynomial σ R} (h : p.support ⊆ q.support) :
    m.degree p ≼[m] m.degree q := by
  simp_rw [degree, m.toSyn.apply_symm_apply]
  exact Finset.sup_mono h

-- submitted: https://github.com/leanprover-community/mathlib4/pull/34758
theorem degree_mul_le' {f g : MvPolynomial σ R} :
    m.toSyn (m.degree (f * g)) ≤ m.toSyn (m.degree f) + m.toSyn (m.degree g) :=
  map_add m.toSyn _ _ ▸ degree_mul_le

-- submitted: https://github.com/leanprover-community/mathlib4/pull/34758
variable {f} in
lemma mem_nonZeroDivisors_of_leadingCoeff_mem_nonZeroDivisors
    (hf : m.leadingCoeff f ∈ nonZeroDivisors _) : f ∈ nonZeroDivisors _ := by
  rw [← nonZeroDivisorsLeft_eq_nonZeroDivisors, mem_nonZeroDivisorsLeft_iff]
  intro g
  rw [← not_imp_not, ← m.leadingCoeff_eq_zero_iff (f := f * g)]
  intro h
  rwa [m.leadingCoeff_mul_of_left_mem_nonZeroDivisors hf h,
    mul_left_mem_nonZeroDivisors_eq_zero_iff hf, m.leadingCoeff_eq_zero_iff]

-- submitted: https://github.com/leanprover-community/mathlib4/pull/34765
@[simp]
theorem leadingCoeff_mul' [NoZeroDivisors R] {f g : MvPolynomial σ R} :
    m.leadingCoeff (f * g) = m.leadingCoeff f * m.leadingCoeff g := by
  -- improved version of `MonomialOrder.leadingCoeff_mul`
  wlog! +distrib h : f ≠ 0 ∧ g ≠ 0
  · cases h <;> simp [*]
  obtain ⟨hf, hg⟩ := h
  rw [leadingCoeff, degree_mul hf hg, ← coeff_mul_of_degree_add]

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
    mul_sub, ← mul_assoc _ _ p₁, ← mul_assoc _ _ p₂, monomial_mul,
    m.leadingCoeff_mul_of_right_mem_nonZeroDivisors hm1 hp₁,
    m.leadingCoeff_mul_of_right_mem_nonZeroDivisors hm2 hp₂,
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


theorem leadingCoeff_mul_of_left_mem_nonZeroDivisors' {f g : MvPolynomial σ R}
    (hf : m.leadingCoeff f ∈ nonZeroDivisors _) :
    m.leadingCoeff (f * g) = m.leadingCoeff f * m.leadingCoeff g := by
  by_cases hg : g = 0
  · simp [hg]
  simp only [leadingCoeff, degree_mul_of_left_mem_nonZeroDivisors hf hg, coeff_mul_of_degree_add]

theorem leadingCoeff_mul_of_right_mem_nonZeroDivisors' {f g : MvPolynomial σ R}
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

variable (m) in
/-- the degree of a multivariate polynomial with respect to a monomial ordering -/
noncomputable def withBotDegree : WithBot (σ →₀ ℕ) :=
  f.support.image m.toSyn |>.max.map m.toSyn.symm

variable (m) in
noncomputable def toWithBotSyn : WithBot (σ →₀ ℕ) ≃+ WithBot m.syn := m.toSyn.withBotCongr

@[simp]
lemma toWithBotSyn_apply_bot : m.toWithBotSyn ⊥ = ⊥ := rfl

@[simp]
lemma toWithBotSyn_symm_apply_bot : m.toWithBotSyn.symm ⊥ = ⊥ := rfl

@[simp]
lemma toWithBotSyn_apply_eq_bot_iff (a) : m.toWithBotSyn a = ⊥ ↔ a = ⊥ := by
  simp [← m.toWithBotSyn.eq_symm_apply]

@[simp]
lemma toWithBotSyn_apply_le_bot_iff (a) : m.toWithBotSyn a ≤ ⊥ ↔ a = ⊥ := by
  simp [← m.toWithBotSyn.eq_symm_apply]

@[simp]
lemma toWithBotSyn_apply_coe (a : σ →₀ ℕ) : m.toWithBotSyn a = m.toSyn a := rfl

@[simp]
lemma bot_lt_toWithBotSyn_apply_iff (a) : ⊥ < m.toWithBotSyn a ↔ a ≠ ⊥ := by
  simp [bot_lt_iff_ne_bot]

@[simp]
lemma toWithBotSyn_symm_apply_eq_bot (a) : m.toWithBotSyn.symm a = ⊥ ↔ a = ⊥ := by
  simp [m.toWithBotSyn.symm_apply_eq]

lemma toWithBotSyn_apply (a : WithBot (σ →₀ ℕ)) : m.toWithBotSyn a = a.map m.toSyn := rfl

/-- Given a monomial order with bot, notation for the corresponding strict order relation on
`WithBot (σ →₀ ℕ)` -/
scoped
notation:50 c " ≺'[" m:25 "] " d:50 =>
  (MonomialOrder.toWithBotSyn m c < MonomialOrder.toWithBotSyn m d)

/-- Given a monomial order with bot, notation for the corresponding order relation on
`WithBot (σ →₀ ℕ)` -/
scoped
notation:50 c " ≼'[" m:25 "] " d:50 =>
  (MonomialOrder.toWithBotSyn m c ≤ MonomialOrder.toWithBotSyn m d)

lemma withBotDegree_eq [Decidable (f = 0)] :
    m.withBotDegree f = if f = 0 then ⊥ else ↑(m.degree f) := by
  simp [withBotDegree, degree]
  by_cases hf : f = 0
  · simp [hf]
  · simp [hf, Finset.max_eq_sup_coe, ← Finset.coe_sup_of_nonempty _ (⇑m.toSyn)]

@[simp]
lemma withBotDegree_eq_coe_degree_iff : m.withBotDegree f = m.degree f ↔ f ≠ 0 := by
  classical
  simp [withBotDegree_eq]

@[simp]
lemma withBotDegree_eq_bot_iff : m.withBotDegree f = ⊥ ↔ f = 0 := by
  classical
  simp [withBotDegree_eq]

lemma degree_eq_unbotD_withBotDegree : m.degree f = (m.withBotDegree f).unbotD 0 := by
  classical
  by_cases h : f = 0 <;> simp [withBotDegree_eq, h]

@[simp]
lemma withBotDegree_zero : m.withBotDegree (R := R) 0 = ⊥ := rfl

lemma withBotDegree_monomial (d) (c) [Decidable (c = 0)] :
    m.withBotDegree (R := R) (monomial d c) = if c = 0 then ⊥ else ↑d := by
  classical
  split_ifs <;> simp [withBotDegree_eq, *, m.degree_monomial]

lemma withBotDegree_C (c) [Decidable (c = 0)] :
    m.withBotDegree (R := R) (C c) = if c = 0 then ⊥ else 0 := by
  classical
  rw [← monomial_zero', withBotDegree_monomial]
  rfl

@[simp]
lemma withBotDegree_leadingTerm : m.withBotDegree (m.leadingTerm f) = m.withBotDegree f := by
  classical
  simp [withBotDegree_eq]

@[simp]
lemma withBotDegree_neg {R} [CommRing R] (f : MvPolynomial σ R) :
    m.withBotDegree (-f) = m.withBotDegree f := by
  classical
  simp [m.withBotDegree_eq]

@[simp]
lemma withBotDegree_one [Nontrivial R] : m.withBotDegree (R := R) 1 = 0 := by
  classical
  simp [withBotDegree_eq]

variable {f g} in
lemma withBotDegree_mul_of_left_mem_nonZeroDivisors (hf : m.leadingCoeff f ∈ nonZeroDivisors _) :
    m.withBotDegree (f * g) = m.withBotDegree f + m.withBotDegree g := by
  classical
  wlog! +distrib h0 : f ≠ 0 ∧ g ≠ 0
  · rcases h0 with h0 | h0 <;> simp [h0]
  have : f * g ≠ 0 := not_imp_not.mpr
    ((mem_nonZeroDivisors_iff.mp (mem_nonZeroDivisors_of_leadingCoeff_mem_nonZeroDivisors hf)).1 _)
    h0.2
  simp [m.withBotDegree_eq, h0, m.degree_mul_of_left_mem_nonZeroDivisors hf, this]

variable {f g} in
lemma withBotDegree_mul_of_right_mem_nonZeroDivisors (hf : m.leadingCoeff g ∈ nonZeroDivisors _) :
    m.withBotDegree (f * g) = m.withBotDegree f + m.withBotDegree g := by
  rw [mul_comm, add_comm, withBotDegree_mul_of_left_mem_nonZeroDivisors (hf := hf)]

@[simp]
lemma withBotDegree_mul [NoZeroDivisors R] :
    m.withBotDegree (f * g) = m.withBotDegree f + m.withBotDegree g := by
  wlog! trivial : Nontrivial R
  · simp [Subsingleton.eq_zero (α := MvPolynomial σ R)]
  wlog! hf : f ≠ 0
  · simp [hf]
  rw [← m.leadingCoeff_ne_zero_iff] at hf
  exact m.withBotDegree_mul_of_left_mem_nonZeroDivisors (mem_nonZeroDivisors_iff_ne_zero.mpr hf)

lemma withBotDegree_mul_le :
    m.withBotDegree (f * g) ≼'[m] m.withBotDegree f + m.withBotDegree g := by
  wlog! +distrib h0 : f * g ≠ 0
  · simp [h0]
  simp [m.withBotDegree_eq_coe_degree_iff f |>.mpr (by aesop),
    m.withBotDegree_eq_coe_degree_iff g |>.mpr (by aesop),
    m.withBotDegree_eq_coe_degree_iff _ |>.mpr h0, ← WithBot.coe_add,
    ← map_add, -- the warning here is a bug?
    m.degree_mul_le]

lemma withBotDegree_mul_le' :
    m.toWithBotSyn (m.withBotDegree (f * g)) ≤
      m.toWithBotSyn (m.withBotDegree f) + m.toWithBotSyn (m.withBotDegree g) := by
  wlog! +distrib h0 : f * g ≠ 0
  · simp [h0]
  simp [m.withBotDegree_eq_coe_degree_iff f |>.mpr (by aesop),
    m.withBotDegree_eq_coe_degree_iff g |>.mpr (by aesop),
    m.withBotDegree_eq_coe_degree_iff _ |>.mpr h0, ← WithBot.coe_add,
    m.degree_mul_le']

-- lemma le_withBotDegree_iff (a) :
--     a ≤ m.toWithBotSyn (m.withBotDegree g) ↔
--       (a ≤ m.toSyn (m.degree g) ∧ (g = 0 → a = ⊥)) := by
--   classical
--   wlog! +distrib h : a ≠ ⊥ ∧ g ≠ 0
--   · rcases h with h | h
--     · simp [h, m.toWithBotSyn_apply]
--     · simp_rw [m.toWithBotSyn_apply]
--       aesop
--   simp [m.withBotDegree_eq, h, m.toWithBotSyn_apply]

lemma withBotDegree_le_withBotDegree_iff :
    m.withBotDegree f ≼'[m] m.withBotDegree g ↔
      (m.degree f ≼[m] m.degree g ∧ (g = 0 → f = 0)) := by
  classical
  wlog! +distrib h : f ≠ 0 ∧ g ≠ 0
  · rcases h with h | h
    · simp [h, m.toWithBotSyn_apply]
    · simp_rw [m.toWithBotSyn_apply]
      aesop
  simp [m.withBotDegree_eq, h, m.toWithBotSyn_apply]

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

-- lemma le_withBotDegree_iff_of_ne_zero (a) (hg : g ≠ 0) :
--     a ≤ m.toWithBotSyn (m.withBotDegree g) ↔ a.unbotD 0 ≤ m.toSyn (m.degree g) := by
--   rw [le_withBotDegree_iff]
--   wlog! ha : a ≠ ⊥
--   · simp [ha]
--   rw [← a.coe_unbot ha, WithBot.coe_le_coe, WithBot.unbotD_coe]
--   simp [hg, ha]

variable {g} in
lemma withBotDegree_le_withBotDegree_iff_of_ne_zero (hg : g ≠ 0) :
    m.withBotDegree f ≼'[m] m.withBotDegree g ↔ m.degree f ≼[m] m.degree g := by
  simp [withBotDegree_le_withBotDegree_iff, hg]

lemma withBotDegree_lt_withBotDegree_iff :
    m.withBotDegree f ≺'[m] m.withBotDegree g ↔
      (m.degree f ≺[m] m.degree g ∨ (f = 0 ∧ g ≠ 0)) := by
  classical
  by_cases! hg : g = 0
  · simp_rw [toWithBotSyn_apply]
    aesop
  by_cases! hf : f = 0
  · simp [hg, hf, bot_lt_iff_ne_bot, toWithBotSyn_apply]
  simp [m.withBotDegree_eq, hf, hg, m.toWithBotSyn_apply]

lemma withBotDegree_lt_withBotDegree_iff_of_ne_zero (hf : f ≠ 0) :
    m.withBotDegree f ≺'[m] m.withBotDegree g ↔ m.degree f ≺[m] m.degree g := by
  simp [withBotDegree_lt_withBotDegree_iff, hf]

lemma withBotDegree_eq_withBotDegree_iff :
    m.withBotDegree f = m.withBotDegree g ↔ (m.degree f = m.degree g ∧ (f = 0 ↔ g = 0)) := by
  classical
  wlog! +distrib h : f ≠ 0 ∧ g ≠ 0
  · rcases h with h | h
    all_goals
      simp_rw [h]
      revert f g
      simp [m.withBotDegree_eq, m.degree_zero]
  simp [h, m.withBotDegree_eq]

lemma withBotDegree_add_le :
    (m.toWithBotSyn <| m.withBotDegree (f + g)) ≤
      (m.toWithBotSyn <| m.withBotDegree f) ⊔ (m.toWithBotSyn <| m.withBotDegree g) := by
  wlog! +distrib h : f ≠ 0 ∧ g ≠ 0
  · rcases h with h | h <;> simp [h, m.toWithBotSyn_apply]
  simpa [withBotDegree_le_withBotDegree_iff, h] using degree_add_le (R := R)

lemma withBotDegree_add_of_lt (h : m.withBotDegree g ≺'[m] m.withBotDegree f) :
    m.withBotDegree (f + g) = m.withBotDegree f := by
  wlog! hg : g ≠ 0
  · simp [hg]
  simp? [withBotDegree_lt_withBotDegree_iff, hg] at h says
    simp only [withBotDegree_lt_withBotDegree_iff, hg, ne_eq, false_and, or_false] at h
  simp? [withBotDegree_eq_withBotDegree_iff, show f ≠ 0 by contrapose h; simp [h]] says
    simp only [withBotDegree_eq_withBotDegree_iff, show f ≠ 0 by contrapose h; simp [h], iff_false]
  rw [← and_imp_iff_and]
  refine ⟨m.degree_add_of_lt h, ?_⟩
  intro h'
  contrapose! h
  simp [← h ▸ h']

lemma withBotDegree_add_of_right_lt (h : m.withBotDegree f ≺'[m] m.withBotDegree g) :
    m.withBotDegree (f + g) = m.withBotDegree g := by
  rw [add_comm]
  exact m.withBotDegree_add_of_lt _ _ h

lemma withBotDegree_sum_le {α : Type*} {s : Finset α} {f : α → MvPolynomial σ R} :
    (m.toWithBotSyn <| m.withBotDegree <| ∑ x ∈ s, f x) ≤
      s.sup fun x ↦ (m.toWithBotSyn <| m.withBotDegree <| f x) := by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s haA h =>
    rw [Finset.sum_cons, Finset.sup_cons]
    exact le_trans (m.withBotDegree_add_le _ _) (max_le_max le_rfl h)

lemma le_withBotDegree {f : MvPolynomial σ R} {d : σ →₀ ℕ} (hd : d ∈ f.support) :
    d ≼'[m] m.withBotDegree f := by
  classical
  simp [withBotDegree_eq, toWithBotSyn_apply, ne_zero_iff.mpr ⟨d, by simpa using hd⟩, le_degree hd]

lemma withBotDegree_le_withBotDegree_of_support_subset
    {p q : MvPolynomial σ R} (h : p.support ⊆ q.support) :
    m.withBotDegree p ≼'[m] m.withBotDegree q := by
  wlog! hq : q ≠ 0
  · simpa [hq] using h
  rw [m.withBotDegree_le_withBotDegree_iff_of_ne_zero _ hq]
  exact m.degree_le_degree_of_support_subset h

lemma withBotDegree_rename_killCompl_le_withBotDegree {σ'} {f : σ' → σ}
    (hf : f.Injective) (p : MvPolynomial σ R) :
    m.withBotDegree ((p.killCompl hf).rename f) ≼'[m] m.withBotDegree p :=
  m.withBotDegree_le_withBotDegree_of_support_subset (support_rename_killCompl_subset hf)

end Semiring

end WithBotDegree

end

end MonomialOrder
