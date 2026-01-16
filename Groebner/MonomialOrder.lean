module

public import Mathlib

open MvPolynomial
namespace MonomialOrder
variable {σ : Type*} {m : MonomialOrder σ}

/- merged:
- https://github.com/leanprover-community/mathlib4/pull/32344,
- https://github.com/leanprover-community/mathlib4/pull/32788.
This section is private. -/
section MergedsPolynomial''
section Ring

variable {R : Type*} [CommRing R]

variable (m) in
/-- The S-polynomial of two polynomials.

Denoting

- the leading monomial of polynomial $f$ and $g$ as $lm(f)$ and $lm(g)$,
- the leading coefficient of $f$ and $g$ as $lc(f)$ and $lc(g)$
  (formalized as `m.leadingCoeff f` and `m.leadingCoeff g`), and
- the least common multiple of $lm(f)$ and $lm(g)$ as $lcm(lm(f),lm(g))$,

the S-polynomial of $f$ and $g$ is defined as
$$sPoly(f,g) := (lcm(lm(f),lm(g)) / lm(f)) * lc(g) * f - (lcm(lm(f),lm(g)) / lm(g)) * lc(f) * g.$$

$(lcm(lm(f),lm(g)) / lm(f))$ and $lcm(lm(f),lm(g)) / lm(g)$ is formalized as
`monomial (m.degree g - m.degree f) 1` and `monomial (m.degree g - m.degree f) 1`, while there is
also another more direct formalization in `sPolynomial''_def`.

Notice that, when the polynomial ring is over a field, S-polynomial is usually defined as
$$sPoly'(f,g) :=
  (lcm(lm(f),lm(g)) / (lm(f) * lc(f))) * f - (lcm(lm(f),lm(g)) / (lm(g) * lc(g))) * g,$$
while we avoid inverting $lc(f)$ and $lc(g)$ in this formalization so that it doesn't require a
field or units (`IsUnit`) over ring.

An equality between these two versions holds: $$sPoly(f,g) = lc(f) * lc(g) * sPoly'(f,g).$$
-/
noncomputable def sPolynomial'' (f g : MvPolynomial σ R) : MvPolynomial σ R :=
  monomial (m.degree g - m.degree f) (m.leadingCoeff g) * f -
  monomial (m.degree f - m.degree g) (m.leadingCoeff f) * g

lemma sPolynomial''_def (f g : MvPolynomial σ R) :
    m.sPolynomial'' f g =
      monomial (m.degree f ⊔ m.degree g - m.degree f) (m.leadingCoeff g) * f -
      monomial (m.degree f ⊔ m.degree g - m.degree g) (m.leadingCoeff f) * g := by
  suffices ∀ f g, m.degree g - m.degree f = m.degree f ⊔ m.degree g - m.degree f by
    rw [sPolynomial'', this, this, sup_comm]
  intro f g
  ext a
  obtain (h | h) := le_total (m.degree f a) (m.degree g a) <;> simp [h]

lemma sPolynomial''_antisymm (f g : MvPolynomial σ R) :
    m.sPolynomial'' f g = - m.sPolynomial'' g f :=
  (neg_sub (_ * g) (_ * f)).symm

@[simp]
lemma sPolynomial''_left_zero (g : MvPolynomial σ R) :
    m.sPolynomial'' 0 g = 0 := by
  simp [sPolynomial'']

@[simp]
lemma sPolynomial''_right_zero (f : MvPolynomial σ R) :
    m.sPolynomial'' f 0 = 0 := by
  rw [sPolynomial''_antisymm, sPolynomial''_left_zero, neg_zero]

@[simp]
lemma sPolynomial''_self (f : MvPolynomial σ R) : m.sPolynomial'' f f = 0 := sub_self _

lemma degree_sPolynomial''_le (f g : MvPolynomial σ R) :
    ((m.degree <| m.sPolynomial'' f g) ≼[m] m.degree f ⊔ m.degree g) := by
  classical
  wlog! +distrib h0 : f ≠ 0 ∧ g ≠ 0
  · (obtain rfl | rfl := h0) <;> simp
  simp only [sPolynomial''_def]
  apply degree_sub_le.trans
  apply (sup_le_sup degree_mul_le degree_mul_le).trans
  simp [degree_monomial, h0.1, h0.2, tsub_add_cancel_of_le, le_sup_left, le_sup_right]

lemma coeff_sPolynomial''_sup_eq_zero (f g : MvPolynomial σ R) :
    (m.sPolynomial'' f g).coeff (m.degree f ⊔ m.degree g) = 0 := by
  rw [sPolynomial''_def, coeff_sub]
  nth_rewrite 1 [← tsub_add_cancel_of_le le_sup_left, coeff_monomial_mul]
  nth_rewrite 1 [← tsub_add_cancel_of_le le_sup_right, coeff_monomial_mul]
  unfold leadingCoeff
  ring

lemma degree_sPolynomial'' (f g : MvPolynomial σ R) :
    (m.degree <| m.sPolynomial'' f g) ≺[m] m.degree f ⊔ m.degree g ∨ m.sPolynomial'' f g = 0 := by
  by_cases hf : m.degree f = 0 ∧ m.degree g = 0
  · rcases hf with ⟨h₁, h₂⟩
    right
    suffices C (m.leadingCoeff g) * f - C (m.leadingCoeff f) * g = 0 by simp_all [sPolynomial''_def]
    nth_rewrite 1 [degree_eq_zero_iff.mp h₁]
    nth_rewrite 2 [degree_eq_zero_iff.mp h₂]
    ring
  · rw [or_iff_not_imp_right]
    intro hs
    apply (m.degree_sPolynomial''_le f g).lt_of_ne
    apply m.toSyn.injective.ne
    contrapose! hs
    rw [← m.coeff_degree_eq_zero_iff, hs, m.coeff_sPolynomial''_sup_eq_zero]

lemma degree_sPolynomial''_lt_sup_degree {f g : MvPolynomial σ R} (h : m.sPolynomial'' f g ≠ 0) :
    (m.degree <| m.sPolynomial'' f g) ≺[m] m.degree f ⊔ m.degree g :=
  (or_iff_left h).mp <| m.degree_sPolynomial'' f g

lemma sPolynomial''_lt_of_degree_ne_zero_of_degree_eq {f g : MvPolynomial σ R}
    (h : m.degree f = m.degree g) (hs : m.sPolynomial'' f g ≠ 0) :
    m.degree (m.sPolynomial'' f g) ≺[m] m.degree f := by
  simpa [h] using m.degree_sPolynomial''_lt_sup_degree hs

lemma sPolynomial''_monomial_mul [NoZeroDivisors R] (p₁ p₂ : MvPolynomial σ R) (d₁ d₂ : σ →₀ ℕ)
    (c₁ c₂ : R) :
    m.sPolynomial'' ((monomial d₁ c₁) * p₁) ((monomial d₂ c₂) * p₂) =
      monomial ((d₁ + m.degree p₁) ⊔ (d₂ + m.degree p₂) - m.degree p₁ ⊔ m.degree p₂) (c₁ * c₂) *
      m.sPolynomial'' p₁ p₂ := by
  classical
  simp only [sPolynomial''_def]
  wlog! +distrib H : c₁ ≠ 0 ∧ c₂ ≠ 0 ∧ p₁ ≠ 0 ∧ p₂ ≠ 0
  · (obtain rfl | rfl | rfl | rfl := H) <;> simp
  rcases H with ⟨hc1, hc2, hp1, hp2⟩
  have hm1 := (monomial_eq_zero (s := d₁)).not.mpr hc1
  have hm2 := (monomial_eq_zero (s := d₂)).not.mpr hc2
  simp_rw [m.degree_mul hm1 hp1, m.degree_mul hm2 hp2,
    mul_sub, ← mul_assoc _ _ p₁, ← mul_assoc _ _ p₂, monomial_mul,
    m.leadingCoeff_mul hm1 hp1, m.leadingCoeff_mul hm2 hp2, m.leadingCoeff_monomial,
    degree_monomial, hc1, hc2, reduceIte, mul_right_comm, mul_comm c₂ c₁]
  rw [tsub_add_tsub_cancel (sup_le_sup (self_le_add_left _ _) (self_le_add_left _ _)) (by simp),
    tsub_add_tsub_cancel (sup_le_sup (self_le_add_left _ _) (self_le_add_left _ _)) (by simp),
    tsub_add_eq_add_tsub le_sup_left, tsub_add_eq_add_tsub le_sup_right,
    add_comm d₁, add_comm d₂, add_tsub_add_eq_tsub_right, add_tsub_add_eq_tsub_right]

lemma sPolynomial''_monomial_mul' [NoZeroDivisors R] (p₁ p₂ : MvPolynomial σ R) (d₁ d₂ : σ →₀ ℕ)
    (c₁ c₂ : R) :
    m.sPolynomial'' (monomial d₁ c₁ * p₁) (monomial d₂ c₂ * p₂) =
      monomial (m.degree (monomial d₁ c₁ * p₁) ⊔ m.degree (monomial d₂ c₂ * p₂) -
          m.degree p₁ ⊔ m.degree p₂) (c₁ * c₂) *
      m.sPolynomial'' p₁ p₂ := by
  classical
  wlog! +distrib H : c₁ ≠ 0 ∧ c₂ ≠ 0 ∧ p₁ ≠ 0 ∧ p₂ ≠ 0
  · (obtain rfl | rfl | rfl | rfl := H) <;> simp
  simp [H, degree_mul, sPolynomial''_monomial_mul, degree_monomial]

lemma sPolynomial''_leadingTerm_mul [NoZeroDivisors R] (p₁ p₂ q₁ q₂ : MvPolynomial σ R) :
    m.sPolynomial'' (m.leadingTerm p₁ * q₁) (m.leadingTerm p₂ * q₂) =
    monomial
        ((m.degree p₁ + m.degree q₁) ⊔ (m.degree p₂ + m.degree q₂) - m.degree q₁ ⊔ m.degree q₂)
        (m.leadingCoeff p₁ * m.leadingCoeff p₂) *
      m.sPolynomial'' q₁ q₂ := by
  simp [sPolynomial''_monomial_mul, leadingTerm]

lemma sPolynomial''_leadingTerm_mul' [NoZeroDivisors R] (p₁ p₂ q₁ q₂ : MvPolynomial σ R) :
    m.sPolynomial'' (m.leadingTerm p₁ * q₁) (m.leadingTerm p₂ * q₂) =
    monomial
        ((m.degree (p₁ * q₁)) ⊔ (m.degree (p₂ * q₂)) - m.degree q₁ ⊔ m.degree q₂)
        (m.leadingCoeff p₁ * m.leadingCoeff p₂) *
      m.sPolynomial'' q₁ q₂ := by
  classical
  wlog! +distrib H : p₁ ≠ 0 ∧ p₂ ≠ 0 ∧ q₁ ≠ 0 ∧ q₂ ≠ 0
  · (obtain rfl | rfl | rfl | rfl := H) <;> simp
  simp [H, leadingTerm, sPolynomial''_monomial_mul, degree_mul]

lemma sPolynomial''_decomposition {d : m.syn} {ι : Type*}
    {B : Finset ι} {g : ι → MvPolynomial σ R}
    (hd : ∀ b ∈ B,
      (m.toSyn <| m.degree <| g b) = d ∧ IsUnit (m.leadingCoeff <| g b) ∨ g b = 0)
    (hfd : (m.toSyn <| m.degree <| ∑ b ∈ B, g b) < d) :
    ∃ (c : ι → ι → R),
      ∑ b ∈ B, g b = ∑ b₁ ∈ B, ∑ b₂ ∈ B, (c b₁ b₂) • m.sPolynomial'' (g b₁) (g b₂) := by
  classical
  induction B using Finset.induction_on with
  | empty => simp
  | insert b B hb h =>
    by_cases hb0 : g b = 0
    · simp_all
    simp? [Finset.sum_insert hb, hb0] at hfd hd says
      simp only [Finset.sum_insert hb, Finset.mem_insert, forall_eq_or_imp, hb0, or_false] at hfd hd
    obtain ⟨⟨rfl, isunit_gb⟩, hd⟩ := hd
    use fun b₁ b₂ ↦ if b₂ = b then ↑isunit_gb.unit⁻¹ else 0
    simp? [Finset.sum_insert hb, hb] says
      simp only [Finset.sum_insert hb, ite_smul, zero_smul, ↓reduceIte, Finset.sum_ite_eq', hb,
        add_zero, sPolynomial''_self, smul_zero, zero_add]
    simp only [m.toSyn.injective.eq_iff] at *
    trans ∑ b' ∈ B, (g b' - (m.leadingCoeff (g b') * ↑isunit_gb.unit⁻¹) • g b)
    · suffices (-(∑ i ∈ B, m.leadingCoeff (g i))) = m.leadingCoeff (g b) by
        rw [add_comm, Finset.sum_sub_distrib, sub_eq_add_neg, ← Finset.sum_smul, ← Finset.sum_mul,
          ← neg_smul, ← neg_mul, this, isunit_gb.mul_val_inv, one_smul]
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
      rw [sPolynomial'']
      obtain (⟨h, -⟩ | h) := hd b' hb' <;>
        simp [h, ← smul_eq_C_mul, smul_sub, ← mul_smul, mul_comm (m.leadingCoeff (g b'))]

end Ring

end MergedsPolynomial''

end MonomialOrder
