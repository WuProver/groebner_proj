
module

public import Mathlib

/-! # Weak Division

## Reference

- "On the construction of Gröbner bases using syzygies" https://www.sciencedirect.com/science/article/pii/S074771718880052X
-/

@[expose] public section

namespace MonomialOrder

open MvPolynomial

open scoped MonomialOrder

variable {σ : Type*} {m : MonomialOrder σ} {R : Type*} [CommRing R]

instance _root_.Pi.irrefl_lex {ι : Type*} {β : ι → Type*}
    (r : ι → ι → Prop) (s : {i : ι} → β i → β i → Prop) [∀ i, Std.Irrefl (@s i)] :
    Std.Irrefl (Pi.Lex r @s) where
  irrefl f := fun ⟨i, h⟩ ↦ Std.Irrefl.irrefl (f i) h.2

lemma _root_.Finset.apply_piecewise_congr {α} {π : α → Type*} {f g : ∀ i, π i}
    (s t : Finset α) (a : α)
    [∀ a, Decidable (a ∈ s)] [∀ a, Decidable (a ∈ t)]
    (ha : a ∈ s ↔ a ∈ t) : s.piecewise f g a = t.piecewise f g a := by
  grind [Finset.piecewise]

open Finset in
theorem _root_.Finset.Colex.lt_iff {α} [LinearOrder α] (l₁ l₂ : Colex (Finset α)) :
    l₁ < l₂ ↔
      ∃ a, (∀ b > a, b ∈ ofColex l₁ ↔ b ∈ ofColex l₂) ∧ a ∈ ofColex l₂ ∧ a ∉ ofColex l₁ := by
  classical
  simp_rw [lt_iff_le_and_ne, Colex.le_def, ← ofColex.injective.ne_iff]
  refine ⟨fun hlt ↦ ?_, by grind⟩
  obtain ⟨a, ha⟩ := exists_maximal (s := ofColex l₂ \ ofColex l₁) (by grind)
  simp_rw [mem_sdiff] at ha
  use a
  grind [Maximal]

open Finset in
theorem _root_.Finset.Colex.lt_iff_pi_lex_lt_pi_lex {α} {π : α → Type*} [LinearOrder α]
    [∀ a, PartialOrder (π a)] (f g : ∀ a, π a) (h : ∀ a, f a > g a)
    (l₁ l₂ : Colex (Finset α)) :
    l₁ < l₂ ↔ Pi.Lex (· > ·) (· < ·) ((ofColex l₁).piecewise f g) ((ofColex l₂).piecewise f g) := by
  unfold Pi.Lex
  convert Finset.Colex.lt_iff l₁ l₂
  all_goals grind [Finset.piecewise]

theorem _root_.Finset.Colex.strictMono_toColex_piecewise_ofColex {α} {π : α → Type*} [LinearOrder α]
    [∀ a, PartialOrder (π a)]
    (f g : ∀ a, π a) (h : ∀ a, f a > g a) :
    StrictMono (fun l ↦ toColex <| Finset.piecewise (ofColex l) f g) :=
  (Finset.Colex.lt_iff_pi_lex_lt_pi_lex f g h · · |>.mp)

instance _root_.Finset.Colex.wellFoundedLT {α : Type*} [LinearOrder α] [WellFoundedLT α] :
    WellFoundedLT (Colex (Finset α)) :=
  StrictMono.wellFoundedLT (β := Colex (Π₀ _ : α, Nat)) (f := fun l ↦ toColex <| .mk (ofColex l) 1)
    fun l₁ l₂ hl₁l₂ ↦ Finset.Colex.strictMono_toColex_piecewise_ofColex 1 0 (by simp) hl₁l₂

lemma toWithBotSyn_monotone : Monotone m.toWithBotSyn := by
  simp [toWithBotSyn, toSyn_monotone]

lemma withBotDegree_le_coe_degree {R} [CommSemiring R] (f : MvPolynomial σ R) :
    m.withBotDegree f ≤ m.degree f := by
  by_cases hf : f = 0
  · simp [hf]
  simp [m.withBotDegree_eq_coe_degree_iff f |>.mpr hf]

lemma notMem_support_of_degree_lt' {a} {f : MvPolynomial σ R} (h : m.degree f ≺[m] a) :
    a ∉ f.support := by
  simp [coeff_eq_zero_of_lt h]

attribute [local instance] WellFoundedLT.toWellFoundedRelation in
open Classical in
theorem weakDiv {ι : Type*} {b : ι → MvPolynomial σ R} (f : MvPolynomial σ R) :
    ∃ (g : ι →₀ (MvPolynomial σ R)) (r : MvPolynomial σ R),
      f = Finsupp.linearCombination _ b g + r ∧
        (∀ i, m.withBotDegree (b i) + m.withBotDegree (g i) ≼'[m] m.withBotDegree f) ∧
        ∀ e ∈ r.support, ∀ c : ι →₀ R,
          (∀ i ∈ c.support, m.degree (b i) ≤ e) →
          r.coeff e ≠ c.linearCombination _ (m.leadingCoeff ∘ b) := by
  classical
  by_cases! hb : ∀ e ∈ f.support, ∀ c : ι →₀ R,
    (∀ i ∈ c.support, m.degree (b i) ≤ e) →
      f.coeff e ≠ c.linearCombination _ (m.leadingCoeff ∘ b)
  · exact ⟨0, f, by simp, by simp, hb⟩
  have hf0 : f ≠ 0 := by contrapose hb with rfl; simp
  obtain ⟨deg, hdeg_mem, c, hdeg_mon, hdeg_sum⟩ := hb
  have hdeg_eq_add (i : ι) (hi : i ∈ c.support) :
      deg = m.degree (monomial (deg - m.degree (b i)) (c i)) + m.degree (b i) := by
    rw [m.degree_monomial, ite_eq_right (by simpa using hi),
      tsub_add_cancel_of_le (hdeg_mon _ hi)]
  obtain ⟨g', r', hg'sum, hg'deg, hg'_mon⟩ :=
    weakDiv (b := b) (f - c.sum (fun i c ↦ monomial (deg - m.degree (b i)) c *  b i))
  use g' + Finsupp.onFinset c.support (fun i ↦ monomial (deg - m.degree (b i)) (c i)) (by simp), r'
  refine ⟨?_, fun i ↦ ?_, hg'_mon⟩
  · simp? [map_add, Finsupp.linearCombination_apply (MvPolynomial σ R) (Finsupp.onFinset ..)] says
      simp only [map_add, Finsupp.linearCombination_apply (MvPolynomial σ R) (Finsupp.onFinset ..),
        smul_eq_mul, Finsupp.mem_support_iff, ne_eq, zero_mul, implies_true, Finsupp.sum_onFinset]
    simp only [Finsupp.sum] at hg'sum
    grind
  simp_rw [map_add] at ⊢ hg'deg
  apply le_trans <| add_le_add_right (m.withBotDegree_add_le ..) _
  rw [add_max, max_le_iff]
  have (i : ι) :
      m.withBotDegree (b i) + m.withBotDegree (monomial (deg - m.degree (b i)) (c i)) ≼'[m]
        m.withBotDegree f := by
    by_cases hi : c i = 0
    · simp [hi]
    rw [m.withBotDegree_eq_coe_degree_iff f |>.mpr hf0]
    trans m.toWithBotSyn ↑(m.degree (b i) + m.degree (monomial (deg - m.degree (b i)) (c i)))
    · simp_rw [WithBot.coe_add, map_add]
      gcongr <;> exact m.toWithBotSyn_monotone (m.withBotDegree_le_coe_degree _)
    rw [add_comm]
    apply le_of_eq_of_le <| congrArg _ <| congrArg _ (hdeg_eq_add i (by simpa using hi)).symm
    simp_rw [m.toWithBotSyn_apply_coe, WithBot.coe_le_coe]
    exact m.le_degree_of_mem_support hdeg_mem
  refine ⟨?_, by simpa using this i⟩
  apply le_trans <| hg'deg ..
  rw [sub_eq_add_neg]
  apply le_trans <| m.withBotDegree_add_le ..
  simp only [Finsupp.sum, withBotDegree_neg, sup_le_iff, Std.le_refl, true_and]
  apply le_trans <| m.withBotDegree_sum_le ..
  rw [Finset.sup_le_iff]
  rintro i -
  apply le_trans <| m.withBotDegree_mul_le ..
  simpa only [add_comm] using this i
termination_by toColex <| f.support.image m.toSyn
decreasing_by
  simp_rw [Finset.Colex.lt_iff, ofColex_toColex,
    ← m.toSyn.coe_toEquiv, Equiv.image_eq_preimage_symm_of_finset, m.toSyn.coe_toEquiv_symm,
    Finset.mem_preimage]
  use m.toSyn deg
  refine ⟨?_, by simp [hdeg_mem], ?_⟩
  · intro e he
    simp only [mem_support_iff, coeff_sub, ne_eq]
    suffices m.toSyn.symm e ∉ support (c.sum fun i c ↦ monomial (deg - m.degree (b i)) c * b i) by
      grind
    apply m.notMem_support_of_degree_lt'
    rw [m.toSyn.apply_symm_apply]
    apply lt_of_lt_of_le' he
    apply le_trans m.degree_sum_le
    apply Finset.sup_le
    intro i hi
    nth_rw 2 [hdeg_eq_add i hi]
    exact m.degree_mul_le
  simp? [hdeg_sum, Finsupp.linearCombination_apply, Finsupp.sum, MvPolynomial.coeff_sum,
      sub_eq_zero] says
    simp only [Finsupp.sum, AddEquiv.symm_apply_apply, mem_support_iff, coeff_sub, hdeg_sum,
      Finsupp.linearCombination_apply, Function.comp_apply, smul_eq_mul, coeff_sum, ne_eq,
      sub_eq_zero, Decidable.not_not]
  apply Finset.sum_congr rfl
  intro i hi
  nth_rw 1 [← add_tsub_cancel_of_le (hdeg_mon _ (by simpa using hi))]
  rw [mul_comm _ (b i), coeff_mul_monomial, leadingCoeff, mul_comm]

theorem weakDiv_set {B : Set (MvPolynomial σ R)} (f : MvPolynomial σ R) :
    (∃ (g : B →₀ (MvPolynomial σ R)) (r : MvPolynomial σ R),
      f = Finsupp.linearCombination _ (fun (b : B) ↦ (b : MvPolynomial σ R)) g + r ∧
      (∀ (b : B), m.withBotDegree b.val + m.withBotDegree (g b) ≼'[m] m.withBotDegree f) ∧
      (∀ e ∈ r.support, ∀ c : B →₀ R,
        (∀ b ∈ c.support, m.degree b.val ≤ e) →
        r.coeff e ≠ c.linearCombination _ (m.leadingCoeff ∘ Subtype.val))) := by
  obtain ⟨g, r, H⟩ := m.weakDiv (b := fun (p : B) ↦ p) f
  refine ⟨g, r, H.1, H.2.1, fun e he b hb ↦ H.2.2 e he b hb⟩

end MonomialOrder
