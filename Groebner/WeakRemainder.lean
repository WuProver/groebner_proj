
module

public import Mathlib
public import Groebner.Ideal

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

lemma notMem_support_of_degree_lt' {R} [CommSemiring R] {a}
    {f : MvPolynomial σ R} (h : m.degree f ≺[m] a) :
    a ∉ f.support := by
  simp [coeff_eq_zero_of_lt h]

lemma _root_.Set.ofPred_mem_range {α ι} {p : α → Prop} {f : ι → α} :
    {a | a ∈ Set.range f ∧ p a} = f '' {i | p (f i)} := by
  grind

lemma degree_le_of_withBotDegree_le_coe {R} [CommSemiring R] {e : m.syn} {f : MvPolynomial σ R}
    (h : m.toWithBotSyn (m.withBotDegree f) ≤ e) :
    m.toSyn (m.degree f) ≤ e := by
  by_cases hf : f = 0
  · simp [hf]
  simpa [m.withBotDegree_eq_coe_degree_iff _ |>.mpr hf] using h

lemma coeff_mul_of_degree_add_degree_le {R} [CommSemiring R] {e : σ →₀ ℕ}
    {f g : MvPolynomial σ R}
    [Decidable (m.degree f + m.degree g = e)]
    (h : m.degree f + m.degree g ≼[m] e) :
    (f * g).coeff e =
      if m.degree f + m.degree g = e then m.leadingCoeff f * m.leadingCoeff g else 0 := by
  by_cases! hfg0 : f = 0 ∨ g = 0
  · rcases hfg0 with h0 | h0 <;> simp [h0]
  split_ifs with h'
  · rw [← h', coeff_mul_of_degree_add]
  rw [← notMem_support_iff]
  apply m.notMem_support_of_degree_lt'
  exact lt_of_le_of_lt m.degree_mul_le <| lt_of_le_of_ne h <| m.toSyn.apply_eq_iff_eq.not.mpr h'

lemma coeff_mul_of_withBotDegree_add_withBotDegree_le {R} [CommSemiring R] {e : σ →₀ ℕ}
    {f g : MvPolynomial σ R}
    [Decidable (m.withBotDegree f + m.withBotDegree g = e)]
    (h : m.withBotDegree f + m.withBotDegree g ≼'[m] e) :
    (f * g).coeff e =
      if m.withBotDegree f + m.withBotDegree g = e then
        m.leadingCoeff f * m.leadingCoeff g else 0 := by
  by_cases! hfg0 : f = 0 ∨ g = 0
  · rcases hfg0 with h0 | h0 <;> simp [h0]
  classical convert m.coeff_mul_of_degree_add_degree_le ?_
  <;> simp_all only [m.withBotDegree_eq_coe_degree_iff _ |>.mpr hfg0.1,
    m.withBotDegree_eq_coe_degree_iff _ |>.mpr hfg0.2, ← WithBot.coe_add,
    m.toWithBotSyn_apply_coe, WithBot.coe_le_coe, WithBot.coe_eq_coe]

lemma _root_.Finsupp.support_mapRange' {α M N : Type*} [Zero M] [Zero N] {f : M → N}
    {hf : f 0 = 0} {g : α →₀ M} (h : ∀ x, f x = 0 → x = 0) :
    (g.mapRange f hf).support = g.support := by grind

lemma monomial_mem_span_range_leadingTerm_tfae {R ι} [CommSemiring R] {e : σ →₀ ℕ} {c : R}
    {b : ι → MvPolynomial σ R} :
    List.TFAE [
      monomial e c ∈ Ideal.span (Set.range (m.leadingTerm ∘ b)),
      c ≠ 0 → ∃ cs : ι →₀ R,
        (∀ i ∈ cs.support, m.degree (b i) ≤ e) ∧ c = cs.linearCombination _ (m.leadingCoeff ∘ b),
      ∃ g : ι →₀ MvPolynomial σ R,
        (∀ i, m.withBotDegree (b i) + m.withBotDegree (g i) ≼'[m] e) ∧
        monomial e c = Finsupp.linearCombination _ (m.leadingTerm ∘ b) g,
      ∃ g : ι →₀ MvPolynomial σ R,
        (∀ i, m.withBotDegree (b i) + m.withBotDegree (g i) ≼'[m] e) ∧
        monomial e c = m.leadingTerm (Finsupp.linearCombination _ b g)]
      := by
  classical
  tfae_have 1 ↔ 2 := by
    by_cases hc0 : c = 0
    · simp [hc0]
    simp_rw [Set.range_comp, leadingTerm.eq_1, MvPolynomial.mem_ideal_span_monomial_image',
      Set.ofPred_mem_range, ← Set.image_comp, Finsupp.mem_span_image_iff_linearCombination,
      Finsupp.mem_supported, support_monomial, ne_eq, hc0, ite_false, not_false_iff, true_imp_iff,
      Finset.mem_singleton, forall_eq, coeff_monomial, ite_true, eq_comm]
    exact Iff.rfl
  tfae_have 2 → 3 := by
    by_cases hc0 : c = 0
    · simpa [hc0] using ⟨0, by simp⟩
    intro h
    rcases h hc0 with ⟨cs, h⟩
    use Finsupp.onFinset cs.support (fun i ↦ monomial (e - m.degree (b i)) (cs i)) (by simp)
    split_ands
    · intro i
      by_cases! h0 : cs i = 0 ∨ b i = 0
      · rcases h0 with h0 | h0 <;> simp [h0]
      -- how can it happen?
      simp [m.withBotDegree_monomial, h0, m.withBotDegree_eq_coe_degree_iff .. |>.mpr,
        ← WithBot.coe_add, add_tsub_cancel_of_le <| h.1 _ <| cs.mem_support_iff.mpr h0.1]
    · simp [Finsupp.linearCombination_apply, - Finsupp.mem_support_iff] at h ⊢
      simp_rw [h.2, Finsupp.sum, map_sum]
      apply Finset.sum_congr rfl
      intro _ hd
      simp_rw [leadingTerm, monomial_mul_monomial, tsub_add_cancel_of_le <| h.1 _ hd]
  tfae_have 3 → 4 := by
    by_cases hc0 : c = 0
    · exact fun _ ↦ ⟨0, by simp [hc0]⟩
    rintro ⟨g, ⟨hdeg, hg⟩⟩
    use g, hdeg
    suffices c = ((Finsupp.linearCombination (MvPolynomial σ R) b) g).coeff e by
      subst this
      rw [leadingTerm, monomial_eq_monomial_iff]
      apply show ∀ a b, a ∧ (a → b) → a ∧ b ∨ _ by tauto
      nth_rw 1 [← m.toSyn.apply_eq_iff_eq, le_antisymm_iff]
      refine ⟨⟨m.le_degree_of_mem_support <| by simpa using hc0, ?_⟩, (by rw [leadingCoeff, ·])⟩
      apply m.degree_le_of_withBotDegree_le_coe
      rw [Finsupp.linearCombination_apply, Finsupp.sum]
      refine le_trans m.withBotDegree_sum_le <| Finset.sup_le_iff.mpr fun i _ ↦ ?_
      exact le_trans (mul_comm (b i) (g i) ▸ m.withBotDegree_mul_le ..) <| by simpa using hdeg i
    apply_fun (AddMonoidAlgebra.coeff · e) at hg
    simp? [Finsupp.linearCombination_apply] at hg ⊢ says
      simp only [coeff_monomial, ↓reduceIte, Finsupp.linearCombination_apply, Function.comp_apply,
        smul_eq_mul, AddMonoidAlgebra.coeff_finsuppSum, Finsupp.sum_apply] at hg ⊢
    rw [hg]
    apply Finsupp.sum_congr
    intro i hi
    rw [mul_comm, mul_comm (g i), m.coeff_mul_of_withBotDegree_add_withBotDegree_le (hdeg _),
      m.coeff_mul_of_withBotDegree_add_withBotDegree_le (by simpa using hdeg _)]
    simp
  tfae_have 4 → 2 := by
    rintro ⟨g, hdeg, hg⟩ hc
    simp? [leadingTerm, leadingCoeff, monomial_eq_monomial_iff, hc] at hg says
      simp only [leadingTerm, leadingCoeff, monomial_eq_monomial_iff, hc, coeff_degree_eq_zero_iff,
        false_and, or_false] at hg
    rcases hg with ⟨hdeg', hg⟩
    simp_rw [← hdeg', Finsupp.linearCombination_apply, Finsupp.sum, coeff_sum, smul_eq_mul,
      mul_comm (g _), m.coeff_mul_of_withBotDegree_add_withBotDegree_le (hdeg _)] at hg
    use g.mapRange m.leadingCoeff (by simp) |>.filter
      fun i ↦ m.withBotDegree (b i) + m.withBotDegree (g i) = e
    split_ands
    · simp only [Finsupp.support_filter, Finset.mem_filter, Finsupp.mem_support_iff,
        Finsupp.mapRange_apply, ne_eq, leadingCoeff_eq_zero_iff, and_imp]
      intro i hgi0
      by_cases hbi0 : b i = 0
      · simp [hbi0]
      rw [m.withBotDegree_eq_coe_degree_iff _ |>.mpr hbi0,
        m.withBotDegree_eq_coe_degree_iff _ |>.mpr hgi0, ← WithBot.coe_add, WithBot.coe_eq_coe]
      exact le_of_add_le_left ∘ le_of_eq
    simp [Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.filter_apply,
      Finsupp.support_mapRange' fun _ ↦ m.leadingCoeff_eq_zero_iff.mp, Finset.sum_filter, ← ite_and,
      mul_comm (m.leadingCoeff <| g _), hg]
  tfae_finish

lemma _root_.Finset.Colex.exists_mem_le_of_le_of_mem {α} [PartialOrder α]
    {l₁ l₂ : Colex (Finset α)} {a : α} (hle : l₁ ≤ l₂) (hmem : a ∈ ofColex l₁) :
    ∃ b ∈ ofColex l₂, a ≤ b := by
  by_cases ha2 : a ∈ ofColex l₂
  · use a
  obtain ⟨b, hb⟩ := Finset.Colex.le_def.mp hle hmem ha2
  exact ⟨b, hb.1, hb.2.2⟩

lemma _root_.Finset.Colex.max_le_max_of_le {α} [LinearOrder α]
    {l₁ l₂ : Colex (Finset α)} (h : l₁ ≤ l₂) : (ofColex l₁).max ≤ (ofColex l₂).max := by
  rw [Finset.max_le_iff]
  intro a ha
  obtain ⟨b, hb⟩ := Finset.Colex.exists_mem_le_of_le_of_mem h ha
  exact le_trans (WithBot.coe_le_coe.mpr hb.2) (Finset.le_max hb.1)

lemma withBotDegree_le_withBotDegree_of_toColex_support_le_toColex_support {R} [CommSemiring R]
    {f g : MvPolynomial σ R}
    (h : toColex (f.support.image m.toSyn) ≤ toColex (g.support.image m.toSyn)) :
    m.toWithBotSyn (m.withBotDegree f) ≤ m.toWithBotSyn (m.withBotDegree g) := by
  have := Finset.Colex.max_le_max_of_le h
  simp_rw [ofColex_toColex, Finset.max_eq_sup_coe, Finset.sup_image] at this
  -- todo: the two sub-goals should be a lemma or definition in #40010 later
  convert this <;> simp [toWithBotSyn, withBotDegree, Finset.max_eq_sup_coe]

lemma toColex_support_sub_lt_toColex_support {e : σ →₀ ℕ} {f g : MvPolynomial σ R}
    (he : e ∈ f.support) (h : m.leadingTerm g = monomial e (f.coeff e)) :
    toColex ((f - g).support.image m.toSyn) < toColex (f.support.image m.toSyn) := by
  simp_rw [Finset.Colex.lt_iff, ofColex_toColex,
    ← m.toSyn.coe_toEquiv, Equiv.image_eq_preimage_symm_of_finset, m.toSyn.coe_toEquiv_symm,
    Finset.mem_preimage]
  use m.toSyn e
  simp [leadingTerm, monomial_eq_monomial_iff, mem_support_iff.mp he, leadingCoeff] at h
  rcases h with ⟨rfl, h⟩
  refine ⟨fun e' he' ↦ ?_, by simp [he], by simp [h]⟩
  suffices m.toSyn.symm e' ∉ g.support by grind
  apply m.notMem_support_of_degree_lt'
  rwa [m.toSyn.apply_symm_apply]

lemma toColex_support_sub_le_toColex_support {e : σ →₀ ℕ} {f g : MvPolynomial σ R}
    (h : m.leadingTerm g = monomial e (f.coeff e)) :
    toColex ((f - g).support.image m.toSyn) ≤ toColex (f.support.image m.toSyn) := by
  by_cases he : e ∈ f.support
  · exact le_of_lt <| m.toColex_support_sub_lt_toColex_support he h
  rw [notMem_support_iff.mp he, monomial_zero, leadingTerm_eq_zero_iff] at h
  simp [h]

lemma withBotDegree_sub_le_withBotDegree {e : σ →₀ ℕ} {f g : MvPolynomial σ R}
    (h : m.leadingTerm g = monomial e (f.coeff e)) :
    m.withBotDegree (f - g) ≼'[m] m.withBotDegree f :=
  withBotDegree_le_withBotDegree_of_toColex_support_le_toColex_support <|
    toColex_support_sub_le_toColex_support h

attribute [local instance] WellFoundedLT.toWellFoundedRelation in
open Classical in
theorem weakDiv {ι : Type*} {b : ι → MvPolynomial σ R} (f : MvPolynomial σ R) :
    ∃ (g : ι →₀ (MvPolynomial σ R)) (r : MvPolynomial σ R),
      f = Finsupp.linearCombination _ b g + r ∧
        (∀ i, m.withBotDegree (b i) + m.withBotDegree (g i) ≼'[m] m.withBotDegree f) ∧
        ∀ e ∈ r.support, monomial e (r.coeff e) ∉ Ideal.span (Set.range <| m.leadingTerm ∘ b) := by
  classical
  by_cases! hb :
    ∀ e ∈ f.support, monomial e (f.coeff e) ∉ Ideal.span (Set.range (m.leadingTerm ∘ b))
  · exact ⟨0, f, by simp, by simp, hb⟩
  have hf0 : f ≠ 0 := by contrapose hb with rfl; simp
  obtain ⟨deg, hdeg_mem, hdeg_sum⟩ := hb
  simp_rw [m.monomial_mem_span_range_leadingTerm_tfae.out 1 4] at hdeg_sum
  rcases hdeg_sum with ⟨g_, hg_deg, hg_sum⟩
  have ⟨g', r', hg'sum, hg'deg, hdeg'sum⟩ := weakDiv (b := b) (f - g_.linearCombination _ b)
  use g_ + g', r'
  rw [sub_eq_iff_eq_add', ← add_assoc, ← map_add] at hg'sum
  refine ⟨hg'sum, fun i ↦ ?_, hdeg'sum⟩
  simp_rw [map_add] at ⊢ hg_deg hg'deg
  rcases le_max_iff.mp <| m.withBotDegree_add_le (g_ i) (g' i) with hle | hle
  · apply le_trans <| add_le_add (le_refl ..) hle
    apply le_trans <| hg_deg _
    exact m.le_withBotDegree hdeg_mem
  apply le_trans <| add_le_add (le_refl ..) hle
  apply le_trans <| hg'deg _
  exact m.withBotDegree_sub_le_withBotDegree hg_sum.symm
termination_by toColex <| f.support.image m.toSyn
decreasing_by exact m.toColex_support_sub_lt_toColex_support hdeg_mem hg_sum.symm

theorem weakDiv_set {B : Set (MvPolynomial σ R)} (f : MvPolynomial σ R) :
    (∃ (g : B →₀ (MvPolynomial σ R)) (r : MvPolynomial σ R),
      f = Finsupp.linearCombination _ (fun (b : B) ↦ (b : MvPolynomial σ R)) g + r ∧
      (∀ (b : B), m.withBotDegree b.val + m.withBotDegree (g b) ≼'[m] m.withBotDegree f) ∧
      ∀ e ∈ r.support, monomial e (r.coeff e) ∉ Ideal.span (m.leadingTerm '' B)) := by
  obtain ⟨g, r, H⟩ := m.weakDiv (b := fun (p : B) ↦ p) f
  refine ⟨g, r, H.1, H.2.1, fun e he hb ↦ H.2.2 e he <| by simpa [Set.range_comp]⟩

end MonomialOrder
