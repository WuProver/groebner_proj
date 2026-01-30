module

public import Mathlib

public section
namespace MvPolynomial

variable {σ σ' R : Type*} [CommSemiring R] {f : σ' → σ} (hf : f.Injective) {p q : MvPolynomial σ R}

variable (f) in
@[simp]
lemma rename_zero :
    (0 : MvPolynomial σ' R).rename f = 0 := rfl

@[simp]
lemma rename_eq_zero_of_injective (p : MvPolynomial σ' R)
    (hf : f.Injective) : p.rename f = 0 ↔ p = 0 := by
  rw [← rename_zero f, (MvPolynomial.rename_injective _ hf).eq_iff]

@[simp]
lemma killCompl_monomial_mapDomain {s : σ' →₀ ℕ} {c : R} :
    (monomial (s.mapDomain f) c).killCompl hf = monomial s c := by
  simp [← rename_monomial]

lemma killCompl_monomial_eq_zero {s : σ →₀ ℕ} {c : R} (hs : ∃ a ∈ s.support, a ∉ Set.range f) :
    (monomial s c).killCompl hf = 0 := by
  unfold killCompl
  rw [aeval_monomial, Finsupp.prod]
  apply mul_eq_zero_of_right
  obtain ⟨a, ha⟩ := hs
  apply Finset.prod_eq_zero ha.1
  simp [ha.2, zero_pow (Finsupp.mem_support_iff.mp ha.1)]

lemma killCompl_monomial_eq_zero' {s : σ →₀ ℕ} {c : R} (hs : ¬ ↑s.support ⊆ Set.range f) :
    (monomial s c).killCompl hf = 0 := killCompl_monomial_eq_zero hf (Set.not_subset.mp hs)

lemma killCompl_monomial_eq_monomial_comapDomain {s : σ →₀ ℕ} {c : R}
    (hs : ↑s.support ⊆ Set.range f) :
    (monomial s c).killCompl hf = monomial (s.comapDomain f hf.injOn) c := by
  nth_rw 1 [← s.mapDomain_comapDomain f hf hs, killCompl_monomial_mapDomain]

lemma killCompl_monomial {s} {c : R} [Decidable (↑s.support ⊆ Set.range f)] :
    (monomial s c).killCompl hf =
      if ↑s.support ⊆ Set.range f then monomial (s.comapDomain f hf.injOn) c else 0 := by
  split_ifs with h
  · exact killCompl_monomial_eq_monomial_comapDomain hf h
  · exact killCompl_monomial_eq_zero' hf h

lemma coeff_killCompl {s} :
    (p.killCompl hf).coeff s = p.coeff (s.mapDomain f) := by
  classical
  apply p.induction_on' (P := fun p ↦ (p.killCompl hf).coeff s = p.coeff (s.mapDomain f))
  · intro u r
    rw [killCompl_monomial]
    split_ifs with h
    · simp [← (Finsupp.mapDomain_injective hf).eq_iff, u.mapDomain_comapDomain _ hf h]
    · simp
      intro rfl
      contrapose! h
      apply subset_trans <| SetLike.coe_subset_coe.mpr <| Finsupp.mapDomain_support
      simp
  · simp_intro ..

lemma support_killCompl {p : MvPolynomial σ R} :
    (p.killCompl hf).support =
      p.support.preimage (Finsupp.mapDomain f) (Finsupp.mapDomain_injective hf).injOn := by
  classical
  ext x
  simp [coeff_killCompl]

lemma support_rename_killCompl_subset {p : MvPolynomial σ R} :
    ((p.killCompl hf).rename f).support ⊆ p.support := by
  classical
  rw [MvPolynomial.support_rename_of_injective hf, support_killCompl, Finset.image_preimage]
  exact Finset.filter_subset ..

lemma rename_killCompl_app (hf : Function.Injective f) {p : MvPolynomial σ R}
    (hp : ↑p.vars ⊆ Set.range f) : (p.killCompl hf).rename f = p := by
  classical
  rw [← MvPolynomial.support_sum_monomial_coeff p, map_sum, map_sum, ← Finset.sum_attach]
  have (x : p.support) : ↑x.val.support ⊆ Set.range f := by
    apply (subset_trans · hp)
    rw [p.vars_eq_support_biUnion_support]
    exact Finset.subset_biUnion_of_mem Finsupp.support x.prop
  simp_rw [killCompl_monomial_eq_monomial_comapDomain hf (this _),
    rename_monomial, Finsupp.mapDomain_comapDomain _ hf _ (this _),
    Finset.sum_attach p.support fun x ↦ monomial x (coeff x p)]

end MvPolynomial
