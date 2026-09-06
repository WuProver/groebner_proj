module

public import Mathlib
public section
namespace MvPolynomial

variable {τ σ R : Type*} [CommSemiring R] {f : σ → τ} (hf : f.Injective) {p q : MvPolynomial τ R}

-- lemmas merged: https://github.com/leanprover-community/mathlib4/pull/34757
-- lemmas merged: https://github.com/leanprover-community/mathlib4/pull/34758

-- not yet submitted
lemma rename_killCompl_app (hf : Function.Injective f) {p : MvPolynomial τ R}
    (hp : ↑p.vars ⊆ Set.range f) : (p.killCompl hf).rename f = p := by
  classical
  rw [← MvPolynomial.support_sum_monomial_coeff p, map_sum, map_sum, ← Finset.sum_attach]
  have (x : p.support) : ↑x.val.support ⊆ Set.range f := by
    apply (subset_trans · hp)
    rw [p.vars_eq_support_biUnion_support]
    exact Finset.subset_biUnion_of_mem Finsupp.support x.prop
  simp_rw [killCompl_monomial_eq_monomial_comapDomain_of_subset hf _ (this _),
    rename_monomial, Finsupp.mapDomain_comapDomain _ hf _ (this _),
    Finset.sum_attach p.support fun x ↦ monomial x (p.coeff x)]

end MvPolynomial
