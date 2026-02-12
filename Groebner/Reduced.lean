module

public import Groebner.Groebner
public import Groebner.Ideal

variable {σ R : Type*} [CommSemiring R] {m : MonomialOrder σ}
variable {G : Set (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)}
variable (hG : m.IsGroebnerBasis G I)

@[expose] public section

namespace MonomialOrder
open MvPolynomial MonomialOrder IsRemainder IsGroebnerBasis

set_option linter.unusedVariables false in
def IsGroebnerBasis.IsMinimal (hG : m.IsGroebnerBasis G I) :=
  (∀ p ∈ G, m.Monic p) ∧ (∀ p ∈ G, ∀ q ∈ G, q ≠ p → ¬ m.degree q ≤ m.degree p)

def IsGroebnerBasis.IsMinimal.isMinimal_def (hG : m.IsGroebnerBasis G I) :
    hG.IsMinimal ↔ (∀ p ∈ G, m.Monic p) ∧ G.Pairwise (¬ m.degree · ≤ m.degree ·) := by
  rw [IsMinimal, Set.Pairwise]
  tauto

def IsGroebnerBasis.IsMinimal.monic {hG : m.IsGroebnerBasis G I} (hG' : hG.IsMinimal) {p}
    (h : p ∈ G) : m.Monic p := hG'.1 _ h

def IsGroebnerBasis.IsMinimal.pairwise {hG : m.IsGroebnerBasis G I} (hG' : hG.IsMinimal) :
    G.Pairwise (¬ m.degree · ≤ m.degree ·) := (isMinimal_def .. |>.mp hG').2

set_option linter.unusedVariables false in
def IsGroebnerBasis.IsReduced (hG : m.IsGroebnerBasis G I) :=
  (∀ p ∈ G, m.Monic p) ∧ ∀ p ∈ G, m.IsRemainder p (G \ {p}) p

-- lemma degree_eq_iff_of_isRemainder {p r : MvPolynomial σ R}
--     (hG : m.IsRemainder p G r)
--     (hG' : ∀ g ∈ G, IsUnit (m.leadingCoeff g)) :
--     m.degree p = m.degree r ↔
--       ∀ g ∈ G, ¬ m.degree g ≤ m.degree p := by
--   unfold IsRemainder at hG
--   sorry

-- lemma leadingTerm_eq_iff_of_isRemainder {p r : MvPolynomial σ R}
--     (hG : m.IsRemainder p G r)
--     (hG' : ∀ g ∈ G, IsUnit (m.leadingCoeff g)) :
--     m.leadingTerm p = m.leadingTerm r ↔
--       ∀ g ∈ G, ¬ m.degree g ≤ m.degree p := by
--   sorry

-- lemma isGroebnerBasis_of_isRemainder_of_isGroebnerBasis
--     {R : Type*} [CommRing R] {m : MonomialOrder σ}
--     {G : Set (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)}
--     (hG : m.IsGroebnerBasis G I) (hG' : ∀ g ∈ G, IsUnit (m.leadingCoeff g))
--     (r : G → MvPolynomial σ R) (hr : ∀ g : G, m.IsRemainder ↑g (G \ {↑g}) (r g)) :
--     m.IsGroebnerBasis (Set.range r) I := by
--   have rmemI (g : G) : r g ∈ I := by
--     rw [m.mem_ideal_iff _ (hr g)]
--     · exact Set.mem_of_subset_of_mem hG.1 g.2
--     rw [Set.diff_singleton_subset_iff, Set.subset_insert_iff]
--     simp [hG.1]
--   constructor
--   · intro r'
--     rw [Set.mem_range]
--     rintro ⟨g, hg⟩
--     exact hg ▸ rmemI g
--   refine le_antisymm ?_ ?_
--   on_goal -1 =>
--     rw [Ideal.span_le]
--     intro _
--     simp only [Set.mem_image, Set.mem_range]
--     rintro ⟨_, ⟨g, hg⟩, hg'⟩
--     subst hg hg'
--     apply Submodule.mem_span_of_mem (Set.mem_image_of_mem m.leadingTerm <| rmemI g)
--   rw [hG.2, Ideal.span_le]
--   intro _
--   rw [Set.mem_image]
--   rintro ⟨g, hgI, hLTg⟩
--   subst hLTg
--   -- rw [monomial_notMem_span_leadingTerm]
--   sorry

-- `hG` can be generalized more.
lemma IsGroebnerBasis.isGroebnerBasis_minimal (hG : m.IsGroebnerBasis G I)
    {G' : Set (MvPolynomial σ R)} (h : G' ⊆ I) (hG' : ∀ g ∈ G', IsUnit (m.leadingCoeff g))
    (h' : {a | Minimal (· ∈ m.degree '' (G \ {0})) a} ⊆ m.degree '' G') :
    m.IsGroebnerBasis G' I := by
  rw [isGroebnerBasis_iff, m.span_leadingTerm_eq_span_monomial hG']
  exists h
  have := hG.span_leadingTerm_image
  apply (le_of_eq_of_le · <| m.span_leadingTerm_le_span_monomial ..) at this
  rw [Ideal.span_le] at this
  apply le_trans this
  simp_rw [← Set.image_image (monomial · (1 : R)) m.degree]
  rw [ideal_span_monomial_image_eq_ideal_span_monomial_image_minimal]
  apply Ideal.span_mono
  exact Set.image_mono h'

lemma IsGroebnerBasis.isGroebnerBasis_monomial (s : Set (σ →₀ ℕ)) :
    m.IsGroebnerBasis ((MvPolynomial.monomial · (1 : R)) '' s)
      (Ideal.span ((MvPolynomial.monomial · 1) '' s)) := by
  classical
  wlog! nontrivial : Nontrivial R generalizing
  · exact IsGroebnerBasis.of_subsingleton ..
  refine ⟨Ideal.subset_span, ?_⟩
  rw [le_antisymm_iff, Ideal.span_le, Ideal.span_le]
  constructor
  case right =>
    apply (subset_trans · Ideal.subset_span)
    apply Set.image_mono
    exact Ideal.subset_span
  rw [m.span_leadingTerm_eq_span_monomial (by simp), Set.image_image]
  simp [-Set.image_subset_iff, m.degree_monomial]
  intro p
  simp [mem_ideal_span_monomial_image, leadingTerm]
  aesop

lemma IsGroebnerBasis.isGroebnerBasis_monomial_minimal {R : Type*} [CommSemiring R]
    (s : Set (σ →₀ ℕ)) :
    m.IsGroebnerBasis ((MvPolynomial.monomial · (1 : R)) '' {x | Minimal (· ∈ s) x})
      (Ideal.span ((MvPolynomial.monomial · 1) '' s)) := by
  classical
  wlog! nontrivial : Nontrivial R generalizing
  · exact IsGroebnerBasis.of_subsingleton ..
  constructor
  · apply (subset_trans · Ideal.subset_span)
    exact Set.image_mono <| setOf_minimal_subset s
  simpa [Set.image_image,
      ← MvPolynomial.ideal_span_monomial_image_eq_ideal_span_monomial_image_minimal] using
    isGroebnerBasis_monomial (m := m) (s := s) (R := R) |>.2

lemma IsGroebnerBasis.smul
    {ι : Type*} (f : ι → R) (f' : ι → MvPolynomial σ R) (hf : ∀ i : ι, IsUnit (f i))
    (hG : m.IsGroebnerBasis (Set.range f') I) :
    m.IsGroebnerBasis (Set.range (fun i ↦ (f i) • (f' i))) I := by
  -- the proof can be generalized
  classical
  simp_rw [smul_eq_C_mul]
  constructor
  · intro p
    simp_rw [Set.mem_range]
    rintro ⟨q, rfl⟩
    exact Ideal.mul_mem_left I _ (hG.1 <| by simp)
  rw [hG.2]
  unfold Ideal.span
  rw [Submodule.span_eq_iSup_of_singleton_spans, Submodule.span_eq_iSup_of_singleton_spans]
  have hunit (i) : IsUnit (C (σ := σ) (f i)) := RingHom.isUnit_map C (hf i)
  simp_rw [iSup_image, iSup_range]
  congr
  ext i : 1
  convert Submodule.span_singleton_smul_eq (hunit i) (m.leadingTerm (f' i)) |>.symm using 3
  simp [leadingTerm, C_mul_monomial, leadingCoeff]
  suffices m.degree (C (f i) * (f' i)) = m.degree (f' i) by simp [this]
  wlog! hg : f' i ≠ 0
  · simp [hg]
  rw [m.degree_mul_of_isRegular_left, m.degree_C, zero_add]
  · simp [leadingCoeff, hf i |>.isRegular]
  · exact hg

lemma IsGroebnerBasis.smul_iff
    {ι : Type*} (f : ι → R) (f' : ι → MvPolynomial σ R) (hf : ∀ i : ι, IsUnit (f i)) :
    m.IsGroebnerBasis (Set.range (fun i ↦ (f i) • (f' i))) I ↔
      m.IsGroebnerBasis (Set.range f') I := by
  classical
  refine ⟨?_, IsGroebnerBasis.smul f f' hf⟩
  convert IsGroebnerBasis.smul
    (fun i ↦ ↑(hf i).unit⁻¹) (fun i ↦ (f i) • (f' i)) (by simp) (I := I)
  simp [smul_smul]

lemma IsGroebnerBasis.inv (hG : m.IsGroebnerBasis G I)
    (hG' : ∀ g ∈ G, IsUnit (m.leadingCoeff g)) :
    m.IsGroebnerBasis (Set.range fun (g : G) ↦ (hG' _ g.prop).unit⁻¹ • g.val) I :=
  smul (hG := by simp [hG]) (hf := by simp)

lemma IsGroebnerBasis.span_image_leadingTerm
    (hG : m.IsGroebnerBasis G I) (hG' : ∀ g ∈ G, IsUnit (m.leadingCoeff g)) :
    m.IsGroebnerBasis (m.leadingTerm '' G) (Ideal.span (m.leadingTerm '' I)) := by
  classical
  rw [hG.2, Set.image_eq_range, ← IsGroebnerBasis.smul_iff
    (f := fun (g : G) ↦ ↑(hG' g.1 g.2).unit⁻¹) (hf := by simp), ← Set.image_eq_range,
    m.span_leadingTerm_eq_span_monomial hG']
  simp [leadingTerm, smul_monomial,
    ← Set.image_eq_range (fun g ↦ monomial (m.degree g) (1 : R)) G,
    ← Set.image_image (monomial · (1 : R)),
    IsGroebnerBasis.isGroebnerBasis_monomial (σ := σ) (m := m)]

open MvPolynomial MonomialOrder MonomialOrder.IsGroebnerBasis
namespace IsGroebnerBasis

variable {hG}

-- todo: move
lemma IsRemainder.self_iff (p : MvPolynomial σ R)
    (G : Set (MvPolynomial σ R)) :
    m.IsRemainder p G p ↔
    ∀ a ∈ p.support, ∀ q ∈ G, q ≠ 0 → ¬ m.degree q ≤ a :=
  and_iff_right ⟨0, by simp⟩

lemma IsRemainder.self_tfae (p : MvPolynomial σ R)
    (G : Set (MvPolynomial σ R)) :
    [m.IsRemainder p G p, ∀ B' ⊆ G, m.IsRemainder p B' p,
      ∀ q ∈ G, m.IsRemainder p {q} p,
      ∀ a ∈ p.support, ∀ q ∈ G, q ≠ 0 → ¬ m.degree q ≤ a].TFAE := by
  classical
  apply List.tfae_of_forall (∀ a ∈ p.support, ∀ q ∈ G, q ≠ 0 → ¬ m.degree q ≤ a)
  intro h h
  fin_cases h
  · exact IsRemainder.self_iff ..
  · simp only [IsRemainder.self_iff]
    aesop
  · simp only [IsRemainder.self_iff]
    aesop
  rfl

lemma IsRemainder.self {p r : MvPolynomial σ R}
    (h : m.IsRemainder p G r) :
    m.IsRemainder r G r :=
  ⟨⟨0, by simp⟩, h.2⟩

lemma IsReduced.isReduced_def :
    hG.IsReduced ↔
      (∀ p ∈ G, m.Monic p) ∧
      ∀ p ∈ G, ∀ a ∈ p.support, ∀ q ∈ G, q ≠ p → ¬ m.degree q ≤ a := by
  simp? [IsReduced, IsRemainder.self_iff] says
    simp only [IsReduced, IsRemainder.self_iff, mem_support_iff, ne_eq, Set.mem_diff,
      Set.mem_singleton_iff, and_imp, and_congr_right_iff]
  rintro h1
  wlog! h : Nontrivial R
  · simp [Subsingleton.eq_zero]
  have (g) (hg : g ∈ G) : g ≠ 0 := (h1 g hg).ne_zero
  aesop

lemma IsReduced.isMinimal : hG.IsReduced → hG.IsMinimal := by
  rw [IsReduced.isReduced_def, IsMinimal]
  intro h
  refine ⟨h.1, ?_⟩
  intro p hp q hq
  wlog! nontrivial : Nontrivial R
  · simp [Subsingleton.eq_zero]
  exact h.2 p hp (m.degree p) (by simp [h.1 p hp |>.ne_zero]) q hq

@[simp]
lemma IsReduced.of_subsingleton [Subsingleton (MvPolynomial σ R)]
    {s : Set (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)} :
    (IsGroebnerBasis.of_subsingleton (m := m) (s := s) (I := I)).IsReduced := by
  simp [IsReduced, Subsingleton.eq_zero (α := MvPolynomial σ R), Monic,
    ← (MvPolynomial.C_injective σ R).eq_iff]

@[simp]
lemma IsMinimal.of_subsingleton [Subsingleton (MvPolynomial σ R)]
    {s : Set (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)} :
    (IsGroebnerBasis.of_subsingleton (m := m) (s := s) (I := I)).IsMinimal :=
  IsReduced.isMinimal IsReduced.of_subsingleton

lemma IsReduced.isReduced_monomial {s : Set (σ →₀ ℕ)} {I : Ideal (MvPolynomial σ R)}
    (h : m.IsGroebnerBasis ((MvPolynomial.monomial · (1 : R)) '' {x | Minimal (· ∈ s) x}) I) :
    h.IsReduced := by
  classical
  rw [IsReduced.isReduced_def]
  constructor
  · simp
  simp_rw [Set.mem_image, Set.mem_setOf]
  rintro p ⟨p', ⟨hp', rfl⟩⟩ a ha q ⟨q', ⟨hq', rfl⟩⟩ hqp
  simp [monomial_eq_monomial_iff] at hqp
  have : Nontrivial R := nontrivial_of_ne _ _ hqp.2
  simp at ha
  subst ha
  simp [degree_monomial]
  by_contra! hq'p'
  exact hqp.1 <| le_antisymm hq'p' <| hp'.le_of_le (hq'.prop) hq'p'

-- lemma isMinimal_monomial_iff_isReduced_monomial {s : Set (σ →₀ ℕ)} {I : Ideal (MvPolynomial σ R)}
--     (hs : m.IsGroebnerBasis ((MvPolynomial.monomial · (1 : R)) '' s) I) :
--     hs.IsMinimal ↔ hs.IsReduced := by
--   rw [IsMinimal, isReduced_def]
--   apply Iff.and (Iff.refl _)
--   simp_rw [Set.mem_image]
--   -- easy
--   sorry

lemma IsMinimal.image_leadingTerm_eq_image_monomial_one (hG' : hG.IsMinimal) :
    m.leadingTerm '' G = (fun p ↦ monomial (m.degree p) 1) '' G := by
  simp_rw [Set.image_eq_range]
  congr
  ext x : 1
  simp [leadingTerm, hG'.1]

lemma IsMinimal.isReduced_leadingTerm (hG' : hG.IsMinimal) :
    IsGroebnerBasis.span_image_leadingTerm hG (by simp_intro .. [hG'.1])
      |>.IsReduced := by
  classical
  wlog! nontrivial : Nontrivial R
  · simp
  rw [IsReduced.isReduced_def]
  constructor
  · simpa using hG'.1
  have := hG'.2
  simp_rw [Set.mem_image]
  rintro _ ⟨p, ⟨hp, rfl⟩⟩
  simp_rw [support_leadingTerm' (hG'.1 p hp).ne_zero, Finset.mem_singleton]
  rintro _ rfl _ ⟨q, ⟨hq, rfl⟩⟩ hqp
  simp [degree_leadingTerm, this _ hp _ hq (by aesop)]

-- lemσisReduced_span_monomial_iff {R : Type*} [CommSemiring R] {s : Set (σ →₀ ℕ)}
--     {I : Ideal (MvPolynomial σ R)}
--     (h : m.IsGroebnerBasis ((MvPolynomial.monomial · (1 : R)) '' {x | Minimal (· ∈ s) x}) I) :
--     h.IsReduced := by
--   classical
--   rw [isReduced_def]
--   constructor
--   · simp
--   simp_rw [Set.mem_image, Set.mem_setOf]
--   rintro p ⟨p', ⟨hp', rfl⟩⟩ a ha q ⟨q', ⟨hq', rfl⟩⟩ hqp
--   simp [monomial_eq_monomial_iff] at hqp
--   have : Nontrivial R := nontrivial_of_ne _ _ hqp.2
--   simp at ha
--   subst ha
--   simp [degree_monomial]
--   by_contra! hq'p'
--   exact hqp.1 <| le_antisymm hq'p' <| hp'.le_of_le (hq'.prop) hq'p'


-- lemma _root_.Set.eq_iff_of_image_eq {α β : Type*} {f : α → β} {s t : Set α}
--     (hf : f '' s = f '' t) : s = t ↔ ∀ a ∈ s, ∀ b ∈ t, f s = f t

lemma IsMinimal.isGroebnerBasis_of_isMinimal_leadingTerm
    (hG : m.IsGroebnerBasis (m.leadingTerm '' G) (Ideal.span <| m.leadingTerm '' I))
    (hGsubset : G ⊆ I) :
    m.IsGroebnerBasis G I := by
  classical
  refine ⟨hGsubset, ?_⟩
  have eq := hG.2
  rw [Set.image_image] at eq
  apply le_antisymm
  · simp only [leadingTerm_leadingTerm] at eq
    rw [← eq]
    apply Ideal.span_mono
    rintro x ⟨p, hp, rfl⟩
    refine ⟨m.leadingTerm p, ?_, leadingTerm_leadingTerm _⟩
    apply Ideal.subset_span
    exact ⟨p, hp, rfl⟩
  · apply Ideal.span_mono
    apply Set.image_mono
    exact hGsubset

lemma IsMinimal.injOn_degree (hG' : hG.IsMinimal) : G.InjOn m.degree := by
  rw [Set.injOn_iff_pairwise_ne]
  exact hG'.pairwise.imp fun _ _ ↦ ne_of_not_le

lemma IsMinimal.minimal_degree (hG' : hG.IsMinimal) {g} (h : g ∈ G) :
    Minimal (· ∈ m.degree '' G) (m.degree g) := by
  by_contra!
  rw [not_minimal_iff_exists_lt <| Set.mem_image_of_mem _ h] at this
  obtain ⟨_, hqp, ⟨q, hqG, rfl⟩⟩ := this
  exact hG'.2 _ h _ hqG (by aesop) hqp.le

variable (hG) in
lemma IsMinimal.isMinimal_iff_monic_and_minimal_degree_and_injOn_leadingTerm :
    hG.IsMinimal ↔
      (∀ g ∈ G, m.Monic g) ∧ (∀ g ∈ G, Minimal (· ∈ m.degree '' G) (m.degree g)) ∧
      G.InjOn m.degree := by
  constructor
  · exact fun hG' ↦ ⟨hG'.1, fun _ ↦ hG'.minimal_degree, hG'.injOn_degree⟩
  intro h
  rw [isMinimal_def]
  refine ⟨h.1, fun p hp q hq hpq ↦ ?_⟩
  by_contra!
  exact h.2.2.ne hp hq hpq <| h.2.1 q hq |>.eq_of_le (Set.mem_image_of_mem _ hp) this

lemma IsMinimal.degree_image_eq_setOf_minimal (hG' : hG.IsMinimal) :
    m.degree '' G = {a | Minimal (· ∈ m.degree '' G) a} := by
  ext
  constructor
  · rintro ⟨p, hpG, rfl⟩
    exact hG'.minimal_degree hpG
  intro h
  exact h.prop

-- lemma IsMinimal.isGroebnerBasis_and_isMinimal_iff_monic_and_minimal_degree_and_injOn_leadingTerm
--     {R : Type*} [CommRing R] [Nontrivial R] {G : Set <| MvPolynomial σ R}
--     (I : Ideal <| MvPolynomial σ R) (hG : m.IsGroebnerBasis G I)
--     (h : ∀ g ∈ G, IsUnit (m.leadingCoeff g)) :
--     hG.IsMinimal ↔
--       (∀ g ∈ G, m.Monic g) ∧
--       m.degree '' G = {x | Minimal (· ∈ m.degree '' (I \ {(0 : MvPolynomial σ R)})) x} ∧
--       G.InjOn m.degree := by
--   rw [isMinimal_iff_monic_and_minimal_degree_and_injOn_leadingTerm]
--   constructor
--   · intro hG'
--     refine ⟨hG'.1, ?_, hG'.2.2⟩
--     have := hG.ideal_eq_span h

--     have := (isGroebnerBasis_iff_subset_and_degree_le_eq_and_degree_le (hG := h) ..).mp hG

--     sorry
--   · intro hG'
--     refine ⟨hG'.1, ?_, hG'.2.2⟩
--     simp_rw [hG'.2.1, Set.mem_setOf, minimal_minimal]
--     intro g hg
--     exact Set.ext_iff.mp hG'.2.1 (m.degree g) |>.mp <| Set.mem_image_of_mem _ hg

lemma IsMinimal.degree_image_eq_of_isMinimal [Nontrivial R]
    (hG' : hG.IsMinimal) {G₁ : Set (MvPolynomial σ R)} {hG₁ : m.IsGroebnerBasis G₁ I}
    (hG₁' : hG₁.IsMinimal) : m.degree '' G = m.degree '' G₁ := by
  rw [hG'.degree_image_eq_setOf_minimal, hG₁'.degree_image_eq_setOf_minimal, Set.ext_iff]
  simp_rw [Set.mem_setOf, ← ideal_span_monomial_image_eq_ideal_span_monomial_image_iff (R := R),
    Set.image_image]
  rw [
    ← m.span_leadingTerm_eq_span_monomial (fun _ h ↦ by simp [hG'.monic h |>.leadingCoeff_eq_one]),
    ← m.span_leadingTerm_eq_span_monomial (fun _ h ↦ by simp [hG₁'.monic h |>.leadingCoeff_eq_one]),
    ← hG.span_leadingTerm_image, ← hG₁.span_leadingTerm_image
  ]

lemma IsMinimal.isMinimal_of_isMinimal_leadingTerm
    {hG : m.IsGroebnerBasis (m.leadingTerm '' G) (Ideal.span <| m.leadingTerm '' I)}
    (hG' : hG.IsMinimal) (hGsubset : G ⊆ I) (hLT : G.InjOn m.degree) :
    (isGroebnerBasis_of_isMinimal_leadingTerm hG hGsubset).IsMinimal := by
  rw [IsMinimal.isMinimal_iff_monic_and_minimal_degree_and_injOn_leadingTerm] at ⊢ hG'
  aesop

lemma leadingCoeff_add_of_lt_right {f g : MvPolynomial σ R}
    (h : m.degree f ≺[m] m.degree g) :
    m.leadingCoeff (f + g) = m.leadingCoeff g :=
  add_comm f g ▸ leadingCoeff_add_of_lt h

-- this requires `R` to be nontrivial, or the reduced GB can be `∅` or `{0}`.
lemma IsReduced.unique {R : Type*} [CommRing R] [Nontrivial R]
    {G₁ G₂ : Set (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)}
    {hG₁ : m.IsGroebnerBasis G₁ I} (hG₁' : hG₁.IsReduced)
    {hG₂ : m.IsGroebnerBasis G₂ I} (hG₂' : hG₂.IsReduced) :
    G₁ = G₂ := by
  classical
  have : m.leadingTerm '' G₁ = m.leadingTerm '' G₂ := by
    rw [hG₁'.isMinimal.image_leadingTerm_eq_image_monomial_one,
      hG₂'.isMinimal.image_leadingTerm_eq_image_monomial_one,
      ← Set.image_image (monomial · (1 : R)) m.degree,
      ← Set.image_image (monomial · (1 : R)) m.degree]
    congr 1
    exact hG₁'.isMinimal.degree_image_eq_of_isMinimal hG₂'.isMinimal
  /- We suppose there exists `p₁ ∈ G₁` and `p₂ ∈ G₂` s.t. `m.degree p₁ = m.degree p₂` and `p₁ ≠ p₂`,
  and prove contradiction about remainder of `p₁ - p₂` that it is unique but can be both `0` and
  `p₁ - p₂`. This contradiction is easy to obtain in informal proof. -/
  ext p₁
  wlog hp₁ : p₁ ∈ G₁ ∧ p₁ ∉ G₂ generalizing G₁ G₂ with h
  · specialize h hG₂' hG₁' this.symm
    aesop
  obtain ⟨hp₁, hp₂'⟩ := hp₁
  exfalso
  obtain ⟨p₂, ⟨hp₂, hp₁₂⟩⟩ := Set.mem_image .. |>.mp <| this ▸ (Set.mem_image_of_mem _ hp₁)
  rw [isReduced_def] at hG₁' hG₂'
  simp [leadingTerm, monomial_eq_monomial_iff, (hG₂'.1 p₂ hp₂).ne_zero] at hp₁₂
  suffices rem_self : m.IsRemainder (p₁ - p₂) G₁ (p₁ - p₂) by
    have := I.sub_mem (Set.mem_of_subset_of_mem hG₁.1 hp₁) (Set.mem_of_subset_of_mem hG₂.1 hp₂)
    rw [← remainder_eq_zero_iff_mem_ideal hG₁ rem_self, sub_eq_zero] at this
    exact hp₂' <| this ▸ hp₂
  rw [IsRemainder.self_iff]
  rintro a ha q hq -
  replace ha' := Finset.mem_union.mp <| Finset.mem_of_subset (support_sub ..) ha
  by_cases hqp : m.degree q = m.degree p₁
  · apply not_imp_not.mpr (m.toSyn_monotone (a := m.degree q) (b := a))
    push_neg
    apply lt_of_le_of_ne
    · rcases ha' with ha | ha
      · exact hqp ▸ m.le_degree_of_mem_support ha
      · exact hqp ▸ hp₁₂.1 ▸ m.le_degree_of_mem_support ha
    contrapose! ha
    rw [m.toSyn.apply_eq_iff_eq] at ha
    simp_rw [leadingCoeff, hp₁₂.1, ← hqp] at hp₁₂
    simp [ha, hp₁₂.2]
  have hqnep : q ≠ p₁ := by contrapose! hqp; simp [hqp]
  rcases ha' with ha | ha
  · exact hG₁'.2 _ hp₁ _ ha _ hq hqnep
  obtain ⟨q', hq'⟩ := Set.mem_image .. |>.mp <| this ▸ (Set.mem_image_of_mem _ hq)
  simp [leadingTerm, monomial_eq_monomial_iff, (hG₁'.1 q hq).ne_zero] at hq'
  rw [← hq'.2.1]
  apply hG₂'.2 _ hp₂ _ ha _ hq'.1
  contrapose! hqp
  simp [← hq'.2.1, ← hp₁₂.1, hqp]

lemma MonomialOrder.degree_le_mul_left {σ R : Type*} [CommRing R] [IsDomain R]
    (m : MonomialOrder σ) (p q : MvPolynomial σ R) (hq : q ≠ 0) :
    m.degree p ≤ m.degree (p * q) := by
  by_cases hp : p = 0
  · rw [hp]
    simp
  · rw [m.degree_mul hp hq]
    exact le_self_add

lemma IsMinimal.isGroebnerBasis_image_isRemainder {R} [CommRing R]
    {G : Set (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)}
    {hG : m.IsGroebnerBasis G I}
    (hG' : hG.IsMinimal)
    (f : G → MvPolynomial σ R) (hf : ∀ g, m.IsRemainder g.val (G \ {g.val}) (f g)) :
    m.IsGroebnerBasis (Set.range f) I := by
    rw [IsMinimal] at hG'
    classical
    rcases hG with ⟨hG1, hG2⟩
    refine ⟨?_, ?_⟩
    · rintro _ ⟨g, rfl⟩
      have := (hf g).1
      obtain ⟨coef, h_eq, -⟩ := this
      have : f g = ↑g - (Finsupp.linearCombination (MvPolynomial σ R) fun b ↦ ↑b) coef := by
        simp_rw [h_eq]
        ring
      simp [this]
      apply Ideal.sub_mem
      ·
        apply hG1 g.2
      · dsimp
        apply Submodule.sum_mem
        intro c _
        apply Ideal.mul_mem_left
        apply hG1
        exact c.2.1
    ·
      rw [hG2]
      apply congr_arg Ideal.span
      ext x
      have lt_eq : ∀ (g : G), m.leadingTerm (f g) = m.leadingTerm g.val := by
        intro g
        by_contra h_ne
        let diff := ↑g - f g

        have fg_eq : f g = ↑g - diff := by
          exact Eq.symm (sub_sub_self (↑g) (f g))

        have h_deg_diff_lt : m.toSyn (m.degree diff) < m.toSyn (m.degree g.val) := by
            have := isRemainder_iff_degree (m := m) g (G \ {↑g}) (f g) <| by
              simp
              rintro b hbG -
              simp [(hG'.1 _ hbG).leadingCoeff_eq_one]
            obtain ⟨c, h_eq, b_deg⟩ := (this.mp <| hf g).left

            have h_diff_eq : diff =
            (Finsupp.linearCombination (MvPolynomial σ R) fun b ↦ ↑b) c := by
              exact sub_eq_iff_eq_add.mpr h_eq

            have h_all_lt : ∀ b ∈ c.support, m.toSyn (m.degree (b.val * c b)) <
              m.toSyn (m.degree g.val) := by
              intro b hb
              have h_le := b_deg b
              apply lt_of_le_of_ne h_le
              intro h_eq_deg
              have h_div : m.degree b.val ≤ m.degree g.val := by
                have h_eq_raw : m.degree (b.val * c b) = m.degree g.val := by
                  exact m.toSyn.injective h_eq_deg
                rw [← h_eq_raw]
                have cbn0 : c b ≠ 0 := by
                  exact Finsupp.mem_support_iff.mp hb
                have h_b_monic : m.Monic b.val := hG'.1 b.val b.2.1
                have lc1 : m.leadingCoeff b.val = 1 := by
                  rw [Monic] at h_b_monic
                  exact h_b_monic
                have lc2 : m.leadingCoeff (c b) ≠ 0 := by
                  rw [leadingCoeff]
                  simp [cbn0]
                have lc : m.leadingCoeff b.val * m.leadingCoeff (c b) ≠ 0 := by
                  simp [lc1, lc2]
                have : m.degree (b.val * c b) = m.degree b.val + m.degree (c b) := by
                   exact degree_mul_of_mul_leadingCoeff_ne_zero lc
                rw [this]
                simp
              exact hG'.2 g.val g.2 b.val b.2.1 b.2.2 h_div
            rw [h_diff_eq]
            apply lt_of_le_of_lt m.degree_sum_le
            have : c ≠ 0 := by
              intro h_c_zero
              rw [h_c_zero, map_zero] at h_diff_eq
              rw [h_diff_eq, sub_zero] at fg_eq
              rw [fg_eq] at h_ne
              exact h_ne rfl
            simp [mul_comm (c _)]
            rwa [← Finset.sup'_eq_sup, Finset.sup'_lt_iff]
            exact Finsupp.support_nonempty_iff.mpr this

        have h_degree : m.degree (f g) = m.degree g.val := by

          rw [fg_eq]
          rw [sub_eq_neg_add]
          apply m.degree_add_eq_right_of_lt
          rw [m.degree_neg]
          exact h_deg_diff_lt
        apply h_ne
        rw [leadingTerm]
        rw [leadingTerm]
        rw [h_degree]
        have : m.leadingCoeff (f g) = m.leadingCoeff g.val := by
          rw [fg_eq]
          rw [sub_eq_add_neg]
          have : m.degree (-diff) = m.degree diff := by rw [m.degree_neg]
          rw [←this] at h_deg_diff_lt
          exact leadingCoeff_add_of_lt h_deg_diff_lt
        rw [this]
      constructor
      ·
        simp only [Set.mem_image, Set.mem_range]

        intro h₁
        rcases h₁  with ⟨x₁, hx₁⟩
        obtain ⟨g_val, hg_in_G, rfl⟩ := hx₁
        use f ⟨x₁, g_val⟩
        constructor
        · use ⟨x₁, g_val⟩
        ·
          by_contra h_neq
          exact h_neq (lt_eq ⟨x₁, g_val⟩)
      ·
        rintro ⟨_, ⟨g, rfl⟩, rfl⟩
        use g.val, g.2
        rw [lt_eq g]

lemma IsReduced.isReduced_image_isRemainder_of_IsMinimal {R} [CommRing R]
    {G : Set (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)}
    {hG : m.IsGroebnerBasis G I}
    (hG' : hG.IsMinimal)
    (f : G → MvPolynomial σ R) (hf : ∀ g, m.IsRemainder g.val (G \ {g.val}) (f g)) :
    hG'.isGroebnerBasis_image_isRemainder f hf |>.IsReduced := by
    rw [isReduced_def]
    have lt_eq : ∀ (g : G), m.leadingTerm (f g) = m.leadingTerm g.val := by
      intro g
      by_contra h_ne
      let diff := ↑g - f g

      have fg_eq : f g = ↑g - diff := by
        exact Eq.symm (sub_sub_self (↑g) (f g))

      have h_deg_diff_lt : m.toSyn (m.degree diff) < m.toSyn (m.degree g.val) := by
          have := isRemainder_iff_degree (m := m) g (G \ {↑g}) (f g) <| by
            simp
            rintro b hbG -
            simp [(hG'.1 _ hbG).leadingCoeff_eq_one]
          obtain ⟨c, h_eq, b_deg⟩ := (this.mp <| hf g).left

          have h_diff_eq : diff =
          (Finsupp.linearCombination (MvPolynomial σ R) fun b ↦ ↑b) c := by
            exact sub_eq_iff_eq_add.mpr h_eq

          have h_all_lt : ∀ b ∈ c.support, m.toSyn (m.degree (b.val * c b)) <
            m.toSyn (m.degree g.val) := by
            intro b hb
            have h_le := b_deg b
            apply lt_of_le_of_ne h_le
            intro h_eq_deg
            have h_div : m.degree b.val ≤ m.degree g.val := by
                have h_eq_raw : m.degree (b.val * c b) = m.degree g.val := by
                  exact m.toSyn.injective h_eq_deg
                rw [← h_eq_raw]
                have cbn0 : c b ≠ 0 := by
                  exact Finsupp.mem_support_iff.mp hb
                have h_b_monic : m.Monic b.val := hG'.1 b.val b.2.1
                have lc1 : m.leadingCoeff b.val = 1 := by
                  rw [Monic] at h_b_monic
                  exact h_b_monic
                have lc2 : m.leadingCoeff (c b) ≠ 0 := by
                  rw [leadingCoeff]
                  simp [cbn0]
                have lc : m.leadingCoeff b.val * m.leadingCoeff (c b) ≠ 0 := by
                  simp [lc1, lc2]
                have : m.degree (b.val * c b) = m.degree b.val + m.degree (c b) := by
                   exact degree_mul_of_mul_leadingCoeff_ne_zero lc
                rw [this]
                simp
            exact hG'.2 g.val g.2 b.val b.2.1 b.2.2 h_div
          rw [h_diff_eq]
          apply lt_of_le_of_lt m.degree_sum_le
          have : c ≠ 0 := by
              intro h_c_zero
              rw [h_c_zero, map_zero] at h_diff_eq
              rw [h_diff_eq, sub_zero] at fg_eq
              rw [fg_eq] at h_ne
              exact h_ne rfl
          simp [mul_comm (c _)]
          rwa [← Finset.sup'_eq_sup, Finset.sup'_lt_iff]
          exact Finsupp.support_nonempty_iff.mpr this
      have h_degree : m.degree (f g) = m.degree g.val := by

        rw [fg_eq]
        rw [sub_eq_neg_add]
        apply m.degree_add_eq_right_of_lt
        rw [m.degree_neg]
        exact h_deg_diff_lt
      apply h_ne
      rw [leadingTerm]
      rw [leadingTerm]
      rw [h_degree]
      have : m.leadingCoeff (f g) = m.leadingCoeff g.val := by
        rw [fg_eq]
        rw [sub_eq_add_neg]
        have : m.degree (-diff) = m.degree diff := by rw [m.degree_neg]
        rw [←this] at h_deg_diff_lt
        exact leadingCoeff_add_of_lt h_deg_diff_lt
      rw [this]
    constructor
    ·
      intro p hp
      obtain ⟨g, rfl⟩ := hp
      have h : m.leadingTerm (f g) = m.leadingTerm ↑g := by
        exact lt_eq g
      unfold Monic
      rw [← m.leadingCoeff_leadingTerm (f g)]
      rw [h]
      have g_monic : m.Monic g.val := by
        exact hG'.1 g g.2
      unfold Monic at g_monic
      rw [m.leadingCoeff_leadingTerm]
      exact g_monic
    · intro p hp q hq r hr neq
      obtain ⟨g, rfl⟩ := hp
      obtain ⟨g', rfl⟩ := hr
      ·
        have h_ne : g' ≠ g := by
          rintro rfl
          exact neq rfl
        have h : m.leadingTerm (f g') = m.leadingTerm ↑g' := by
          exact lt_eq g'
        have deg_r_eq_g' : m.degree (f g') = m.degree g'.val := by
          simp [← degree_leadingTerm, h]
        rw [deg_r_eq_g']
        apply (hf g).2 q hq g'
        ·
          rw [Set.mem_diff, Set.mem_singleton_iff]
          constructor
          · exact g'.2
          · exact Subtype.coe_ne_coe.mpr h_ne
        · intro h_val_eq
          have g'_monic : m.Monic g'.val := hG'.1 g' g'.2
          rw [h_val_eq] at g'_monic
          simp_rw [Monic] at g'_monic
          simp at g'_monic
          have h_fg_zero : f g = 0 := by

            apply MvPolynomial.ext
            intro m
            rw [← mul_one (coeff m (f g))]
            rw [← g'_monic, mul_zero]
            rw [coeff_zero]

          rw [h_fg_zero] at hq
          rw [MvPolynomial.support_zero] at hq
          exact (List.mem_nil_iff q).mp hq

lemma IsReduced.exists_of_isGroebnerBasis {R} [CommRing R] {G : Set (MvPolynomial σ R)}
    {I : Ideal (MvPolynomial σ R)} (hG : m.IsGroebnerBasis G I)
    (hG' : ∀ g ∈ G, IsUnit (m.leadingCoeff g)) :
    ∃ (B : Set (MvPolynomial σ R)) (h : m.IsGroebnerBasis B I), h.IsReduced := by
  classical
  wlog! nontrivial : Nontrivial R
  · by_cases! hG : G = ∅
    · simp
    · use {0}
      simp
  -- monicized basis
  let monicized := Set.range fun (g : G) ↦ (hG' _ g.prop).unit⁻¹ • g.val
  have monicized_isGB : m.IsGroebnerBasis monicized I := hG.inv hG'
  have monicized_monic : ∀ g ∈ monicized, m.Monic g := by
    unfold monicized
    simp? says simp only [Set.mem_range, Subtype.exists, forall_exists_index]
    rintro _ _ hmemG rfl
    simp [Monic, Units.smul_def, smul_eq_C_mul]
    convert m.leadingCoeff_mul_of_right_mem_nonZeroDivisors _ _
    · simp [m.leadingCoeff_C]
    · simp
    exact (hG' _ hmemG).mem_nonZeroDivisors
  -- minimalized basis
  obtain ⟨minimal, minimal_subset_monic, injOn_degree, degree_minimal_eq⟩ :=
    Set.SurjOn.exists_subset_injOn_image_eq
      (s := monicized) (t := {x | Minimal (· ∈ (m.degree '' monicized)) x})
      (f := m.degree) (fun _ ↦ Minimal.prop)
  have minimal_isGB :=
    monicized_isGB.isGroebnerBasis_minimal (subset_trans minimal_subset_monic monicized_isGB.subset)
      (by simp [monicized_monic · <| minimal_subset_monic ·]) <| subset_of_eq <| by
        rw [degree_minimal_eq, sdiff_eq_left.mpr]
        rw [Set.disjoint_singleton_right]
        by_contra! h
        simpa [Monic] using monicized_monic _ h
  have minimal_isMinimal : IsMinimal (G := minimal) (I := I) _ :=
    IsMinimal.isMinimal_iff_monic_and_minimal_degree_and_injOn_leadingTerm minimal_isGB |>.mpr
      ⟨(monicized_monic · <| minimal_subset_monic ·), ?min, injOn_degree⟩
  case min =>
    intro g h
    simpa only [degree_minimal_eq, Set.mem_setOf, minimal_minimal] using
      Set.ext_iff.mp degree_minimal_eq (m.degree g) |>.mp (Set.mem_image_of_mem _ h)
  -- reduced basis
  have reduced := IsReduced.isReduced_image_isRemainder_of_IsMinimal minimal_isMinimal
    (fun g ↦ Exists.choose <|
      exists_isRemainder (m := m) g.val (B := minimal \ {g.val})
        (hB := by simp_intro .. [minimal_isMinimal.1]))
    (hf := by simp [Exists.choose_spec])
  exact ⟨_, _, reduced⟩

lemma IsReduced.exists_of_isGroebnerBasis₀ {R} [CommRing R] {G : Set (MvPolynomial σ R)}
    {I : Ideal (MvPolynomial σ R)} (hG : m.IsGroebnerBasis G I)
    (hG' : ∀ g ∈ G, IsUnit (m.leadingCoeff g) ∨ g = 0) :
    ∃ (B : Set (MvPolynomial σ R)) (h : m.IsGroebnerBasis B I), h.IsReduced := by
  apply exists_of_isGroebnerBasis (isGroebnerBasis_sdiff_singleton_zero .. |>.mpr hG)
  simp_intro .. [or_iff_not_imp_right.mp (hG' _ _)]

lemma IsReduced.exists_of_isGroebnerBasis' {k} [Field k] {I : Ideal (MvPolynomial σ k)} :
    ∃ (B : Set (MvPolynomial σ k)) (h : m.IsGroebnerBasis B I), h.IsReduced :=
  IsReduced.exists_of_isGroebnerBasis₀ (isGroebnerBasis_self (m := m) I) (by simp [em'])

theorem IsReduced.uniqueExists_of_isGroebnerBasis {R} [Nontrivial R] [CommRing R]
    {G : Set (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)}
    (hG : m.IsGroebnerBasis G I) (hG' : ∀ g ∈ G, IsUnit (m.leadingCoeff g)) :
    ∃! (B : Set (MvPolynomial σ R)), ∃ (h : m.IsGroebnerBasis B I),
      h.IsReduced := by
  obtain ⟨B, h, h'⟩ := IsReduced.exists_of_isGroebnerBasis hG hG'
  refine ⟨B, ⟨h, h'⟩, ?_⟩
  intro s
  simp only [forall_exists_index]
  intro hs hs'
  exact hs'.unique h'

theorem IsReduced.uniqueExists_of_isGroebnerBasis₀ {R} [Nontrivial R] [CommRing R]
    {G : Set (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)}
    (hG : m.IsGroebnerBasis G I) (hG' : ∀ g ∈ G, IsUnit (m.leadingCoeff g) ∨ g = 0) :
    ∃! (B : Set (MvPolynomial σ R)), ∃ (h : m.IsGroebnerBasis B I), h.IsReduced := by
  apply IsReduced.uniqueExists_of_isGroebnerBasis ((isGroebnerBasis_sdiff_singleton_zero ..).mpr hG)
  simp_intro .. [or_iff_not_imp_right.mp (hG' _ _)]

theorem IsReduced.uniqueExists_of_isGroebnerBasis' {k} [Field k] (I : Ideal (MvPolynomial σ k)) :
    ∃! (B : Set (MvPolynomial σ k)), ∃ (h : m.IsGroebnerBasis B I), h.IsReduced :=
  IsReduced.uniqueExists_of_isGroebnerBasis₀ (isGroebnerBasis_self (m := m) I) (by simp [em'])

-- lemma _root_.MonomialOrder.Embedding.isReduced_iff_isReduced_rename {σ' σ}
--     {m' : MonomialOrder σ'} {m : MonomialOrder σ}
--     (e : Embedding m' m) (p : MvPolynomial σ' R) {G : Set (MvPolynomial σ' R)}
--     (I : MvPolynomial σ' R) (hG : IsGroebnerBasis) :
--     m'.IsRemainder p B r ↔
--       m.IsRemainder (p.rename e) (rename e '' B) (r.rename e) :=
--   ⟨e.isRemainder_rename_of_isRemainder,

theorem IsReduced.def_minimal {k} [Field k] (G : Set (MvPolynomial σ k))
    (I : Ideal (MvPolynomial σ k)) :
    (∃ h : m.IsGroebnerBasis G I, h.IsReduced) ↔
    (∀ g, g ∈ G ↔
      m.Monic g ∧
      MaximalFor (fun p ↦ p ∈ I) (m.degree ·) g ∧
      ∀ p ∈ I, p ≠ 0 → m.degree p ≠ m.degree g → ∀ a ∈ g.support, ¬ m.degree p ≤ a) := by
  wlog h : ∃ (h : m.IsGroebnerBasis G I), h.IsReduced generalizing G
  · obtain ⟨G', hG', hG''⟩ := IsReduced.uniqueExists_of_isGroebnerBasis' (m := m) I
    specialize this G' hG'
    -- rw [← this]
    sorry
  sorry
  -- sorry
  -- constructor
  -- · intro ⟨hGB, hR⟩ g
  --   constructor
  --   · intro h
  --     refine ⟨hR.1 _ h, ?_, ?_⟩
  --     sorry
  --     rw [IsGroebnerBasis.isGroebnerBasis_iff_subset_and_degree_le_eq_and_degree_le'] at hGB
  -- sorry

theorem IsReduced.def_minimal' : (∃ h : m.IsGroebnerBasis G I, h.IsReduced) ↔
    ((∀ g ∈ G, m.Monic g) ∧
      m.degree '' G =
        { x | Minimal (· ∈ m.degree '' ((I : Set (MvPolynomial σ R)) \ {0})) x}) := sorry

lemma _root_.Filter.union_mem_of_mem {α} {a b : Set α} {f : Filter α} (ha : a ∈ f) (hb : b ∈ f) :
    a ∪ b ∈ f := by
  convert Filter.union_mem_sup ha hb
  simp

-- lemma _root_.Filter.inter_mem_of_mem {α} {a b : Set α} {f : Filter α} (ha : a ∈ f) (hb : b ∈ f) :
--     a ∩ b ∈ f := by
--   convert Filter.inter_mem ha hb
--   simp

lemma _root_.Filter.biUnion_mem_of_mem {α ι} {f : Filter α}
    {s : Set ι} {t : ι → Set α} (hs : s.Nonempty) (hs' : s.Finite)
    (h : ∀ i ∈ s, t i ∈ f) :
    ⋃ i ∈ s, t i ∈ f := by
  classical
  rw [← hs'.coe_toFinset] at ⊢ h hs
  generalize hs'.toFinset = s at ⊢ h hs
  rw [Finset.coe_nonempty] at hs
  induction s using Finset.induction_on with
  | empty => simp at hs
  | insert a' s' _ h' =>
    by_cases! hs' : s' = ∅
    · subst hs'
      simpa using h
    simp at h
    simpa using Filter.union_mem_of_mem h.1 (h' h.2 hs')

lemma _root_.Filter.sUnion_mem_of_mem {α} {f : Filter α}
    {s : Set (Set α)} (hs : s.Nonempty)
    (hs' : s.Finite) (h : ∀ a ∈ s, a ∈ f) : Set.sUnion s ∈ f := by
  classical
  rw [← hs'.coe_toFinset] at ⊢ h hs
  generalize hs'.toFinset = s at ⊢ h hs
  rw [Finset.coe_nonempty] at hs
  induction s using Finset.induction_on with
  | empty => simp at hs
  | insert a' s' _ h' =>
    by_cases! hs' : s' = ∅
    · subst hs'
      simpa using h
    simp at h
    simp [Filter.union_mem_of_mem h.1 (h' h.2 hs')]

-- bug?
lemma _root_.Filter.iUnion_mem_of_mem {α ι} {f : Filter α} [Fintype ι]
    [nomempty : Nonempty ι] {s : ι → Set α} (h : ∀ i : ι, s i ∈ f) : Set.iUnion s ∈ f := by
  classical
  have finite := Set.univ_finite_iff_nonempty_fintype (α := ι) |>.mpr <| .intro inferInstance
  rw [← Set.sUnion_range]
  apply f.sUnion_mem_of_mem
  · simp [Set.range_nonempty]
  · simp [Set.finite_range]
  simp [h]

-- lemma _root_.Filter.iUnion_mem_of_mem {α ι} {f : Filter α} [Fintype ι] [nomempty : Nonempty ι]
--     {s : ι → Set α} (h : ∀ i : ι, s i ∈ f) : Set.iUnion s ∈ f := by
--   classical
--   revert nomempty s h
--   apply Fintype.induction_subsingleton_or_nontrivial ι
--     (P := fun ι ↦ ∀ [inst : Nonempty ι] {s : ι → Set α}, (∀ (i : ι), s i ∈ f) → Set.iUnion s ∈ f)
--   · intro ι _ _ nonempty s h
--     -- todo: some related lemmas
--     rw [show s = fun _ ↦ s (Classical.choice nonempty) by ext; congr!, Set.iUnion_const]
--     exact h _
--   · intro ι' _ nontrivial ι nonempty f h
--     have := Classical.choice nonempty
--     specialize l
--     simp
--   sorry

theorem IsReduced.subset_limsup {k} [Field k] {I : Ideal (MvPolynomial σ k)} {α}
    {σ' : α → Type*} {m' : (a : α) → MonomialOrder (σ' a)}
    {f : Filter α} {e : (a : α) → (m' a).Embedding m}
    (hI : Set.univ = f.liminf (fun x ↦ Set.range (e x)))
    {G' : (a : α) → Set (MvPolynomial (σ' a) k)}
    (hG' : ∀ a, (m' a).IsGroebnerBasis (G' a) (I.comap <| rename (e a)))
    (hG'' : ∀ a, (hG' a).IsReduced)
    {G : Set (MvPolynomial σ k)} {hG₀ : m.IsGroebnerBasis G I} (hG : hG₀.IsReduced) :
    G ⊆ f.liminf fun a ↦ rename (e a) '' G' a := by
  classical
  have hG''' a : ∃ h : IsGroebnerBasis (G' a) (Ideal.comap (rename ⇑(e a)) I), h.IsReduced :=
    ⟨_, hG'' a⟩
  simp_rw [def_minimal] at ⊢ hG'''
  intro g
  simp [Filter.liminf_eq_iSup_iInf, eq_comm (a := Set.univ), Set.iUnion_eq_univ_iff,
    -MvPolynomial.mem_support_iff] at ⊢ hI
  intro h
  rw [IsReduced.def_minimal .. |>.mp ⟨_, hG⟩] at h
  refine ⟨Set.sInter (g.vars.image (hI · |>.choose)), ?_, ?_⟩
  · simp
    intro a ha
    obtain ⟨h, -⟩ := (hI _).choose_spec
    exact h
  intro a ha
  obtain ⟨g' , rfl⟩ :=
    MvPolynomial.exists_rename_eq_of_vars_subset_range g _ (e a).coe_injective <| by
      intro i hi
      simp at ha
      specialize ha i hi
      simpa using (hI i).choose_spec.2 _ ha
  refine ⟨g', ?_, rfl⟩
  rw [hG''' a g']
  simp [-MvPolynomial.mem_support_iff] at h ⊢
  split_ands
  · simpa using h.1
  · simpa using h.2.1.1
  · intro p hp
    simpa using h.2.1.2 hp
  intro p hp
  have := h.2.2 _ hp
  nth_rw 3 [(e a).degree_rename] at this
  simpa [-MvPolynomial.mem_support_iff, support_rename_of_injective (e a).coe_injective,
    Finsupp.mapDomain_le_mapDomain_iff_le (e a).coe_injective] using this

def IsReduced.isReduced_limsup {k} [Field k] {I : Ideal (MvPolynomial σ k)} {α}
    {σ' : α → Type*} {m' : (a : α) → MonomialOrder (σ' a)}
    {f : Filter α} [f.NeBot]
    {e : (a : α) → (m' a).Embedding m}
    (hI : Set.univ = f.liminf (fun x ↦ Set.range (e x)))
    {G' : (a : α) → Set (MvPolynomial (σ' a) k)}
    (hG' : ∀ a, (m' a).IsGroebnerBasis (G' a) (I.comap <| rename (e a)))
    (hG'' : ∀ a, (hG' a).IsReduced) :
    ∃ h : m.IsGroebnerBasis (f.liminf fun a ↦ rename (e a) '' G' a) I, h.IsReduced := by
  classical
  refine ⟨IsGroebnerBasis.of_subset
    (IsReduced.uniqueExists_of_isGroebnerBasis' I).choose_spec.1.choose ?_ ?_, ?_⟩
  · apply IsReduced.subset_limsup hI hG' hG''
    exact (IsReduced.uniqueExists_of_isGroebnerBasis' I).choose_spec.1.choose_spec
  · intro g
    simp [Filter.liminf_eq_iSup_iInf]
    intro s hs hs'
    obtain ⟨a, ha⟩ := Filter.NeBot.nonempty_of_mem ‹_› hs
    obtain ⟨g', hg', rfl⟩ := hs' a ha
    simpa using (hG' a).subset hg'
  simp_rw [isReduced_def, ← forall_and]
  simp [Filter.liminf_eq_iSup_iInf, eq_comm (a := Set.univ), Set.iUnion_eq_univ_iff,
    -MvPolynomial.mem_support_iff] at ⊢ hI
  intro g s hs hs'
  constructor
  · obtain ⟨a, ha⟩ := Filter.NeBot.nonempty_of_mem ‹_› hs
    obtain ⟨g', hg', hg'eq⟩ := hs' a ha
    specialize hG'' a
    simpa [← hg'eq] using hG''.1 g' hg'
  intro b hb p t ht ht' pneg
  -- obtain ⟨aₜ, haₜ⟩ := Filter.NeBot.nonempty_of_mem _ ht
  -- obtain ⟨p', hp', hp'eq⟩ := ht' aₜ haₜ
  obtain ⟨u, hu⟩ := Filter.NeBot.nonempty_of_mem ‹_› (Filter.inter_mem hs ht)
  have := Set.mem_of_mem_inter_left hu
  obtain ⟨g', hg', rfl⟩ := hs' u (Set.mem_of_mem_inter_left hu)
  obtain ⟨p', hp', rfl⟩ := ht' u (Set.mem_of_mem_inter_right hu)
  specialize hG'' u
  rw [isReduced_def] at hG''
  rw [support_rename_of_injective (e u).coe_injective, Finset.mem_image] at hb
  obtain ⟨b', hb', rfl⟩ := hb
  simpa [(e u).degree_rename, Finsupp.mapDomain_le_mapDomain_iff_le (e u).coe_injective] using
    hG''.2 g' hg' b' hb' p' hp' <|
      by simpa [rename_injective _ (e u).coe_injective |>.eq_iff] using pneg

-- theorem IsReduced.isReduced_limsup {k} [Field k] {I : Ideal (MvPolynomial σ k)} {α}
--     {f : Filter α} {σ' : α → Type*} {m' : (a : α) → MonomialOrder (σ' a)}
--     {e : (a : α) → (m' a).Embedding m} {G' : (a : α) → Set (MvPolynomial (σ' a) k)} :
--     (∀ a, ∃ h : (m' a).IsGroebnerBasis (G' a) (I.comap <| rename (e a)), h.IsReduced) ↔
--       ∃ h : m.IsGroebnerBasis (f.liminf fun a ↦ rename (e a) '' G' a) I, h.IsReduced := by


end MonomialOrder.IsGroebnerBasis
