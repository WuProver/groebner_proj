import Mathlib.Data.Set.Finite.Basic

namespace Set

-- theorem nbij_iff_bijOn_coe {α β : Type*} {s : Finset α} {t : Finset β} {i : α → β} :
--     (∀ a ∈ s, i a ∈ t) ∧
--     InjOn i s ∧ SurjOn i ↑s ↑t ↔
--     Set.BijOn i s t := refl _

-- theorem nbij_of_bijOn_coe {α β : Type*} {s : Finset α} {t : Finset β} {i : α → β}
--     (h : Set.BijOn i s t) :
--     (∀ a ∈ s, i a ∈ t) ∧
--     InjOn i s ∧ SurjOn i ↑s ↑t := h

-- theorem nbij_of_bijOn_coe' {α β : Type*} {a : Prop} {s : Finset α} {t : Finset β} {i : α → β}
--     (h : Set.BijOn i s t) (h' : (∀ a ∈ s, i a ∈ t) → InjOn i ↑s → SurjOn i ↑s ↑t → a) :
--     a :=
--   h' h.mapsTo h.injOn h.surjOn

-- theorem nbij_iff_bijOn_finite {α β : Type*} {s : Set α} {t : Set β}
--     {i : α → β} (hs : s.Finite) (ht : t.Finite) :
--       (∀ a ∈ hs.toFinset, i a ∈ ht.toFinset) ∧
--         InjOn i hs.toFinset ∧
--         SurjOn i ↑hs.toFinset ↑ht.toFinset ↔
--     Set.BijOn i s t := by
--   simp
--   rfl

-- theorem nbij_of_bijOn_right_finite {α β : Type*} {s : Set α} {t : Set β}
--     {i : α → β} (ht : t.Finite) (h : Set.BijOn i s t) :
--     let hs : s.Finite := Set.Finite.of_finite_image (h.image_eq.symm ▸ ht) h.injOn
--     (∀ a ∈ hs.toFinset, i a ∈ ht.toFinset) ∧
--     InjOn i hs.toFinset ∧ SurjOn i ↑hs.toFinset ↑ht.toFinset := by
--   simpa

-- theorem nbij_of_bijOn_right_finite' {α β : Type*} {a : (α → β) → Prop} {s : Set α} {t : Set β}
--     {i : α → β} (ht : t.Finite) (h : Set.BijOn i s t)
--     (h' : let hs : s.Finite := Set.Finite.of_finite_image (h.image_eq.symm ▸ ht) h.injOn
--       ∀ (i' : α → β), (∀ a ∈ hs.toFinset, i' a ∈ ht.toFinset) → InjOn i' hs.toFinset →
--       SurjOn i' ↑hs.toFinset ↑ht.toFinset → a i') :
--     a i :=
--   let h := nbij_of_bijOn_right_finite ht h
--   h' i h.1 h.2.1 h.2.2

-- theorem nbij_of_bijOn_left_finite {α β : Type*} {s : Set α} {t : Set β}
--     {i : α → β} (hs : s.Finite) (h : Set.BijOn i s t) :
--     let ht : t.Finite := h.image_eq.symm ▸ Set.Finite.image i hs
--     (∀ a ∈ hs.toFinset, i a ∈ ht.toFinset) ∧
--     InjOn i hs.toFinset ∧ SurjOn i ↑hs.toFinset ↑ht.toFinset := by
--   simpa

-- theorem nbij_of_bijOn_left_finite' {α β : Type*} {a : (α → β) → Prop} {s : Set α} {t : Set β}
--     {i : α → β} (hs : s.Finite) (h : Set.BijOn i s t)
--     (h' : let ht : t.Finite := h.image_eq.symm ▸ Set.Finite.image i hs
--       ∀ (i' : α → β), (∀ a ∈ hs.toFinset, i' a ∈ ht.toFinset) → InjOn i' hs.toFinset →
--       SurjOn i' ↑hs.toFinset ↑ht.toFinset → a i') :
--     a i := by
--   let h := nbij_of_bijOn_left_finite hs h
--   exact h' i h.1 h.2.1 h.2.2

-- submitted: https://github.com/leanprover-community/mathlib4/pull/26013
lemma card_bijOn {α β : Type*} {s : Finset α} {t : Finset β}
    (i : α → β) (h : Set.BijOn i s t) : s.card = t.card :=
  Finset.card_nbij i h.mapsTo h.injOn h.surjOn

/--
Let $f: \alpha \to \beta$ be a function and $s \subseteq \alpha$ a subset with finite image $f(s)$. Then there exists a finite subset $s' \subseteq_{\text{fin}} s$ such that:

- $s' \subseteq s$ (subset relation)
- $f(s') = f(s)$ (image equality)
- $|s'| = |f(s)|$ (cardinality preservation)
-/
-- submitted: https://github.com/leanprover-community/mathlib4/pull/26013
lemma finset_subset_preimage_of_finite_image {α : Type*} {β : Type*}
    {s : Set α} {f : α → β} (h : (f '' s).Finite) :
    ∃ (s' : Finset α), ↑s' ⊆ s ∧ f '' s' = f '' s ∧ s'.card = h.toFinset.card := by
  have ⟨s', hs', hs'₁⟩ := Set.exists_subset_bijOn s f
  have h' := Set.Finite.of_finite_image (hs'₁.image_eq.symm ▸ h) hs'₁.injOn
  use h'.toFinset
  rw [Set.Finite.coe_toFinset]
  exact ⟨hs', hs'₁.image_eq, card_bijOn _ <| h.coe_toFinset.symm ▸ h'.coe_toFinset.symm ▸ hs'₁⟩
