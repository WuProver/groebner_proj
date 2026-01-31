module

public import Mathlib

public section

namespace Finsupp

lemma mapDomain_le_iff_le_of_injective {ι : Type*} {κ : Type*} {α : Type*}
    [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α] {f : ι → κ} (h : f.Injective)
    (a b : ι →₀ α) : a.mapDomain f ≤ b.mapDomain f ↔ a ≤ b := by
  classical
  refine ⟨?_, (Finsupp.mapDomain_mono (f := f) (α := α) ·)⟩
  intro h'
  rw [Finsupp.le_def] at h' ⊢
  intro i
  simpa [Finsupp.mapDomain_apply h] using h' (f i)

-- #check Finsupp.mapDomain_appl
-- theorem sum_tsub_index {M N α} [DecidableEq α] [AddZeroClass M] [AddCommMonoid N] {f g : α →₀ M}
--     {h : α → M → N} (h_zero : ∀ a ∈ f.support ∪ g.support, h a 0 = 1)
--     (h_add : ∀ a ∈ f.support ∪ g.support, ∀ (b₁ b₂), h a (b₁ + b₂) = h a b₁ * h a b₂) :
--     (f + g).prod h = f.prod h * g.prod h := by

open Finset

-- @[to_additive]
-- theorem prod_zipWith_index {σ α α' β} [DecidableEq σ]
--     [Zero α] [Zero α'] [Zero β] [CommMonoid β]
--     {a : σ →₀ α} {b : σ →₀ α} {f : α → α → α'} (hf : f 0 0 = 0)
--     {h : σ → α' → β} {h' : σ → α → β}
--     (h_zero : ∀ x ∈ a.support ∪ b.support, h' x 0 = 1)
--     (h_add : ∀ x ∈ a.support ∪ b.support, ∀ (b₁ b₂), h x (f b₁ b₂) = h' x b₁ * h' x b₂) :
--     (Finsupp.zipWith f hf a b).prod h = a.prod h' * b.prod h' := by
--   have (x) (hx : x ∈ a.support ∪ b.support) : h x 0 = 1 := by
--     simpa [hf, h_zero x hx] using h_add x hx 0 0
--   rw [Finsupp.prod_of_support_subset a subset_union_left h' h_zero,
--     Finsupp.prod_of_support_subset b subset_union_right h' h_zero,
--     ← Finset.prod_mul_distrib,
--     Finsupp.prod_of_support_subset (Finsupp.zipWith f hf a b) support_zipWith h this]
--   exact Finset.prod_congr rfl fun x hx => by apply h_add x hx

-- @[to_additive]
-- theorem prod_zipWith_index {σ α₁ α₂ α' β} [DecidableEq σ]
--     [Zero α₁] [Zero α₂] [Zero α'] [CommMonoid β]
--     {a : σ →₀ α₁} {b : σ →₀ α₂} {f : α₁ → α₂ → α'} (hf : f 0 0 = 0)
--     {h' : σ → α' → β} {h₁ : σ → α₁ → β} {h₂ : σ → α₂ → β}
--     (h₁_zero : ∀ x ∈ a.support ∪ b.support, h₁ x 0 = 1)
--     (h₂_zero : ∀ x ∈ a.support ∪ b.support, h₂ x 0 = 1)
--     (h_add : ∀ x ∈ a.support ∪ b.support, ∀ (b₁ b₂), h' x (f b₁ b₂) = h₁ x b₁ * h₂ x b₂) :
--     (Finsupp.zipWith f hf a b).prod h' = a.prod h₁ * b.prod h₂ := by
--   have (x) (hx : x ∈ a.support ∪ b.support) : h' x 0 = 1 := by
--     simpa [hf, h₁_zero x hx, h₂_zero x hx] using h_add x hx 0 0
--   rw [Finsupp.prod_of_support_subset a subset_union_left h₁ h₁_zero,
--     Finsupp.prod_of_support_subset b subset_union_right h₂ h₂_zero,
--     ← Finset.prod_mul_distrib,
--     Finsupp.prod_of_support_subset (Finsupp.zipWith f hf a b) support_zipWith h' this]
--   exact Finset.prod_congr rfl fun x hx => by apply h_add x hx

-- @[to_additive]
-- theorem prod_zipWith_index' {σ α α' β} [DecidableEq σ]
--     [Zero α] [Zero α'] [CommMonoid β]
--     {a : σ →₀ α} {b : σ →₀ α} {f : α → α → α'} (hf : f 0 0 = 0)
--     {h : σ → α' → β} {h' : σ → α → β}
--     (h_zero : ∀ x ∈ a.support ∪ b.support, h' x 0 = 1)
--     (h_add : ∀ x ∈ a.support ∪ b.support, ∀ (b₁ b₂), h x (f b₁ b₂) = h' x b₁ * h' x b₂) :
--     (Finsupp.zipWith f hf a b).prod h = a.prod h' * b.prod h' :=
--   prod_zipWith_index hf h_zero h_zero h_add

-- @[to_additive]
-- theorem prod_add_index_ {α M N} [DecidableEq α] [AddZeroClass M] [CommMonoid N] {f g : α →₀ M}
--     {h : α → M → N} (h_zero : ∀ a ∈ f.support ∪ g.support, h a 0 = 1)
--     (h_add : ∀ a ∈ f.support ∪ g.support, ∀ (b₁ b₂), h a (b₁ + b₂) = h a b₁ * h a b₂) :
--     (f + g).prod h = f.prod h * g.prod h :=
--   prod_zipWith_index' (zero_add (M := M) 0) h_zero h_add

lemma mapDomain_tsub_mapDomain {σ α κ} [AddCommMonoid α] [PartialOrder α] [CanonicallyOrderedAdd α]
    [Sub α] [OrderedSub α] {f : σ → κ} (h : f.Injective) (a b : σ →₀ α) :
    a.mapDomain f - b.mapDomain f = (a - b).mapDomain f := by
  ext y
  rw [tsub_apply]
  wlog h : y ∈ Set.range f
  · simp [mapDomain_notin_range _ _ h]
  obtain ⟨x, rfl⟩ := h
  simp [mapDomain_apply h _ x]

end Finsupp
