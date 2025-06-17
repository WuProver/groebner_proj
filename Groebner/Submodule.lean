import Mathlib.LinearAlgebra.Span.Basic
import Mathlib

namespace Submodule
open Set

variable (R : Type*) {M : Type*}
variable [Semiring R] [AddCommMonoid M] [Module R M]
variable (s : Set M)


-- to Mathlib
/--
  $$
    \langle G \rangle = \langle G \setminus \{0\} \rangle
  $$
-/
@[simp]
lemma span_sdiff_singleton_zero._mathlib:
  span R (s \ {0}) = span R s := by
  by_cases h : 0 ∈ s
  ·rw [←span_insert_zero, (by simp [h] : insert 0 (s \ {0}) = s)]
  ·simp [h]

-- merged: https://github.com/leanprover-community/mathlib4/pull/24648
lemma subset_span_finite_of_subset_span._mathlib (s : Set M)
  (t : Finset M) (ht : (t : Set M) ⊆ span R s) :
  ∃ (s' : Finset M), ↑s' ⊆ s ∧ (t : Set M) ⊆ span R (s' : Set M) := by
  classical
  have t' : Finset t := Finset.subtype (· ∈ t) t
  let s' := (Finset.subtype (· ∈ t) t).biUnion fun ⟨m, hm⟩ ↦
      Exists.choose <| Submodule.mem_span_finite_of_mem_span
        <| Set.mem_of_subset_of_mem ht hm
  use s'
  have : ↑s' ⊆ s := by
    unfold s'
    simp
    intro a ha
    generalize_proofs h
    exact h.choose_spec.1
  use this
  unfold s'
  simp
  intro m
  simp
  intro hm
  generalize_proofs h
  rw [span_iUnion]
  apply mem_iSup_of_mem (p := fun x ↦ span R (↑(h x).choose : Set M)) ⟨m, hm⟩
  exact (h (Subtype.mk m hm)).choose_spec.2

-- submitted: https://github.com/leanprover-community/mathlib4/pull/24651
theorem fg_span_iff_fg_span_finset_subset (s : Set M) :
  (span R s).FG ↔ ∃ (s' : Finset M), ↑s' ⊆ s ∧ span R s = span R s' := by
  unfold FG
  constructor
  ·
    intro ⟨s'', hs''⟩
    obtain ⟨s', hs's, hss'⟩ := subset_span_finite_of_subset_span (hs'' ▸ subset_span)
    refine ⟨s', hs's, ?_⟩
    apply le_antisymm
    · rwa [← hs'', Submodule.span_le]
    · rw [Submodule.span_le]
      trans s
      exact hs's
      exact subset_span
  · intro ⟨s', _, h⟩
    exact ⟨s', h.symm⟩

theorem mem_of_mem_of_le {x : M} {s t : Submodule R M} (hx : x ∈ s) (h : s ≤ t) : x ∈ t :=
  Set.mem_of_mem_of_subset hx h

theorem mem_span_of_mem {x : M} {s : Set M} (hx : x ∈ s) : x ∈ span R s :=
  mem_span.mpr fun _ h ↦ h hx

#find_home! mem_of_mem_of_le


end Submodule
