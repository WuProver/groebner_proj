module

public import Lean

public section

@[simp]
theorem and_imp_iff_and {a b : Prop} : a ∧ (a → b) ↔ a ∧ b :=
  ⟨fun ⟨a, b'⟩ ↦ ⟨a, b' a⟩, fun ⟨a, b⟩ ↦ ⟨a, fun _ ↦ b⟩⟩

@[simp]
theorem imp_and_iff_and {a b : Prop} : (a → b) ∧ a ↔ b ∧ a :=
  ⟨fun ⟨b', a⟩ ↦ ⟨b' a, a⟩, fun ⟨b, a⟩ ↦ ⟨fun _ ↦ b, a⟩⟩
