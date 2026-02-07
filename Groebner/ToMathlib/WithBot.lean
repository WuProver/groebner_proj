module
public import Mathlib

namespace WithBot

variable {α β} {f : α → β} (a b : WithBot α)

@[to_dual]
public theorem map_add' [Add α] [Add β] (hf : ∀ x y, f (x + y) = f x + f y) :
    (a + b).map f = a.map f + b.map f := by
  induction a
  · exact (bot_add _).symm
  · induction b
    · exact (add_bot _).symm
    · rw [map_coe, map_coe, ← coe_add, ← coe_add, ← hf]
      rfl

@[to_dual]
public lemma map_lt_iff [LT α] [LT β] (f : α → β) (mono_iff : ∀ {a b}, f a < f b ↔ a < b) :
    a.map f < b.map f ↔ a < b := by cases a <;> cases b <;> simp [mono_iff]

end WithBot
