-- submitted: https://github.com/leanprover-community/mathlib4/pull/34756
module

public import Mathlib

@[expose] public section

namespace AddEquiv

variable {α β γ} [Add α] [Add β] [Add γ] (e e₁ : α ≃+ β) (e₂ : β ≃+ γ)

@[to_dual]
def withBotCongr : WithBot α ≃+ WithBot β := {
  e.toEquiv.withBotCongr with
  map_add' := e.toAddHom.withBotMap.map_add'
}

@[to_dual (attr := simp)]
lemma coe_withBotCongr : e.withBotCongr = WithBot.map e := rfl

@[to_dual]
lemma coe_withBotCongr_eq_equiv_withBotCongr : e.withBotCongr = (e : α ≃ β).withBotCongr := rfl

@[to_dual]
lemma coe_withBotCongr_eq_addHom_withBotMap : e.withBotCongr = (e : AddHom α β).withBotMap := rfl

@[to_dual]
lemma withBotCongr_apply (a : WithBot α) : e.withBotCongr a = a.map e := rfl

@[to_dual (attr := simp)]
lemma withBotCongr_refl : (AddEquiv.refl α).withBotCongr = AddEquiv.refl _ :=
  AddEquiv.ext <| congr_fun WithBot.map_id

@[to_dual (attr := simp)]
theorem withBotCongr_symm : e.symm.withBotCongr = e.withBotCongr.symm := rfl

@[to_dual (attr := simp)]
theorem withBotCongr_trans :
    (e₁.trans e₂).withBotCongr = e₁.withBotCongr.trans e₂.withBotCongr := by
  ext x
  simp

end AddEquiv
