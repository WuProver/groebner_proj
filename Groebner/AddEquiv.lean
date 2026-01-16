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
lemma withBotCongr_toEquiv_eq : e.withBotCongr.toEquiv = e.toEquiv.withBotCongr := rfl

@[to_dual (attr := simp)]
lemma withBotCongr_toAddHom_eq : e.withBotCongr.toAddHom = e.toAddHom.withBotMap := rfl

@[to_dual (attr := simp)]
lemma withBotCongr_apply (a : WithBot α) : e.withBotCongr a = a.map e := rfl

@[to_dual (attr := simp)]
lemma withBotCongr_refl : withBotCongr (AddEquiv.refl α) = AddEquiv.refl _ :=
  AddEquiv.ext <| congr_fun WithBot.map_id

@[to_dual (attr := simp)]
theorem withBotCongr_symm : e.symm.withBotCongr = e.withBotCongr.symm :=
  rfl

@[to_dual (attr := simp)]
theorem withBotCongr_trans :
    (e₁.trans e₂).withBotCongr = e₁.withBotCongr.trans e₂.withBotCongr := by
  ext x
  simp

end AddEquiv
