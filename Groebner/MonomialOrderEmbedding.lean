module

public import Mathlib
public import Groebner.MulEquiv

@[expose] public section

def RelHom.onFun {α : Type*} {β : Type*} (r : β → β → Prop) (f : α → β) :
    RelHom (Function.onFun r f) r where
  toFun := f
  map_rel' := by simp

@[simp] def RelHom.coe_onFun {α : Type*} {β : Type*} {r : β → β → Prop} (f : α → β) :
    RelHom.onFun r f = f := rfl

instance _root_.IsWellFounded.onFun {α : Type*} {β : Type*} (r : β → β → Prop) (f : α → β)
    [wfl : IsWellFounded β r] :
    IsWellFounded α (Function.onFun r f) := RelHomClass.isWellFounded (RelHom.onFun r f)

namespace MonomialOrder

open MvPolynomial

variable {σ' : Type*} (m' : MonomialOrder σ') {σ : Type*} (m : MonomialOrder σ) (f : σ' → σ)

set_option linter.unusedVariables false in
def ofInjective.Syn (m : MonomialOrder σ) {σ' : Type*} (f : σ' → σ) := σ' →₀ ℕ

noncomputable instance ofInjective.acm' : AddCommMonoid (Syn m f) :=
  inferInstanceAs <| AddCommMonoid <| σ' →₀ ℕ

def ofInjective.toSyn' (m : MonomialOrder σ) {σ' : Type*} (f : σ' → σ) : (σ' →₀ ℕ) ≃+ (Syn m f) :=
  AddEquiv.refl (σ' →₀ ℕ)

open ofInjective in
noncomputable def ofInjective {σ' : Type*} {f : σ' → σ} (hf : f.Injective) :
    MonomialOrder σ' :=
  letI hom := m.toSyn.toAddMonoidHom.comp <| Finsupp.mapDomain.addMonoidHom f
  letI map := m.toSyn ∘ Finsupp.mapDomain f
  haveI map_injective : Function.Injective map := by
    simp [m.toSyn.injective, Finsupp.mapDomain_injective hf, map]
  letI toSyn := AddEquiv.ofLeftInverse'' hom (Set.rangeSplitting hom) <| by
    rwa [AddMonoidHom.mrangeRestrict_eq_rangeFactorization, Set.leftInverse_rangeFactorization]
  letI lo : LinearOrder (Syn m f) := LinearOrder.lift' map map_injective
  { syn := Syn m f
    toSyn : (σ' →₀ ℕ) ≃+ (Syn m f) := toSyn' m f
    toSyn_monotone := by
      intro a b h
      apply m.toSyn_monotone
      exact Finsupp.mapDomain_mono h
    ioam := {
      add_le_add_left a b hab c := by
        convert_to map _ ≤ map _ at hab
        convert_to map (HAdd.hAdd (α := σ' →₀ ℕ) _ _) ≤ map (HAdd.hAdd (α := σ' →₀ ℕ) _ _)
        simpa [map, Finsupp.mapDomain_add, AddEquiv.map_add] using hab
    }
    wf := -- show WellFoundedLT (Syn m f) from -- why it doesn't work without `show` or `by exact`?
      by exact inferInstanceAs <| IsWellFounded (Syn m f) fun x1 x2 ↦ map x1 < map x2
  }

structure Embedding where
  toFun : σ' → σ
  toFun_injective : toFun.Injective
  monotone' : Monotone (m.toSyn ∘ Finsupp.mapDomain toFun ∘ m'.toSyn.symm)

namespace Embedding

variable {m' m} (e : Embedding m' m) {R} [CommSemiring R]
variable (p q : MvPolynomial σ' R)

instance instFunLike : FunLike (Embedding m' m) σ' σ where
  coe := Embedding.toFun
  coe_injective' e₁ e₂ h := by
    convert_to (Embedding.mk _ _ _) = ⟨_, _, _⟩
    congr

@[ext] lemma ext {e₁ e₂ : Embedding m' m} (h : ⇑e₁ = ⇑e₂) : e₁ = e₂ :=
  (instFunLike ..).coe_injective' h

@[simp] lemma toFun_eq_coe : e.toFun = ⇑e := rfl

lemma monotone : Monotone (m.toSyn ∘ Finsupp.mapDomain e ∘ m'.toSyn.symm) := e.monotone'

lemma coe_injective : Function.Injective e := e.toFun_injective

def toStrictMono : StrictMono (m.toSyn ∘ Finsupp.mapDomain e ∘ m'.toSyn.symm) :=
  e.monotone'.strictMono_of_injective <| by
    simpa using Finsupp.mapDomain_injective <| e.coe_injective

noncomputable def toOrderEmbedding : OrderEmbedding m'.syn m.syn := .ofStrictMono _ e.toStrictMono

def le_iff_le (a b : m'.syn) :
    Finsupp.mapDomain e (m'.toSyn.symm a) ≼[m] Finsupp.mapDomain e (m'.toSyn.symm b) ↔ a ≤ b :=
  e.toOrderEmbedding.le_iff_le

def le_iff_le' (a b : σ' →₀ ℕ) :
    Finsupp.mapDomain e a ≼[m] Finsupp.mapDomain e b ↔ a ≼[m'] b := by
  nth_rw 1 [← m'.toSyn.symm_apply_apply a, ← m'.toSyn.symm_apply_apply b]
  exact e.le_iff_le ..

def lt_iff_lt (a b : m'.syn) :
    Finsupp.mapDomain e (m'.toSyn.symm a) ≺[m] Finsupp.mapDomain e (m'.toSyn.symm b) ↔ a < b :=
  e.toOrderEmbedding.lt_iff_lt

def lt_iff_lt' (a b : σ' →₀ ℕ) :
    Finsupp.mapDomain e a ≺[m] Finsupp.mapDomain e b ↔ a ≺[m'] b := by
  nth_rw 1 [← m'.toSyn.symm_apply_apply a, ← m'.toSyn.symm_apply_apply b]
  exact e.lt_iff_lt ..

variable (m) in
def ofInjective {f : σ' → σ} (hf : f.Injective) : Embedding (m.ofInjective hf) m where
  toFun := f
  toFun_injective := hf
  monotone' := by
    intro a b h
    letI map := m.toSyn ∘ Finsupp.mapDomain f
    convert_to map _ ≤ map _ at ⊢ h
    simpa [MonomialOrder.ofInjective, ofInjective.toSyn', map] using h

variable (m) in
lemma ofInjective_coe {f : σ' → σ} (hf : f.Injective) : ofInjective m hf = f := rfl

lemma degree_rename : m.degree (p.rename e) = (m'.degree p).mapDomain e := by
  classical
  simp? [degree, support_rename_of_injective e.coe_injective] says
    simp only [degree, support_rename_of_injective e.coe_injective, Finset.sup_image]
  convert_to
    m.toSyn.symm ((p.support.map m'.toSyn.toEmbedding).sup
      (m.toSyn ∘ Finsupp.mapDomain ⇑e ∘ m'.toSyn.symm)) = _
  · simp [Function.comp_def]
  · simp [← Finset.comp_sup_eq_sup_comp_of_is_total _ e.monotone (by simp)]

@[simp]
lemma leadingCoeff_rename : m.leadingCoeff (p.rename e) = m'.leadingCoeff p := by
  simp [leadingCoeff, ← coeff_rename_mapDomain _ (e.coe_injective), degree_rename]

lemma leadingTerm_rename : m.leadingTerm (p.rename e) = (m'.leadingTerm p).rename e := by
  simp [leadingTerm, degree_rename, rename_monomial]

end Embedding

end MonomialOrder
