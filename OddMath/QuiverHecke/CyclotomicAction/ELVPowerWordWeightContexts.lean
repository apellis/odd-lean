import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordEvaluation
import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordContexts

/-! # Chosen right contexts on the full-coefficient weight word family

SwappedVacuumCoordinates §§4–6: iterate the given E functors and existing
single-append charts on arbitrary full old-Hom arrows.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerWordWeightContexts
open CyclotomicAction CyclotomicCrossingTensor
universe u
section Weight
variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X)
/-- The literal successive target weights along a right context. -/
def contextWeight (x : X) : List I → X
  | [] => x
  | i :: η => contextWeight (x + D.α i) η
end Weight

private theorem comparison_step {C B E : Type*} [Category* C] [Category* B] [Category* E]
    (K : C ⥤ B) (H : B ⥤ E) {P Q : C} {V W : B} {S T : E}
    (e : K.obj P ≅ V) (f : K.obj Q ≅ W) (c : H.obj V ≅ S) (d : H.obj W ≅ T)
    (x : P ⟶ Q) (y : V ⟶ W) (z : S ⟶ T)
    (h₀ : K.map x ≫ f.hom = e.hom ≫ y) (h₁ : H.map y ≫ d.hom = c.hom ≫ z) :
    (K ⋙ H).map x ≫ (H.mapIso f ≪≫ d).hom = (H.mapIso e ≪≫ c).hom ≫ z := by
  simp only [Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Category.assoc, ← H.map_comp, h₀, H.map_comp, Category.assoc, h₁]

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)
  (Λ : X)
local notation "N" => PowerWordContent.powerBound D cutoff L

/-- Actual successive E functors, at their actual successive weights. -/
def contextFunctor (x : X) : (η : List I) → ELVWeightProduct D Sc cutoff N Λ x ⥤
    ELVWeightProduct D Sc cutoff N Λ (contextWeight D x η)
  | [] => 𝟭 _
  | i :: η => elvEFunctor D Sc cutoff N i Λ (rfl : x + D.α i = x + D.α i) ⋙
      contextFunctor (x + D.α i) η

omit [Fintype I] in
private theorem append_weight (ν : List I) (i : I) (x : X)
    (hx : x = PowerWordWeight.wordWeight D Λ ν) :
    x + D.α i = PowerWordWeight.wordWeight D Λ (ν ++ [i]) :=
  (congrArg (fun y => y + D.α i) hx).trans (PowerWordWeight.wordWeight_append D Λ ν i)

omit [Fintype I] in

/-- Only the existing whole append comparisons are composed. -/
def contextIso (ν : List I) (x : X) (hx : x = PowerWordWeight.wordWeight D Λ ν) :
    (η : List I) → (contextFunctor D Sc cutoff L Λ x η).obj (PowerWordWeight.wordFamily D Sc cutoff L Λ x ν) ≅
      PowerWordWeight.wordFamily D Sc cutoff L Λ (contextWeight D x η) (PowerWordContexts.extendedWord ν η)
  | [] => Iso.refl _
  | i :: η => (contextFunctor D Sc cutoff L Λ (x + D.α i) η).mapIso
      (PowerWordWeightCross.appendIsoAtWeights D Sc cutoff L Λ ν i x (x + D.α i) hx
        (append_weight D Λ ν i x hx) rfl) ≪≫
      contextIso (ν ++ [i]) (x + D.α i) (append_weight D Λ ν i x hx) η

private def contextEquation (s t η : List I) (x : X)
    (hs : x = PowerWordWeight.wordWeight D Λ s) (ht : x = PowerWordWeight.wordWeight D Λ t)
    (g : (OldCategory.mk t : OldCategory D Sc cutoff) ⟶ OldCategory.mk s) : Prop :=
  (contextFunctor D Sc cutoff L Λ x η).map (PowerWordWeightWhiskering.wordFamilyArrow D Sc cutoff L Λ x s t g) ≫
      (contextIso D Sc cutoff L Λ t x ht η).hom =
    (contextIso D Sc cutoff L Λ s x hs η).hom ≫
      PowerWordWeightWhiskering.wordFamilyArrow D Sc cutoff L Λ (contextWeight D x η)
        (PowerWordContexts.extendedWord s η) (PowerWordContexts.extendedWord t η)
        (PowerWordContexts.extendedArrow D Sc cutoff s t η g)

/-- Every chosen right context has the prescribed full old-Hom operator on
all content blocks and coefficient vectors. The weight equalities only
express the unchanged weights of the same-content words. -/
theorem context_family_arrow (s t η : List I) (x : X)
    (hs : x = PowerWordWeight.wordWeight D Λ s) (ht : x = PowerWordWeight.wordWeight D Λ t)
    (hst : (s : Multiset I) = (t : Multiset I))
    (g : (OldCategory.mk t : OldCategory D Sc cutoff) ⟶ OldCategory.mk s) :
    contextEquation D Sc cutoff L Λ s t η x hs ht g := by
  induction η generalizing s t x with
  | nil =>
      change (𝟭 _).map _ ≫ (Iso.refl _).hom = (Iso.refl _).hom ≫ _
      simp only [Functor.id_map, Iso.refl_hom, Category.comp_id, Category.id_comp]
      rfl
  | cons i η ih =>
      have hst' : ((s ++ [i] : List I) : Multiset I) = ((t ++ [i] : List I) : Multiset I) := by
        rw [← Multiset.coe_add, ← Multiset.coe_add, hst]
      exact comparison_step
        (elvEFunctor D Sc cutoff N i Λ (rfl : x + D.α i = x + D.α i))
        (contextFunctor D Sc cutoff L Λ (x + D.α i) η)
        (PowerWordWeightCross.appendIsoAtWeights D Sc cutoff L Λ s i x (x + D.α i) hs
          (append_weight D Λ s i x hs) rfl)
        (PowerWordWeightCross.appendIsoAtWeights D Sc cutoff L Λ t i x (x + D.α i) ht
          (append_weight D Λ t i x ht) rfl)
        (contextIso D Sc cutoff L Λ (s ++ [i]) (x + D.α i) (append_weight D Λ s i x hs) η)
        (contextIso D Sc cutoff L Λ (t ++ [i]) (x + D.α i) (append_weight D Λ t i x ht) η)
        (PowerWordWeightWhiskering.wordFamilyArrow D Sc cutoff L Λ x s t g)
        (PowerWordWeightWhiskering.wordFamilyArrow D Sc cutoff L Λ (x + D.α i) (s ++ [i]) (t ++ [i])
          ((append D Sc cutoff i).map g))
        (PowerWordWeightWhiskering.wordFamilyArrow D Sc cutoff L Λ (contextWeight D (x + D.α i) η)
          (PowerWordContexts.extendedWord (s ++ [i]) η) (PowerWordContexts.extendedWord (t ++ [i]) η)
          (PowerWordContexts.extendedArrow D Sc cutoff (s ++ [i]) (t ++ [i]) η ((append D Sc cutoff i).map g)))
        (PowerWordWeightWhiskering.append_family_arrow D Sc cutoff L Λ s t i x (x + D.α i)
          hs (append_weight D Λ s i x hs) ht (append_weight D Λ t i x ht) rfl hst g)
        (ih (s ++ [i]) (t ++ [i]) (x + D.α i) (append_weight D Λ s i x hs)
          (append_weight D Λ t i x ht) hst' ((append D Sc cutoff i).map g))

/-- Apply the given context to a selected chart, then use only the existing
recursive whole append comparisons. -/
def contextChart (ν η : List I) (x : X) (hx : x = PowerWordWeight.wordWeight D Λ ν)
    {A : ELVWeightProduct D Sc cutoff N Λ x}
    (e : A ≅ PowerWordWeight.wordFamily D Sc cutoff L Λ x ν) :
    (contextFunctor D Sc cutoff L Λ x η).obj A ≅
      PowerWordWeight.wordFamily D Sc cutoff L Λ (contextWeight D x η) (PowerWordContexts.extendedWord ν η) :=
  (contextFunctor D Sc cutoff L Λ x η).mapIso e ≪≫ contextIso D Sc cutoff L Λ ν x hx η

omit [Fintype I] in
private theorem pair_weight (ν : List I) (i j : I) {xj xu : X}
    (h₁ : PowerWordWeight.wordWeight D Λ ν + D.α j = xj) (h₂ : xj + D.α i = xu) :
    xu = PowerWordWeight.wordWeight D Λ ((ν ++ [j]) ++ [i]) :=
  h₂.symm.trans ((congrArg (fun x => x + D.α i)
    (h₁.symm.trans (PowerWordWeight.wordWeight_append D Λ ν j))).trans
      (PowerWordWeight.wordWeight_append D Λ (ν ++ [j]) i))

end OddMath.QuiverHecke.ELVOld.PowerWordWeightContexts
