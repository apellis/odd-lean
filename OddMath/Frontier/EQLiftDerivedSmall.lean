import OddMath.Frontier.EQLiftDerived

/-!
# Composites of derived inductions along morphisms of dg rings

Generic: derived induction along a composite of morphisms of dg rings is the composite of the derived inductions
(`derivedInductionCompIso`), from dg-lean's `CatModule.DerivedCategory.inductionCompIso`.
-/

noncomputable section

open CategoryTheory

namespace OddMath.Frontier.EQLift

open DG

set_option linter.unusedSectionVars false

universe w₁ w₂

section Comp

variable {A B C : Type} [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B] [DGAddCommGroup B] [DGRing B]
  [Ring C] [DGAddCommGroup C] [DGRing C]
  [CatModule.HasDerivedCategory.{w₁, 0} (SingleObj A)] [CatModule.HasDerivedCategory.{w₁, 0} (SingleObj B)]
  [CatModule.HasDerivedCategory.{w₁, 0} (SingleObj C)]
  [DG.HasDerivedCategory.{w₂, 0} A] [DG.HasDerivedCategory.{w₂, 0} B] [DG.HasDerivedCategory.{w₂, 0} C]

theorem singleObjFunctor_comp (φ : C →ᵈᵍ+* B) (ψ : B →ᵈᵍ+* A) :
    (ψ.comp φ).singleObjFunctor = φ.singleObjFunctor ⋙ ψ.singleObjFunctor := rfl

/-- **Derived induction along `ψ ∘ φ` is derived induction along `φ` followed by derived induction along `ψ`.** -/
def derivedInductionCompIso (φ : C →ᵈᵍ+* B) (ψ : B →ᵈᵍ+* A) :
    (ψ.comp φ).derivedInduction.{w₁, w₁, w₂, w₂} ≅
      φ.derivedInduction.{w₁, w₁, w₂, w₂} ⋙ ψ.derivedInduction.{w₁, w₁, w₂, w₂} :=
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
      (CatModule.DerivedCategory.inductionCompIso φ.singleObjFunctor ψ.singleObjFunctor) _) ≪≫
    Functor.isoWhiskerLeft ((CatModule.DerivedCategory.singleObjEquivalence C).inverse ⋙
        CatModule.DerivedCategory.induction.{w₁, w₁, 0} φ.singleObjFunctor)
      (Functor.isoWhiskerRight (CatModule.DerivedCategory.singleObjEquivalence B).unitIso
        (CatModule.DerivedCategory.induction.{w₁, w₁, 0} ψ.singleObjFunctor ⋙
          (CatModule.DerivedCategory.singleObjEquivalence A).functor))

end Comp

end OddMath.Frontier.EQLift
