import OddMath.QuiverHecke.CyclotomicAction.ELVContentExtensionAppend
import OddMath.QuiverHecke.CyclotomicAction.ELVContentRestrictionExtension
import OddMath.QuiverHecke.CyclotomicAction.ELVContentRestrictionTensor
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Chosen content E/F comparisons as families of module isomorphisms

The content action in SwappedVacuumCoordinates §6 uses canonical extension
along the full content inclusion. The chosen append comparison, including
its inclusion unit, is natural on every supernatural input-module map.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open CategoryTheory.Functor
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor
universe u
private theorem inverseMate_app
    {C B A O : Type u} [Category.{u} C] [Category.{u} B]
    [Category.{u} A] [Category.{u} O]
    {L₁ : C ⥤ A} {R₁ : A ⥤ C} {L₀ : B ⥤ O} {R₀ : O ⥤ B}
    {F : C ⥤ B} {G : A ⥤ O} (a : L₁ ⊣ R₁) (b : L₀ ⊣ R₀)
    (sq : R₁ ⋙ F ⟶ G ⋙ R₀) (M : C) :
    ((mateEquiv a b).symm sq).app M =
      L₀.map (F.map (a.unit.app M)) ≫ L₀.map (sq.app (L₁.obj M)) ≫
        b.counit.app (G.obj (L₁.obj M)) := by
  simp [mateEquiv, Functor.map_comp, Category.assoc]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i : I)

/-- The chosen comparison for content induction, natural on all input maps. -/
def oldContentAppendRestrictionNaturalIso :
    BalancedInduction.induction (k := k) (oldContentAppend D Sc cutoff ν i) ≅
      (BalancedInduction.induction (oldContentInclusion D Sc cutoff ν) ⋙
        BalancedInduction.induction (append D Sc cutoff i)) ⋙
          BalancedInduction.restriction (oldContentInclusion D Sc cutoff (i :: ν)) :=
  (Functor.rightUnitor _).symm ≪≫
    isoWhiskerLeft (BalancedInduction.induction (oldContentAppend D Sc cutoff ν i))
      (BalancedInduction.fullyFaithfulUnitNaturalIso
        (oldContentInclusion D Sc cutoff (i :: ν))) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (oldContentAppendExtensionIso D Sc cutoff ν i)
      (BalancedInduction.restriction (oldContentInclusion D Sc cutoff (i :: ν)))

/-- This family retains the previously chosen comparison at every input module. -/
theorem oldContentAppendRestrictionNaturalIso_hom_app
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k)) :
    (oldContentAppendRestrictionNaturalIso D Sc cutoff ν i).hom.app M =
      (oldContentAppendRestrictionIso D Sc cutoff ν i M).hom := by
  simp only [oldContentAppendRestrictionNaturalIso, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app,
    whiskerRight_app, Functor.rightUnitor_inv_app, Functor.associator_inv_app,
    Category.id_comp, BalancedInduction.fullyFaithfulUnitNaturalIso,
    NatIso.ofComponents_hom_app, oldContentAppendRestrictionIso,
    oldContentExtensionUnitIso, Functor.mapIso_hom]
  rfl

local notation "L₀" => BalancedInduction.induction (k := k) (oldContentInclusion D Sc cutoff ν)
local notation "R₀" => BalancedInduction.restriction (k := k) (oldContentInclusion D Sc cutoff ν)
local notation "L₁" => BalancedInduction.induction (k := k) (oldContentInclusion D Sc cutoff (i :: ν))
local notation "R₁" => BalancedInduction.restriction (k := k) (oldContentInclusion D Sc cutoff (i :: ν))
local notation "Fc" => BalancedInduction.restriction (k := k) (oldContentAppend D Sc cutoff ν i)
local notation "Fo" => BalancedInduction.restriction (k := k) (append D Sc cutoff i)

/-- The selected literal restriction square is natural on all input maps. -/
def oldContentRestrictionSquareNaturalIso : R₁ ⋙ Fc ≅ Fo ⋙ R₀ :=
  NatIso.ofComponents (oldContentRestrictionSquare D Sc cutoff ν i) (by
    intro M N f
    change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
    rw [Category.comp_id, Category.id_comp]
    rfl)

private def restrictionExtensionMate : Fc ⋙ L₀ ⟶ L₁ ⋙ Fo :=
  (mateEquiv (BalancedInduction.adjunction (oldContentInclusion D Sc cutoff (i :: ν)))
    (BalancedInduction.adjunction (oldContentInclusion D Sc cutoff ν))).symm
      (oldContentRestrictionSquareNaturalIso D Sc cutoff ν i).hom

private theorem oldContentRestrictionExtensionIso_hom_mate
    (M : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k)) :
    (oldContentRestrictionExtensionIso D Sc cutoff ν i M).hom =
      (restrictionExtensionMate D Sc cutoff ν i).app M := by
  rw [oldContentRestrictionExtensionIso_hom, restrictionExtensionMate, inverseMate_app]
  simp only [oldContentRestrictionSquareNaturalIso, NatIso.ofComponents_hom_app,
    oldContentRestrictionSquare, Iso.refl_hom, Functor.map_id, Category.comp_id]
  rfl

/-- The selected restriction-extension comparison is natural for all
supernatural input-module maps, including odd maps. -/
theorem oldContentRestrictionExtensionIso_naturality
    {M N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k)} (f : M ⟶ N) :
    (L₀).map ((Fc).map f) ≫ (oldContentRestrictionExtensionIso D Sc cutoff ν i N).hom =
      (oldContentRestrictionExtensionIso D Sc cutoff ν i M).hom ≫ (Fo).map ((L₁).map f) := by
  rw [oldContentRestrictionExtensionIso_hom_mate, oldContentRestrictionExtensionIso_hom_mate]
  exact (restrictionExtensionMate D Sc cutoff ν i).naturality f

/-- The chosen restriction comparison as a whole family on input modules. -/
def oldContentRestrictionExtensionNaturalIso :
    Fc ⋙ L₀ ≅ L₁ ⋙ Fo :=
  NatIso.ofComponents (oldContentRestrictionExtensionIso D Sc cutoff ν i)
    (fun f => oldContentRestrictionExtensionIso_naturality D Sc cutoff ν i f)

end OddMath.QuiverHecke.ELVOld
