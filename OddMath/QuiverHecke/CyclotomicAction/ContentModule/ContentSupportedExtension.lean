import StringDiagrams.Super.PiTwo
import Mathlib.CategoryTheory.Adjunction.Mates
import OddMath.QuiverHecke.CyclotomicAction.ContentModule.ContentModuleQuadratic
import OddMath.QuiverHecke.CyclotomicAction.KernelDegree

/-!
# Content module

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Canonical extension and support on an old content block

Content conservation makes extension by the full content inclusion zero off
that content. On supported modules the actual inclusion counit is invertible.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  {C E : Type u} [Category.{u} C] [Category.{u} E]
  [Preadditive C] [Linear k C] [Preadditive E] [Linear k E]
  (J : C ⥤ E)

omit [Preadditive C] [Linear k C] in
theorem obj_eq_zero_of_coeff_eq_zero (M : C ⥤ SVec k) (w : E)
    (h : ∀ s (g : J.obj s ⟶ w), g = 0) (z : Obj J M w) : z = 0 := by
  have hz : (LinearMap.id : Obj J M w →ₗ[k] Obj J M w) = 0 := by
    apply hom_ext
    intro s g b
    change tensor J M s g b = 0
    rw [h s g]
    exact tensor_zero_left J M s b
  exact LinearMap.congr_fun hz z

variable [J.Full] [J.Faithful] [J.Additive] [J.Linear k]
  (N : E ⥤ SVec k) [N.Additive] [N.Linear k]

theorem counit_eq_fullyFaithfulUnitInverse (v : C) :
    counit J N (J.obj v) = fullyFaithfulUnitInverse J (J ⋙ N) v := by
  apply hom_ext
  intro s g b
  rw [counit_tensor]
  have he := fullyFaithfulUnitInverse_tensor J (J ⋙ N) v s g b
  change fullyFaithfulUnitInverse J (J ⋙ N) v (tensor J (J ⋙ N) s g b) =
    N.map (J.map (J.preimage g)) b at he
  rw [Functor.map_preimage] at he
  exact he.symm

theorem counit_bijective_at_image (v : C) :
    Function.Bijective (counit J N (J.obj v)) := by
  rw [counit_eq_fullyFaithfulUnitInverse]
  have hleft := fullyFaithfulUnitInverse_unit J (J ⋙ N) v
  have hright := unit_fullyFaithfulUnitInverse J (J ⋙ N) v
  exact ⟨fun x y h => by
    have hx := LinearMap.congr_fun hright x
    have hy := LinearMap.congr_fun hright y
    change unit J (J ⋙ N) v (fullyFaithfulUnitInverse J (J ⋙ N) v x) = x at hx
    change unit J (J ⋙ N) v (fullyFaithfulUnitInverse J (J ⋙ N) v y) = y at hy
    exact hx.symm.trans ((congrArg (unit J (J ⋙ N) v) h).trans hy),
    fun y => ⟨unit J (J ⋙ N) v y, LinearMap.congr_fun hleft y⟩⟩

end OddMath.QuiverHecke.ELV.BalancedInduction
namespace OddMath.QuiverHecke.ELV
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Support means literal zero components outside the chosen colour multiset. -/
def OldContentSupported (ν : List I)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) : Prop :=
  ∀ w : OldCategory D Sc cutoff, (w.word : Multiset I) ≠ (ν : Multiset I) →
    Subsingleton (N.obj w)

theorem oldContentExtension_supported (ν : List I)
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k)) :
    OldContentSupported D Sc cutoff ν
      (BalancedInduction.induced (oldContentInclusion D Sc cutoff ν) M) := by
  intro w hw
  have hz : ∀ z : BalancedInduction.Obj (oldContentInclusion D Sc cutoff ν) M.toFunctor w,
      z = 0 := by
    apply BalancedInduction.obj_eq_zero_of_coeff_eq_zero
    intro s g
    apply oldCategory_hom_eq_zero_of_content_ne D Sc cutoff (f := g)
    intro he
    exact hw (he.symm.trans (Multiset.coe_eq_coe.mpr s.wordPerm))
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

theorem supported_contentCounit_bijective (ν : List I)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hN : OldContentSupported D Sc cutoff ν N) (w : OldCategory D Sc cutoff) :
    Function.Bijective (BalancedInduction.counit (oldContentInclusion D Sc cutoff ν)
      N.toFunctor w) := by
  classical
  by_cases hw : (w.word : Multiset I) = (ν : Multiset I)
  · exact BalancedInduction.counit_bijective_at_image
      (oldContentInclusion D Sc cutoff ν) N.toFunctor
      ⟨w, Multiset.coe_eq_coe.mp hw⟩
  · have hsource := oldContentExtension_supported D Sc cutoff ν
      ((BalancedInduction.restriction (oldContentInclusion D Sc cutoff ν)).obj N) w hw
    have htarget := hN w hw
    exact ⟨fun x y _ => hsource.elim x y, fun y => ⟨0, htarget.elim _ y⟩⟩

/-- The forward map is precisely the established balanced inclusion counit. -/
def supportedContentCounitEquiv (ν : List I)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hN : OldContentSupported D Sc cutoff ν N) (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj (oldContentInclusion D Sc cutoff ν)
        (oldContentInclusion D Sc cutoff ν ⋙ N.toFunctor) w ≃ₗ[k] N.obj w :=
  LinearEquiv.ofBijective _ (supported_contentCounit_bijective D Sc cutoff ν N hN w)

def supportedContentCounitNatIso (ν : List I)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hN : OldContentSupported D Sc cutoff ν N) :
    (BalancedInduction.induced (oldContentInclusion D Sc cutoff ν)
      ((BalancedInduction.restriction (oldContentInclusion D Sc cutoff ν)).obj N)).toFunctor ≅
        N.toFunctor :=
  NatIso.ofComponents (fun w =>
    { hom := BalancedInduction.counit (oldContentInclusion D Sc cutoff ν) N.toFunctor w
      inv := (supportedContentCounitEquiv D Sc cutoff ν N hN w).symm.toLinearMap
      hom_inv_id := by
        ext z
        exact (supportedContentCounitEquiv D Sc cutoff ν N hN w).symm_apply_apply z
      inv_hom_id := by
        ext z
        exact (supportedContentCounitEquiv D Sc cutoff ν N hN w).apply_symm_apply z })
    (fun a => BalancedInduction.counit_naturality (oldContentInclusion D Sc cutoff ν)
      N.toFunctor a)

/-- Supported modules are recovered by the actual even inclusion counit. -/
def supportedContentCounitIso (ν : List I)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hN : OldContentSupported D Sc cutoff ν N) :
    BalancedInduction.induced (oldContentInclusion D Sc cutoff ν)
      ((BalancedInduction.restriction (oldContentInclusion D Sc cutoff ν)).obj N) ≅ N :=
  moduleIsoOfEvenNatIso _ _ (supportedContentCounitNatIso D Sc cutoff ν N hN)
    (fun w => BalancedInduction.counit_mem (oldContentInclusion D Sc cutoff ν) N w)
    (fun w => Supercategory.inv_mem
      ((supportedContentCounitNatIso D Sc cutoff ν N hN).app w)
      (BalancedInduction.counit_mem (oldContentInclusion D Sc cutoff ν) N w))

theorem supportedContentCounitIso_hom (ν : List I)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hN : OldContentSupported D Sc cutoff ν N) :
    (supportedContentCounitIso D Sc cutoff ν N hN).hom =
      (BalancedInduction.adjunctionCounit (oldContentInclusion D Sc cutoff ν)).app N := by
  apply Superfunctor.hom_ext
  intro p w
  rfl

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Restriction and canonical old-content extension

The literal append/inclusion square and the supported inclusion counit give
an actual supermodule comparison for restriction, alongside the induction
comparison. The support argument uses full coefficients and no flatness.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem oldAppendRestriction_supported (ν : List I) (i : I)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hN : OldContentSupported D Sc cutoff (i :: ν) N) :
    OldContentSupported D Sc cutoff ν
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj N) := by
  intro w hw
  apply hN ((append D Sc cutoff i).obj w)
  intro he
  apply hw
  change (w.word : Multiset I) + ([i] : Multiset I) =
    ([i] : Multiset I) + (ν : Multiset I) at he
  rw [add_comm ([i] : Multiset I)] at he
  exact add_right_cancel he

/-- The two restrictions in the append/inclusion square agree literally. -/
def oldContentRestrictionSquare (ν : List I) (i : I)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (BalancedInduction.restriction (oldContentAppend D Sc cutoff ν i)).obj
      ((BalancedInduction.restriction (oldContentInclusion D Sc cutoff (i :: ν))).obj N) ≅
    (BalancedInduction.restriction (oldContentInclusion D Sc cutoff ν)).obj
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj N) := Iso.refl _

/-- Extending fixed-content restriction is canonically old restriction of the
canonical extension. The map is built from the actual inclusion unit/counit. -/
def oldContentRestrictionExtensionIso (ν : List I) (i : I)
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k)) :
    BalancedInduction.induced (oldContentInclusion D Sc cutoff ν)
      ((BalancedInduction.restriction (oldContentAppend D Sc cutoff ν i)).obj N) ≅
    (BalancedInduction.restriction (append D Sc cutoff i)).obj
      (BalancedInduction.induced (oldContentInclusion D Sc cutoff (i :: ν)) N) :=
  (BalancedInduction.induction (oldContentInclusion D Sc cutoff ν)).mapIso
    ((BalancedInduction.restriction (oldContentAppend D Sc cutoff ν i)).mapIso
      (oldContentExtensionUnitIso D Sc cutoff (i :: ν) N) ≪≫
      oldContentRestrictionSquare D Sc cutoff ν i
        (BalancedInduction.induced (oldContentInclusion D Sc cutoff (i :: ν)) N)) ≪≫
    supportedContentCounitIso D Sc cutoff ν _
      (oldAppendRestriction_supported D Sc cutoff ν i _
        (oldContentExtension_supported D Sc cutoff (i :: ν) N))

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Generator formula for the content restriction comparison

The canonical inclusion unit/counit comparison sends [g ⊗ b] to
[append(g) ⊗ b]. This is the restriction-side map needed to compare the
fixed-content action generators in SwappedVacuumCoordinates §6.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  {C E : Type u} [Category.{u} C] [Category.{u} E]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive E] [Linear k E] [Supercategory k E]
  (J : C ⥤ E) [J.Additive] [J.Linear k] [IsSuperfunctor k J]

theorem unit_total_apply (M : Superfunctor k C (SVec k)) (v : C) (b : M.obj v) :
    ((adjunctionUnit J).app M).total v b = unit J M.toFunctor v b := by
  simp only [adjunctionUnit, Superfunctor.homMk, SuperNatTrans.total,
    unitTransform_app, ↓reduceIte, one_ne_zero, add_zero]
  rfl

theorem counit_total_apply (N : Superfunctor k E (SVec k)) (w : E)
    (z : Obj J (J ⋙ N.toFunctor) w) :
    ((adjunctionCounit J).app N).total w z = counit J N.toFunctor w z := by
  simp only [adjunctionCounit, Superfunctor.homMk, SuperNatTrans.total,
    counitTransform_app, ↓reduceIte, one_ne_zero, add_zero]
  rfl

end OddMath.QuiverHecke.ELV.BalancedInduction
namespace OddMath.QuiverHecke.ELV
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The comparison is the induction of the actual inclusion unit followed by
its actual inclusion counit; the append/inclusion restriction square is strict. -/
theorem oldContentRestrictionExtensionIso_hom (ν : List I) (i : I)
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k)) :
    (oldContentRestrictionExtensionIso D Sc cutoff ν i N).hom =
      (BalancedInduction.induction (oldContentInclusion D Sc cutoff ν)).map
        ((BalancedInduction.restriction (oldContentAppend D Sc cutoff ν i)).map
          ((BalancedInduction.adjunctionUnit
            (oldContentInclusion D Sc cutoff (i :: ν))).app N)) ≫
      (BalancedInduction.adjunctionCounit (oldContentInclusion D Sc cutoff ν)).app
        ((BalancedInduction.restriction (append D Sc cutoff i)).obj
          (BalancedInduction.induced (oldContentInclusion D Sc cutoff (i :: ν)) N)) := by
  simp only [oldContentRestrictionExtensionIso, Iso.trans_hom, Functor.mapIso_hom,
    oldContentRestrictionSquare, Iso.refl_hom, Category.comp_id,
    oldContentExtensionUnitIso, BalancedInduction.fullyFaithfulUnitIso_hom,
    supportedContentCounitIso_hom]

/-- The prescribed source-arrow generator is unchanged and its old arrow is appended. -/
theorem oldContentRestrictionExtensionIso_tensor (ν : List I) (i : I)
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (w : OldCategory D Sc cutoff) (s : OldContentCategory D Sc cutoff ν)
    (g : (oldContentInclusion D Sc cutoff ν).obj s ⟶ w)
    (b : N.obj ((oldContentAppend D Sc cutoff ν i).obj s)) :
    (oldContentRestrictionExtensionIso D Sc cutoff ν i N).hom.total w
      (BalancedInduction.tensor (oldContentInclusion D Sc cutoff ν)
        ((BalancedInduction.restriction (oldContentAppend D Sc cutoff ν i)).obj N).toFunctor s g b) =
      BalancedInduction.tensor (oldContentInclusion D Sc cutoff (i :: ν)) N.toFunctor
        ((oldContentAppend D Sc cutoff ν i).obj s) ((append D Sc cutoff i).map g) b := by
  rw [oldContentRestrictionExtensionIso_hom, Superfunctor.comp_total]
  change ((BalancedInduction.adjunctionCounit (oldContentInclusion D Sc cutoff ν)).app
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj
        (BalancedInduction.induced (oldContentInclusion D Sc cutoff (i :: ν)) N))).total w
      ((BalancedInduction.moduleMap (oldContentInclusion D Sc cutoff ν)
        ((BalancedInduction.restriction (oldContentAppend D Sc cutoff ν i)).map
          ((BalancedInduction.adjunctionUnit
            (oldContentInclusion D Sc cutoff (i :: ν))).app N))).total w
        (BalancedInduction.tensor (oldContentInclusion D Sc cutoff ν)
          ((BalancedInduction.restriction (oldContentAppend D Sc cutoff ν i)).obj N).toFunctor
            s g b)) = _
  rw [BalancedInduction.counit_total_apply]
  have hm := BalancedInduction.moduleMap_total_tensor
    (oldContentInclusion D Sc cutoff ν)
    ((BalancedInduction.restriction (oldContentAppend D Sc cutoff ν i)).map
      ((BalancedInduction.adjunctionUnit (oldContentInclusion D Sc cutoff (i :: ν))).app N))
    w s g b
  refine (congrArg (BalancedInduction.counit (oldContentInclusion D Sc cutoff ν)
    ((BalancedInduction.restriction (append D Sc cutoff i)).obj
      (BalancedInduction.induced (oldContentInclusion D Sc cutoff (i :: ν)) N)).toFunctor w) hm).trans ?_
  change BalancedInduction.counit (oldContentInclusion D Sc cutoff ν)
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj
        (BalancedInduction.induced (oldContentInclusion D Sc cutoff (i :: ν)) N)).toFunctor w
      (BalancedInduction.tensor (oldContentInclusion D Sc cutoff ν) _ s g
        (BalancedInduction.unit (oldContentInclusion D Sc cutoff (i :: ν)) N.toFunctor
          ((oldContentAppend D Sc cutoff ν i).obj s) b) +
        BalancedInduction.tensor (oldContentInclusion D Sc cutoff ν) _ s (twist k 1 g) 0) = _
  rw [BalancedInduction.tensor_zero_right, add_zero, BalancedInduction.counit_tensor]
  change BalancedInduction.postcompose (oldContentInclusion D Sc cutoff (i :: ν)) N.toFunctor
      ((append D Sc cutoff i).map g)
      (BalancedInduction.unit (oldContentInclusion D Sc cutoff (i :: ν)) N.toFunctor
        ((oldContentAppend D Sc cutoff ν i).obj s) b) = _
  rw [BalancedInduction.unit_apply, BalancedInduction.postcompose_tensor, Category.id_comp]

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Chosen content E/F comparisons as families of module isomorphisms

The content action in SwappedVacuumCoordinates §6 uses canonical extension
along the full content inclusion. The chosen append comparison, including
its inclusion unit, is natural on every supernatural input-module map.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open CategoryTheory.Functor
namespace OddMath.QuiverHecke.ELV
open CyclotomicCrossingTensor
universe u v
private theorem inverseMate_app
    {C B A O : Type u} [Category.{v} C] [Category.{v} B]
    [Category.{v} A] [Category.{v} O]
    {L₁ : C ⥤ A} {R₁ : A ⥤ C} {L₀ : B ⥤ O} {R₀ : O ⥤ B}
    {F : C ⥤ B} {G : A ⥤ O} (a : L₁ ⊣ R₁) (b : L₀ ⊣ R₀)
    (sq : R₁ ⋙ F ⟶ G ⋙ R₀) (M : C) :
    ((mateEquiv a b).symm sq).app M =
      L₀.map (F.map (a.unit.app M)) ≫ L₀.map (sq.app (L₁.obj M)) ≫
        b.counit.app (G.obj (L₁.obj M)) := by
  simp [mateEquiv]

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
local notation "Ec" => BalancedInduction.induction (k := k) (oldContentAppend D Sc cutoff ν i)
local notation "Eo" => BalancedInduction.induction (k := k) (append D Sc cutoff i)

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
    oldContentRestrictionSquare, Iso.refl_hom]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
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

/-- Extension of the preceding E/F composite at content i::ν uses the
chosen append comparison and the chosen restriction comparison, in order. -/
def oldContentEFExtensionNaturalIso :
    (Fc ⋙ Ec) ⋙ L₁ ≅ (L₁ ⋙ Fo) ⋙ Eo :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft Fc (oldContentAppendExtensionIso D Sc cutoff ν i) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (oldContentRestrictionExtensionNaturalIso D Sc cutoff ν i) Eo

/-- The composite comparison retains both prescribed forward maps. -/
theorem oldContentEFExtensionNaturalIso_hom_app
    (M : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k)) :
    (oldContentEFExtensionNaturalIso D Sc cutoff ν i).hom.app M =
      (oldContentAppendExtensionIso D Sc cutoff ν i).hom.app ((Fc).obj M) ≫
        (Eo).map (oldContentRestrictionExtensionIso D Sc cutoff ν i M).hom := by
  simp only [oldContentEFExtensionNaturalIso, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app,
    whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, oldContentRestrictionExtensionNaturalIso, NatIso.ofComponents_hom_app]

/-- The preceding E/F composite at i::ν agrees with old E/F after canonical
extension and restriction. Its source is the chosen content composite. -/
def oldContentEFRestrictionNaturalIso :
    Fc ⋙ Ec ≅ ((L₁ ⋙ Fo) ⋙ Eo) ⋙ R₁ :=
  (Functor.rightUnitor _).symm ≪≫
    isoWhiskerLeft (Fc ⋙ Ec)
      (BalancedInduction.fullyFaithfulUnitNaturalIso
        (oldContentInclusion D Sc cutoff (i :: ν))) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (oldContentEFExtensionNaturalIso D Sc cutoff ν i) R₁

/-- The following F/E composite at ν agrees with old F/E after canonical
extension and restriction, using the selected append-restriction map. -/
def oldContentFERestrictionNaturalIso :
    Ec ⋙ Fc ≅ ((L₀ ⋙ Eo) ⋙ Fo) ⋙ R₀ :=
  isoWhiskerRight (oldContentAppendRestrictionNaturalIso D Sc cutoff ν i) Fc ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (L₀ ⋙ Eo) (oldContentRestrictionSquareNaturalIso D Sc cutoff ν i) ≪≫
    (Functor.associator _ _ _).symm

/-- The following-composite chart keeps the chosen E comparison under F. -/
theorem oldContentFERestrictionNaturalIso_hom_app
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k)) :
    (oldContentFERestrictionNaturalIso D Sc cutoff ν i).hom.app M =
      (Fc).map (oldContentAppendRestrictionIso D Sc cutoff ν i M).hom := by
  simp only [oldContentFERestrictionNaturalIso, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app,
    whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    oldContentAppendRestrictionNaturalIso_hom_app, oldContentRestrictionSquareNaturalIso,
    NatIso.ofComponents_hom_app, oldContentRestrictionSquare, Iso.refl_hom,
    Category.comp_id]
  erw [Category.comp_id, Category.comp_id]

end OddMath.QuiverHecke.ELV
end

end
