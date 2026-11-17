import OddMath.QuiverHecke.CyclotomicAction.BoundaryNumerator.BoundaryRowLeading
import OddMath.QuiverHecke.CyclotomicAction.ContentModule.ContentSupportedExtension
import OddMath.QuiverHecke.CyclotomicAction.InductionGridMate.InductionSquareTensors

/-!
# Content append

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # The chosen dot under full-content extension

The content E/F comparison in DeformedActionAssembly §5 must preserve the
chosen generators before the old-category inverse matrices are transported.
Here the existing old append dot restricts to the old content category, and
the canonical append-extension comparison intertwines its induced operator
with the prescribed old induction dot. All coefficient twists are retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
open CyclotomicCrossingTensor
universe u

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i : I)

/-- The literal old append dot, restricted to its full content category. -/
def oldContentAppendDot (s : OldContentCategory D Sc cutoff ν) :
    (oldContentAppend D Sc cutoff ν i).obj s ⟶
      (oldContentAppend D Sc cutoff ν i).obj s :=
  oldAppendDotComponent D Sc cutoff i s.obj

theorem oldContentAppendDot_supernatural :
    IsSupernatural k (D.parity i) (oldContentAppendDot D Sc cutoff ν i) where
  mem s := (oldAppendDot_supernatural D Sc cutoff i).mem s.obj
  naturality := by
    intro s t p f hf
    exact (oldAppendDot_supernatural D Sc cutoff i).naturality hf

/-- The induced chosen dot on the old content module category. -/
def oldContentInductionDotComponent
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k)) :
    BalancedInduction.induced (oldContentAppend D Sc cutoff ν i) M ⟶
      BalancedInduction.induced (oldContentAppend D Sc cutoff ν i) M :=
  BalancedInduction.transformComponent (oldContentAppendDot_supernatural D Sc cutoff ν i) M

/-- The literal linear component of the chosen comparison, with both raw
coend carriers fixed before inserting its operator maps. -/
def oldContentAppendExtensionLinear
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))
    (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj (oldContentInclusion D Sc cutoff (i :: ν))
        (BalancedInduction.induced (oldContentAppend D Sc cutoff ν i) M).toFunctor w →ₗ[k]
      BalancedInduction.Obj (append D Sc cutoff i)
        (BalancedInduction.induced (oldContentInclusion D Sc cutoff ν) M).toFunctor w :=
  ((oldContentAppendExtensionIso D Sc cutoff ν i).hom.app M).total w

/-- The chosen comparison's tensor formula in the fixed raw coend carriers. -/
theorem oldContentAppendExtensionLinear_tensor
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))
    (s : OldContentCategory D Sc cutoff ν)
    (t : OldContentCategory D Sc cutoff (i :: ν)) (w : OldCategory D Sc cutoff)
    (h : t.obj ⟶ w)
    (g : (append D Sc cutoff i).obj s.obj ⟶ t.obj) (b : M.obj s) :
    oldContentAppendExtensionLinear D Sc cutoff ν i M w
      (BalancedInduction.tensor (oldContentInclusion D Sc cutoff (i :: ν))
        (BalancedInduction.induced (oldContentAppend D Sc cutoff ν i) M).toFunctor
        t h (BalancedInduction.tensor (oldContentAppend D Sc cutoff ν i)
          M.toFunctor s g b)) =
      BalancedInduction.inductionInsertedTensor (oldContentInclusion D Sc cutoff ν)
        (append D Sc cutoff i) M s w (g ≫ h) b := by
  exact oldContentAppendExtensionIso_tensor D Sc cutoff ν i M s t w h g b

/-- On every nested generator, the chosen comparison keeps the full twist
from the inner dot and the outer induction map. -/
theorem oldContentAppendExtensionIso_dot_tensor
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))
    (s : OldContentCategory D Sc cutoff ν)
    (t : OldContentCategory D Sc cutoff (i :: ν)) (w : OldCategory D Sc cutoff)
    (h : t.obj ⟶ w)
    (g : (oldContentAppend D Sc cutoff ν i).obj s ⟶ t) (b : M.obj s) :
    oldContentAppendExtensionLinear D Sc cutoff ν i M w
      (BalancedInduction.mapComponent (oldContentInclusion D Sc cutoff (i :: ν))
        (oldContentInductionDotComponent D Sc cutoff ν i M) (D.parity i) w
        (BalancedInduction.tensor (oldContentInclusion D Sc cutoff (i :: ν))
          (BalancedInduction.induced (oldContentAppend D Sc cutoff ν i) M).toFunctor
          t h (BalancedInduction.tensor (oldContentAppend D Sc cutoff ν i)
            M.toFunctor s g b))) =
    inductionDot D Sc cutoff i
      (BalancedInduction.induced (oldContentInclusion D Sc cutoff ν) M) w
      (oldContentAppendExtensionLinear D Sc cutoff ν i M w
        (BalancedInduction.tensor (oldContentInclusion D Sc cutoff (i :: ν))
          (BalancedInduction.induced (oldContentAppend D Sc cutoff ν i) M).toFunctor
          t h (BalancedInduction.tensor (oldContentAppend D Sc cutoff ν i)
            M.toFunctor s g b))) := by
  rw [BalancedInduction.mapComponent_tensor]
  simp only [oldContentInductionDotComponent, BalancedInduction.transformComponent_apply,
    ↓reduceIte, BalancedInduction.transformLinear_tensor]
  rw [oldContentAppendExtensionLinear_tensor, oldContentAppendExtensionLinear_tensor]
  unfold BalancedInduction.inductionInsertedTensor
  rw [inductionDot_tensor]
  apply congrArg (fun a : (append D Sc cutoff i).obj s.obj ⟶ w =>
    BalancedInduction.tensor (append D Sc cutoff i)
      (BalancedInduction.induced (oldContentInclusion D Sc cutoff ν) M).toFunctor
      s.obj a (BalancedInduction.tensor (oldContentInclusion D Sc cutoff ν)
        M.toFunctor s (𝟙 s.obj) b))
  change (oldAppendDotComponent D Sc cutoff i s.obj ≫
      twist k (D.parity i) (show (append D Sc cutoff i).obj s.obj ⟶ t.obj from g)) ≫
      twist k (D.parity i) h =
    oldAppendDotComponent D Sc cutoff i s.obj ≫
      twist k (D.parity i)
        ((show (append D Sc cutoff i).obj s.obj ⟶ t.obj from g) ≫ h)
  rw [twist_comp, Category.assoc]

/-- The entire canonical append-extension comparison intertwines the dot
on all balanced coends, with no homogeneity hypothesis on their generators. -/
theorem oldContentAppendExtensionIso_dot
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))
    (w : OldCategory D Sc cutoff) :
    oldContentAppendExtensionLinear D Sc cutoff ν i M w ∘ₗ
      BalancedInduction.mapComponent (oldContentInclusion D Sc cutoff (i :: ν))
        (oldContentInductionDotComponent D Sc cutoff ν i M) (D.parity i) w =
    inductionDot D Sc cutoff i
      (BalancedInduction.induced (oldContentInclusion D Sc cutoff ν) M) w ∘ₗ
        oldContentAppendExtensionLinear D Sc cutoff ν i M w := by
  apply BalancedInduction.nested_hom_ext
    (oldContentAppend D Sc cutoff ν i) (oldContentInclusion D Sc cutoff (i :: ν)) M w
  intro s t h g b
  simpa only [LinearMap.comp_apply] using
    oldContentAppendExtensionIso_dot_tensor D Sc cutoff ν i M s t w h g b

end OddMath.QuiverHecke.ELV
end

end

section

/-! # The chosen dot after restricting append extension

The fixed-content inverse comparison in DeformedActionAssembly §5 uses
`oldContentAppendRestrictionIso`, including its selected fully-faithful
inclusion unit. Its literal raw coend component intertwines the prescribed
content dot and the restricted old induction dot, with either moving parity.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
open CyclotomicCrossingTensor
universe u

namespace BalancedInduction
private theorem fullyFaithfulComparison_total
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Full] [J.Faithful] [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (N : Superfunctor k C (SVec k)) (P : Superfunctor k A (SVec k))
    (e : induced J N ≅ P) (v : C) (b : N.obj v) :
    ((fullyFaithfulUnitIso J N ≪≫ (restriction J).mapIso e).hom).total v b =
      e.hom.total (J.obj v) (unit J N.toFunctor v b) := by
  have hu : (fullyFaithfulUnitIso J N).hom.total v b = unit J N.toFunctor v b := by
    rw [fullyFaithfulUnitIso_hom]
    exact unit_total_apply J N v b
  rw [Iso.trans_hom, Functor.mapIso_hom, Superfunctor.comp_total]
  change ((restriction J).map e.hom).total v
    ((fullyFaithfulUnitIso J N).hom.total v b) = _
  exact congrArg (fun a => ((restriction J).map e.hom).total v a) hu

private theorem fullyFaithfulComparison_linear
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Full] [J.Faithful] [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (N : Superfunctor k C (SVec k)) (P : Superfunctor k A (SVec k))
    (e : induced J N ≅ P) (v : C) :
    ((fullyFaithfulUnitIso J N ≪≫ (restriction J).mapIso e).hom).total v =
      e.hom.total (J.obj v) ∘ₗ unit J N.toFunctor v := by
  apply LinearMap.ext
  intro b
  exact fullyFaithfulComparison_total J N P e v b

private theorem mapComponent_unit
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {M N : Superfunctor k C (SVec k)} (f : M ⟶ N) (p : ZMod 2) (v : C) (b : M.obj v) :
    mapComponent J f p (J.obj v) (unit J M.toFunctor v b) =
      unit J N.toFunctor v (f.app p v b) := by
  rw [unit_apply, mapComponent_tensor, twist_id, unit_apply]

private theorem mapComponent_unit_linear
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {M N : Superfunctor k C (SVec k)} (f : M ⟶ N) (p : ZMod 2) (v : C) :
    mapComponent J f p (J.obj v) ∘ₗ unit J M.toFunctor v =
      unit J N.toFunctor v ∘ₗ f.app p v := by
  apply LinearMap.ext
  intro b
  exact mapComponent_unit J f p v b
end BalancedInduction

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i : I)

/-- The selected append-restriction comparison on its literal coend carriers. -/
def oldContentAppendRestrictionLinear
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) :
    BalancedInduction.Obj (oldContentAppend D Sc cutoff ν i) M.toFunctor t →ₗ[k]
      BalancedInduction.Obj (append D Sc cutoff i)
        (BalancedInduction.induced (oldContentInclusion D Sc cutoff ν) M).toFunctor t.obj :=
  (oldContentAppendRestrictionIso D Sc cutoff ν i M).hom.total t

/-- The actual inclusion unit, with its source fixed as the raw append coend. -/
def oldContentAppendInclusionUnitLinear
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) :
    BalancedInduction.Obj (oldContentAppend D Sc cutoff ν i) M.toFunctor t →ₗ[k]
      BalancedInduction.Obj (oldContentInclusion D Sc cutoff (i :: ν))
        (BalancedInduction.induced (oldContentAppend D Sc cutoff ν i) M).toFunctor t.obj :=
  BalancedInduction.unit (oldContentInclusion D Sc cutoff (i :: ν))
    (BalancedInduction.induced (oldContentAppend D Sc cutoff ν i) M).toFunctor t

/-- The selected map first inserts the actual inclusion unit and then uses
the already selected full-content append extension comparison. -/
theorem oldContentAppendRestrictionLinear_eq
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) :
    oldContentAppendRestrictionLinear D Sc cutoff ν i M t =
      oldContentAppendExtensionLinear D Sc cutoff ν i M t.obj ∘ₗ
        oldContentAppendInclusionUnitLinear D Sc cutoff ν i M t := by
  exact BalancedInduction.fullyFaithfulComparison_linear
    (oldContentInclusion D Sc cutoff (i :: ν))
    (BalancedInduction.induced (oldContentAppend D Sc cutoff ν i) M)
    (BalancedInduction.induced (append D Sc cutoff i)
      (BalancedInduction.induced (oldContentInclusion D Sc cutoff ν) M))
    ((oldContentAppendExtensionIso D Sc cutoff ν i).app M) t

/-- Restricting the chosen comparison preserves the literal dot operator
for both moving parities, on every module and every content object. -/
theorem oldContentAppendRestrictionIso_dot
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) :
    oldContentAppendRestrictionLinear D Sc cutoff ν i M t ∘ₗ
      BalancedInduction.transformLinear
        (oldContentAppendDot_supernatural D Sc cutoff ν i) M t =
      inductionDot D Sc cutoff i
        (BalancedInduction.induced (oldContentInclusion D Sc cutoff ν) M) t.obj ∘ₗ
          oldContentAppendRestrictionLinear D Sc cutoff ν i M t := by
  simp only [oldContentAppendRestrictionLinear_eq]
  have hu := BalancedInduction.mapComponent_unit_linear
    (oldContentInclusion D Sc cutoff (i :: ν))
    (oldContentInductionDotComponent D Sc cutoff ν i M) (D.parity i) t
  simp only [oldContentInductionDotComponent, BalancedInduction.transformComponent_app,
    ↓reduceIte] at hu
  change BalancedInduction.mapComponent (oldContentInclusion D Sc cutoff (i :: ν))
      (oldContentInductionDotComponent D Sc cutoff ν i M) (D.parity i) t.obj ∘ₗ
      oldContentAppendInclusionUnitLinear D Sc cutoff ν i M t =
    oldContentAppendInclusionUnitLinear D Sc cutoff ν i M t ∘ₗ
      BalancedInduction.transformLinear
        (oldContentAppendDot_supernatural D Sc cutoff ν i) M t at hu
  rw [LinearMap.comp_assoc, ← hu, ← LinearMap.comp_assoc,
    oldContentAppendExtensionIso_dot, LinearMap.comp_assoc]

end OddMath.QuiverHecke.ELV
end

end

section

/-! # The ordinary adjunction under old-content extension

The chosen full-content append comparisons in SwappedVacuumCoordinates §6
must preserve the prescribed cup and cap before the same-colour matrix
inverse can be attached to the content E/F functors. These are comparisons
of the existing units and counits, on every input module and every vector.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
open CyclotomicCrossingTensor
universe u
namespace BalancedInduction
private theorem even_comp_app_one
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {M L N : Superfunctor k C (SVec k)} (f : M ⟶ L) (g : L ⟶ N)
    (hf : f ∈ parity (R := k) _ _ 0) (hg : g ∈ parity (R := k) _ _ 0) (v : C) :
    (f ≫ g).app 1 v = 0 :=
  Superfunctor.app_eq_zero_of_mem (comp_mem hf hg) (by decide) v

end BalancedInduction

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i : I)

/-- The selected append-restriction comparison sends the actual content
unit to the old append unit on the actual inclusion unit. -/
theorem oldContentAppendRestrictionIso_unit
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))
    (s : OldContentCategory D Sc cutoff ν) (b : M.obj s) :
    oldContentAppendRestrictionLinear D Sc cutoff ν i M
      ((oldContentAppend D Sc cutoff ν i).obj s)
      (BalancedInduction.unit (oldContentAppend D Sc cutoff ν i) M.toFunctor s b) =
    BalancedInduction.unit (append D Sc cutoff i)
      (BalancedInduction.induced (oldContentInclusion D Sc cutoff ν) M).toFunctor s.obj
      (BalancedInduction.unit (oldContentInclusion D Sc cutoff ν) M.toFunctor s b) := by
  rw [oldContentAppendRestrictionLinear_eq, LinearMap.comp_apply]
  have hu : oldContentAppendInclusionUnitLinear D Sc cutoff ν i M
      ((oldContentAppend D Sc cutoff ν i).obj s)
      (BalancedInduction.unit (oldContentAppend D Sc cutoff ν i) M.toFunctor s b) =
      BalancedInduction.tensor (oldContentInclusion D Sc cutoff (i :: ν))
        (BalancedInduction.induced (oldContentAppend D Sc cutoff ν i) M).toFunctor
        ((oldContentAppend D Sc cutoff ν i).obj s) (𝟙 ((append D Sc cutoff i).obj s.obj))
        (BalancedInduction.tensor (oldContentAppend D Sc cutoff ν i) M.toFunctor s
          (𝟙 ((append D Sc cutoff i).obj s.obj)) b) := rfl
  rw [hu, oldContentAppendExtensionLinear_tensor]
  exact congrArg (fun a : (append D Sc cutoff i).obj s.obj ⟶
      (append D Sc cutoff i).obj s.obj =>
      BalancedInduction.inductionInsertedTensor (oldContentInclusion D Sc cutoff ν)
        (append D Sc cutoff i) M s ((append D Sc cutoff i).obj s.obj) a b)
    (Category.id_comp (𝟙 ((append D Sc cutoff i).obj s.obj)))

/-- The chosen comparison for content restriction, on its literal coend carriers. -/
def oldContentRestrictionExtensionLinear
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj (oldContentInclusion D Sc cutoff ν)
        ((BalancedInduction.restriction (oldContentAppend D Sc cutoff ν i)).obj N).toFunctor w →ₗ[k]
      BalancedInduction.Obj (oldContentInclusion D Sc cutoff (i :: ν)) N.toFunctor
        ((append D Sc cutoff i).obj w) :=
  (oldContentRestrictionExtensionIso D Sc cutoff ν i N).hom.total w

/-- Restriction extension uses the original arrow with the same append functor. -/
theorem oldContentRestrictionExtensionLinear_tensor
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (w : OldCategory D Sc cutoff) (s : OldContentCategory D Sc cutoff ν)
    (g : s.obj ⟶ w) (b : N.obj ((oldContentAppend D Sc cutoff ν i).obj s)) :
    oldContentRestrictionExtensionLinear D Sc cutoff ν i N w
      (BalancedInduction.tensor (oldContentInclusion D Sc cutoff ν)
        ((BalancedInduction.restriction (oldContentAppend D Sc cutoff ν i)).obj N).toFunctor
        s g b) =
      BalancedInduction.tensor (oldContentInclusion D Sc cutoff (i :: ν)) N.toFunctor
        ((oldContentAppend D Sc cutoff ν i).obj s) ((append D Sc cutoff i).map g) b := by
  exact oldContentRestrictionExtensionIso_tensor D Sc cutoff ν i N w s g b

/-- Homogeneous components of the selected restriction extension on its raw coends. -/
def oldContentRestrictionExtensionComponent (p : ZMod 2)
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj (oldContentInclusion D Sc cutoff ν)
        ((BalancedInduction.restriction (oldContentAppend D Sc cutoff ν i)).obj N).toFunctor w →ₗ[k]
      BalancedInduction.Obj (oldContentInclusion D Sc cutoff (i :: ν)) N.toFunctor
        ((append D Sc cutoff i).obj w) :=
  (oldContentRestrictionExtensionIso D Sc cutoff ν i N).hom.app p w

/-- The chosen restriction comparison has zero odd component. -/
theorem oldContentRestrictionExtensionComponent_one
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (w : OldCategory D Sc cutoff) :
    oldContentRestrictionExtensionComponent D Sc cutoff ν i 1 N w = 0 := by
  have hu := BalancedInduction.adjunctionUnit_mem
    (oldContentInclusion D Sc cutoff (i :: ν)) N
  have hr := map_mem (BalancedInduction.restriction (oldContentAppend D Sc cutoff ν i)) hu
  have hi := map_mem (BalancedInduction.induction (oldContentInclusion D Sc cutoff ν)) hr
  have hc := BalancedInduction.adjunctionCounit_mem (oldContentInclusion D Sc cutoff ν)
    ((BalancedInduction.restriction (append D Sc cutoff i)).obj
      (BalancedInduction.induced (oldContentInclusion D Sc cutoff (i :: ν)) N))
  have hz := BalancedInduction.even_comp_app_one _ _ hi hc w
  have he := congrArg (fun f => f.app 1 w)
    (oldContentRestrictionExtensionIso_hom D Sc cutoff ν i N)
  exact he.trans hz

/-- Its degree-zero component is its whole selected map. -/
theorem oldContentRestrictionExtensionComponent_zero
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (w : OldCategory D Sc cutoff) :
    oldContentRestrictionExtensionComponent D Sc cutoff ν i 0 N w =
      oldContentRestrictionExtensionLinear D Sc cutoff ν i N w := by
  have hz := oldContentRestrictionExtensionComponent_one D Sc cutoff ν i N w
  change oldContentRestrictionExtensionComponent D Sc cutoff ν i 0 N w =
    oldContentRestrictionExtensionComponent D Sc cutoff ν i 0 N w +
      oldContentRestrictionExtensionComponent D Sc cutoff ν i 1 N w
  rw [hz, add_zero]

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Literal tensors of the selected content E/F charts

The same-colour and distinct-colour matrix comparisons in
DeformedMatrixComparison section 4 use the selected full-content
extension comparisons. Their tensor formulas insert the actual inclusion
unit and retain each old coefficient arrow.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open CategoryTheory.Functor
namespace OddMath.QuiverHecke.ELV
open CyclotomicCrossingTensor
universe u
namespace BalancedInduction
private theorem even_of_app_one_zero
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {M N : Superfunctor k C (SVec k)} (f : M ⟶ N) (h : ∀ w, f.app 1 w = 0) :
    f ∈ parity (R := k) _ _ 0 := by
  apply Superfunctor.mem_parity_iff_isHomogeneous.mpr
  intro q hq
  rcases parity_eq_zero_or_one q with rfl | rfl
  · exact (hq rfl).elim
  · funext w
    exact h w

private theorem moduleMap_total_of_app_one_zero
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {M N : Superfunctor k C (SVec k)} (f : M ⟶ N) (h : ∀ w, f.app 1 w = 0)
    (w : A) :
    (moduleMap J f).total w = mapComponent J f 0 w := by
  have hf := even_of_app_one_zero f h
  have hi := IsSuperfunctor.map_mem (F := induction J) hf
  have hz := Superfunctor.app_eq_zero_of_mem hi (by decide : (1 : ZMod 2) ≠ 0) w
  change mapComponent J f 1 w = 0 at hz
  change mapComponent J f 0 w + mapComponent J f 1 w = mapComponent J f 0 w
  rw [hz, add_zero]

private theorem restriction_comparison_total
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (Q : C ⥤ A) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    {M : Superfunctor k C (SVec k)} {N P : Superfunctor k A (SVec k)}
    (a : M ⟶ (restriction Q).obj N) (b : N ⟶ P) (v : C) (x : M.obj v) :
    (a ≫ (restriction Q).map b).total v x =
      b.total (Q.obj v) (a.total v x) := by
  rw [Superfunctor.comp_total]
  rfl
end BalancedInduction

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i : I)
local notation "J₀" => oldContentAppend D Sc cutoff ν i
local notation "J₁" => oldContentAppend D Sc cutoff (i :: ν) i
local notation "Q₀" => oldContentInclusion D Sc cutoff ν
local notation "Q₁" => oldContentInclusion D Sc cutoff (i :: ν)
local notation "J" => append D Sc cutoff i
local notation "Fc" => BalancedInduction.restriction (k := k) J₀
local notation "E" => BalancedInduction.induction (k := k) J
local notation "R₁" => BalancedInduction.restriction (k := k) Q₁

/-- Restriction of the selected E comparison on each literal tensor. -/
theorem oldContentAppendRestrictionLinear_tensor
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))
    (s : OldContentCategory D Sc cutoff ν)
    (t : OldContentCategory D Sc cutoff (i :: ν))
    (g : (J).obj s.obj ⟶ t.obj) (b : M.obj s) :
    oldContentAppendRestrictionLinear D Sc cutoff ν i M t
      (BalancedInduction.tensor J₀ M.toFunctor s g b) =
      BalancedInduction.inductionInsertedTensor Q₀ J M s t.obj g b := by
  rw [oldContentAppendRestrictionLinear_eq, LinearMap.comp_apply]
  have hu : oldContentAppendInclusionUnitLinear D Sc cutoff ν i M t
      (BalancedInduction.tensor J₀ M.toFunctor s g b) =
      BalancedInduction.tensor Q₁ (BalancedInduction.induced J₀ M).toFunctor t (𝟙 t.obj)
        (BalancedInduction.tensor J₀ M.toFunctor s g b) := rfl
  rw [hu, oldContentAppendExtensionLinear_tensor]
  exact congrArg (fun a : (J).obj s.obj ⟶ t.obj =>
    BalancedInduction.inductionInsertedTensor Q₀ J M s t.obj a b) (Category.comp_id g)

/-- The chosen preceding E/F chart keeps the selected E and F comparisons. -/
theorem oldContentEFRestrictionNaturalIso_hom_app
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k)) :
    (oldContentEFRestrictionNaturalIso D Sc cutoff ν i).hom.app N =
      (oldContentAppendRestrictionIso D Sc cutoff ν i ((Fc).obj N)).hom ≫
        (R₁).map ((E).map (oldContentRestrictionExtensionIso D Sc cutoff ν i N).hom) := by
  simp only [oldContentEFRestrictionNaturalIso, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app,
    whiskerRight_app, Functor.rightUnitor_inv_app, Functor.associator_inv_app,
    Category.id_comp, BalancedInduction.fullyFaithfulUnitNaturalIso,
    NatIso.ofComponents_hom_app, oldContentEFExtensionNaturalIso_hom_app,
    CategoryTheory.Functor.map_comp, Category.assoc,
    oldContentAppendRestrictionIso, Iso.trans_hom, Functor.mapIso_hom,
    oldContentExtensionUnitIso]
  rfl

/-- The selected preceding E/F comparison at its literal source and old target. -/
def oldContentEFRestrictionLinear
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) :
    BalancedInduction.Obj J₀ ((Fc).obj N).toFunctor t →ₗ[k]
      BalancedInduction.Obj J ((BalancedInduction.restriction J).obj
        (BalancedInduction.induced Q₁ N)).toFunctor t.obj :=
  ((oldContentEFRestrictionNaturalIso D Sc cutoff ν i).hom.app N).total t

/-- Its forward map keeps the chosen E and restriction-extension comparisons. -/
theorem oldContentEFRestrictionLinear_apply
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν))
    (z : BalancedInduction.Obj J₀ ((Fc).obj N).toFunctor t) :
    oldContentEFRestrictionLinear D Sc cutoff ν i N t z =
      BalancedInduction.mapComponent J (oldContentRestrictionExtensionIso D Sc cutoff ν i N).hom
        0 t.obj (oldContentAppendRestrictionLinear D Sc cutoff ν i ((Fc).obj N) t z) := by
  have hodd (w : OldCategory D Sc cutoff) :
      (oldContentRestrictionExtensionIso D Sc cutoff ν i N).hom.app 1 w = 0 :=
    oldContentRestrictionExtensionComponent_one D Sc cutoff ν i N w
  have hm := BalancedInduction.moduleMap_total_of_app_one_zero J
    (oldContentRestrictionExtensionIso D Sc cutoff ν i N).hom hodd t.obj
  have he := congrArg (fun f => f.total t z)
    (oldContentEFRestrictionNaturalIso_hom_app D Sc cutoff ν i N)
  have hc := BalancedInduction.restriction_comparison_total Q₁
    (oldContentAppendRestrictionIso D Sc cutoff ν i ((Fc).obj N)).hom
    ((E).map (oldContentRestrictionExtensionIso D Sc cutoff ν i N).hom) t z
  have hx := LinearMap.congr_fun hm
    ((oldContentAppendRestrictionIso D Sc cutoff ν i ((Fc).obj N)).hom.total t z)
  exact he.trans (hc.trans hx)

/-- The chosen E/F chart inserts precisely the inclusion unit in the old coefficient module. -/
theorem oldContentEFRestrictionLinear_tensor
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (s : OldContentCategory D Sc cutoff ν)
    (t : OldContentCategory D Sc cutoff (i :: ν))
    (g : (J).obj s.obj ⟶ t.obj) (b : N.obj ((J₀).obj s)) :
    oldContentEFRestrictionLinear D Sc cutoff ν i N t
      (BalancedInduction.tensor J₀ ((Fc).obj N).toFunctor s g b) =
      BalancedInduction.tensor J ((BalancedInduction.restriction J).obj
        (BalancedInduction.induced Q₁ N)).toFunctor s.obj g
        (BalancedInduction.tensor Q₁ N.toFunctor ((J₀).obj s)
          (𝟙 ((J).obj s.obj)) b) := by
  rw [oldContentEFRestrictionLinear_apply]
  have h₁ := oldContentAppendRestrictionLinear_tensor D Sc cutoff ν i ((Fc).obj N) s t g b
  have hStep := congrArg (BalancedInduction.mapComponent J
    (oldContentRestrictionExtensionIso D Sc cutoff ν i N).hom 0 t.obj) h₁
  refine hStep.trans ?_
  unfold BalancedInduction.inductionInsertedTensor
  have hm := BalancedInduction.mapComponent_tensor J
    (oldContentRestrictionExtensionIso D Sc cutoff ν i N).hom 0 t.obj s.obj g
    (BalancedInduction.tensor Q₀ ((Fc).obj N).toFunctor s (𝟙 s.obj) b)
  have hf := oldContentRestrictionExtensionComponent_zero D Sc cutoff ν i N s.obj
  have hs := oldContentRestrictionExtensionLinear_tensor D Sc cutoff ν i N s.obj s (𝟙 s.obj) b
  have he : oldContentRestrictionExtensionComponent D Sc cutoff ν i 0 N s.obj
      (BalancedInduction.tensor Q₀ ((Fc).obj N).toFunctor s (𝟙 s.obj) b) =
      BalancedInduction.tensor Q₁ N.toFunctor ((J₀).obj s) (𝟙 ((J).obj s.obj)) b := by
    rw [hf]
    exact hs.trans (congrArg (fun a => BalancedInduction.tensor Q₁ N.toFunctor
      ((J₀).obj s) a b) ((J).map_id s.obj))
  have hResult := hm.trans (congrArg₂ (fun a z => BalancedInduction.tensor J
    ((BalancedInduction.restriction J).obj (BalancedInduction.induced Q₁ N)).toFunctor
      s.obj a z) (twist_zero g) he)
  exact hResult

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Fixed-content height and finite matrix counts
DeformedMatrixComparison section 4 fixes one finite unit/cap count on an
exact-content block. The actual raw degree difference depends only on
that content; no equivalence between old and truncated categories is used.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The actual Cartan height of the supplied coefficient content. -/
def contentCrossingHeight (i : I) (β : Multiset I) : ℤ :=
  (cutoff i : ℤ) - (β.map (fun j => D.h i (D.α j))).sum

@[simp] theorem contentCrossingHeight_coe (i : I) (v : List I) :
    contentCrossingHeight D cutoff i (v : Multiset I) =
      (cutoff i : ℤ) - (v.map (fun j => D.h i (D.α j))).sum := rfl

/-- The prescribed unit count is the nonnegative part of the actual content height. -/
def contentUnitCount (i : I) (β : Multiset I) : ℕ :=
  (contentCrossingHeight D cutoff i β).toNat

/-- The prescribed cap count is the nonnegative part of the negative content height. -/
def contentCapCount (i : I) (β : Multiset I) : ℕ :=
  (-contentCrossingHeight D cutoff i β).toNat

theorem contentUnitCount_cast (i : I) (β : Multiset I)
    (h : 0 ≤ contentCrossingHeight D cutoff i β) :
    (contentUnitCount D cutoff i β : ℤ) = contentCrossingHeight D cutoff i β :=
  Int.toNat_of_nonneg h

theorem contentCapCount_cast (i : I) (β : Multiset I)
    (h : contentCrossingHeight D cutoff i β ≤ 0) :
    (contentCapCount D cutoff i β : ℤ) = -contentCrossingHeight D cutoff i β :=
  Int.toNat_of_nonneg (neg_nonneg.mpr h)

/-- The actual row-degree difference is exactly the fixed-content Cartan height. -/
theorem crossingHeight_eq_content (i : I) (v : List I) :
    (endpointQPDegree D cutoff i v : ℤ) - outputSDegree D i v =
      contentCrossingHeight D cutoff i (v : Multiset I) := by
  rw [contentCrossingHeight_coe, endpointQPDegree_sub_outputSDegree]

/-- Every actual untruncated content object has the same matrix height. -/
theorem oldContent_crossingHeight (i : I) (ν : List I)
    (v : OldContentCategory D Sc cutoff ν) :
    (endpointQPDegree D cutoff i v.obj.word : ℤ) - outputSDegree D i v.obj.word =
      contentCrossingHeight D cutoff i (ν : Multiset I) := by
  rw [crossingHeight_eq_content, Multiset.coe_eq_coe.mpr v.wordPerm]

/-- A single explicit count satisfies the positive matrix degree equality on the old block. -/
theorem oldContent_unitCount_height (i : I) (ν : List I)
    (h : 0 ≤ contentCrossingHeight D cutoff i (ν : Multiset I))
    (v : OldContentCategory D Sc cutoff ν) :
    endpointQPDegree D cutoff i v.obj.word = outputSDegree D i v.obj.word +
      contentUnitCount D cutoff i (ν : Multiset I) := by
  have hv := oldContent_crossingHeight D Sc cutoff i ν v
  have hm := contentUnitCount_cast D cutoff i (ν : Multiset I) h
  omega

/-- A single explicit count satisfies the negative matrix degree equality on the old block. -/
theorem oldContent_capCount_height (i : I) (ν : List I)
    (h : contentCrossingHeight D cutoff i (ν : Multiset I) ≤ 0)
    (v : OldContentCategory D Sc cutoff ν) :
    outputSDegree D i v.obj.word = endpointQPDegree D cutoff i v.obj.word +
      contentCapCount D cutoff i (ν : Multiset I) := by
  have hv := oldContent_crossingHeight D Sc cutoff i ν v
  have hm := contentCapCount_cast D cutoff i (ν : Multiset I) h
  omega

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end
