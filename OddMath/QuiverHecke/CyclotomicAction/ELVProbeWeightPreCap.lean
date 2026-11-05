import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightVacuumCap
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCapPreCoordinates
import OddMath.SKM.RouquierHomPreCoordinates
import OddMath.SKM.RouquierNormalizedHomAdjunction

/-! # The normalized whole-weight pre-Hom cap on the regular probe

SwappedActionAssembly F2 and SwappedVacuumNonpositiveBubbles §1 (2):
insert the actual normalized probe counit into the prescribed pre-Hom
adjunction. Its regular-probe evaluation is the literal shifted native
cap through the source shift, whole-weight FE, and native source charts.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
open CyclotomicAction
universe u
local instance preCapHomPi {k : Type u} [CommRing k] (A B : PiSCat.{u,u,u+1} k) :
    PiSupercategory k (A ⟶ B) := PiTwoSupercategory.homPiLeft A B

private def totalEvaluation {k C A : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category A] [Preadditive A] [Linear k A] [Supercategory k A] (N : C) :
    Superfunctor k C A ⥤ A where
  obj F := F.obj N
  map f := f.total N
  map_id F := SuperNatTrans.id_total F.toFunctor N
  map_comp f g := Superfunctor.comp_total f g N

private theorem total_zsmul {k C A : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category A] [Preadditive A] [Linear k A] [Supercategory k A]
    {F G : Superfunctor k C A} (f : F ⟶ G) (z : ℤ) (N : C) :
    (z • f).total N = z • f.total N := by
  change z • f.app 0 N + z • f.app 1 N = z • (f.app 0 N + f.app 1 N)
  exact (smul_add _ _ _).symm

private theorem rightWhisker_total {k : Type u} [CommRing k]
    {A B C : PiSCat.{u,u,u+1} k} {F G : A ⟶ B} (f : F ⟶ G) (Z : B ⟶ C) (N : A) :
    (f ▷ Z).total N = Z.map (f.total N) := by
  change Z.map (f.app 0 N) + Z.map (f.app 1 N) = Z.map (f.app 0 N + f.app 1 N)
  exact (Functor.map_add Z.toFunctor).symm

private theorem preCounit_total
    {I X k : Type u} [AddCommGroup X] [CommRing k] {D : SKM.Datum I X}
    (T : SKM.RouquierFamily (k := k) (B := PiSCat.{u,u,u+1} k) D)
    (W : X → PiSCat.{u,u,u+1} k) (i : I) (muM : X) {muP nuP : X}
    (h : -nuP + D.α i = -muP) (Z : SKM.homWeightSector T.obj W nuP muM)
    (N : T.obj (-nuP)) :
    ((SKM.homContentPreAdjunction T W T.leftAdjoints i muM h).counit.app Z).total N =
      koszulSign (SKM.leftAdjParity D i (-nuP)) (SKM.leftAdjParity D i (-nuP)) •
        ((SKM.homContentPreInverseSource T W i muM h Z).hom.total N ≫
          Z.map ((T.leftAdjoints.adjL i h).counit.total N)) := by
  have hrow : (SKM.homContentPreAdjunction T W T.leftAdjoints i muM h).counit.app Z =
      koszulSign (SKM.leftAdjParity D i (-nuP)) (SKM.leftAdjParity D i (-nuP)) •
        ((SKM.homContentPreInverseSource T W i muM h Z).hom ≫
          (T.leftAdjoints.adjL i h).counit ▷ Z ≫ (leftUnitor Z).hom) := by
    simpa only [SKM.homContentPreInverseSource, Iso.trans_hom, Functor.mapIso_hom,
      Iso.symm_hom, SKM.homPre, Category.assoc, ← SKM.RouquierFamily.leftAdjoints_counit] using
        SKM.homContentPreAdjunction_leftAdjoints_counit_app T W i muM h Z
  rw [hrow]
  change (koszulSign (SKM.leftAdjParity D i (-nuP)) (SKM.leftAdjParity D i (-nuP)) •
    ((SKM.homContentPreInverseSource T W i muM h Z).hom ≫
      (T.leftAdjoints.adjL i h).counit ▷ Z ≫ (leftUnitor Z).hom)).total N = _
  rw [total_zsmul, Superfunctor.comp_total, Superfunctor.comp_total, rightWhisker_total]
  have hu : (leftUnitor Z).hom.total N = 𝟙 (Z.obj N) := SuperNatTrans.id_total Z.toFunctor N
  rw [hu]
  erw [Category.comp_id]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ) (Λ : X)
  (hc : ∀ i, (probeCutoff D m i : ℤ) = D.h i Λ)
  (W : X → PiSCat.{u,u,u+1} k) (muM : X) (i : I) {muP : X}
  (h : -Λ + D.α i = -muP) (H : ProbeVacuumCap.modulePiCategory D Sc m ⟶ W muM)
local notation "T" => probeOldRouquierFamily D Sc m Λ hc
local notation "N₀" => regularProbe D Sc m Λ

/-- The Hom input retains the whole weight product before selecting its
empty probe content and applying the given output functor. -/
def preCapInput : SKM.homWeightSector (T).obj W Λ muM :=
  (emptyProbe D Sc m Λ).comp H
local notation "Z" => preCapInput D Sc m Λ hc W muM H

/-- The actual shifted pre-Hom source is identified with the prescribed
native shifted source through all three selected source comparisons. -/
def vacuumPreSourceIso :
    (((SKM.homContentPreE (T) W i muM h).obj
      ((SKM.homContentPreF (T) W i muM h).obj Z)).obj N₀) ≅
      ProbeVacuumCap.shiftedPreSourceObject D Sc m (W muM) i H :=
  (totalEvaluation N₀).mapIso (SKM.homContentPreInverseSource (T) W i muM h Z) ≪≫
    H.toFunctor.mapIso (vacuumCapSourceIso D Sc m Λ i h) ≪≫
      (ProbeVacuumCap.preSourceComponent D Sc m (W muM) i H).symm

/-- The prescribed whole-weight pre-Hom counit evaluates to the native
shifted cap under the selected source chart. No cap compatibility or
moment premise is supplied. -/
theorem vacuumPreCounit_eq (hP : 0 < probeCutoff D m i) :
    ((SKM.homContentPreAdjunction (T) W (T).leftAdjoints i muM h).counit.app Z).total N₀ ≫
      H.map (eqToHom (emptyProbe_regular D Sc m Λ)) =
    (vacuumPreSourceIso D Sc m Λ hc W muM i h H).hom ≫
      ProbeVacuumCap.shiftedPreCap D Sc m (W muM) i hP H := by
  have hw := preCounit_total (T) W i muM h Z N₀
  have hout := congrArg (fun f => f ≫ H.map (eqToHom (emptyProbe_regular D Sc m Λ))) hw
  refine hout.trans ?_
  have hn := congrArg H.toFunctor.map (vacuumLeftCounit_eq D Sc m Λ i h hc hP)
  rw [CategoryTheory.Functor.map_zsmul, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp] at hn
  change (koszulSign (SKM.leftAdjParity D i (-Λ)) (SKM.leftAdjParity D i (-Λ)) •
      ((SKM.homContentPreInverseSource (T) W i muM h Z).hom.total N₀ ≫
        H.map ((emptyProbe D Sc m Λ).map (((T).leftAdjoints.adjL i h).counit.total N₀)))) ≫
        H.map (eqToHom (emptyProbe_regular D Sc m Λ)) = _
  rw [Preadditive.zsmul_comp, Category.assoc, ← Preadditive.comp_zsmul, hn,
    ProbeVacuumCap.shiftedPreCap_eq]
  simp only [vacuumPreSourceIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    totalEvaluation, Category.assoc, Iso.inv_hom_id_assoc]

end OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
