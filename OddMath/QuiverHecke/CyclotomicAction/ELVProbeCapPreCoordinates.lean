import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCapPrecomposition
import OddMath.SKM.RouquierShiftedAdjunction
import Mathlib.CategoryTheory.Conj

/-! # Canonical shifted coordinates for the probe cap

The source comparison in `SwappedActionAssembly.md`, §5 (A14), and
`RouquierHomPreCoordinates` is retained before evaluating the regular
probe. No left unit, triangle identities, or transpose-dot identification
are supplied by these coordinates.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.ProbeVacuumCap
open BalancedInduction CyclotomicCrossingTensor
universe u

local instance probeCapPreCoordinatesHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

private def evaluation {k : Type u} [CommRing k] {C R : Type*}
    [Category C] [Category R] [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive R] [Linear k R] [Supercategory k R] (M : C) :
    Superfunctor k C R ⥤ R where
  obj F := F.obj M
  map f := f.total M
  map_id F := SuperNatTrans.id_total F.toFunctor M
  map_comp f g := Superfunctor.comp_total f g M

private theorem total_mem {k : Type u} [CommRing k] {C R : Type*}
    [Category C] [Category R] [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive R] [Linear k R] [Supercategory k R]
    {F G : Superfunctor k C R} {p : ZMod 2} {f : F ⟶ G}
    (hf : f ∈ parity (R := k) _ _ p) (M : C) :
    f.total M ∈ parity (R := k) _ _ p := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hf (by decide : (1 : ZMod 2) ≠ 0), add_zero]
    exact f.app_mem 0 M
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hf (by decide : (0 : ZMod 2) ≠ 1), zero_add]
    exact f.app_mem 1 M

private instance evaluationAdditive {k : Type u} [CommRing k] {C R : Type*}
    [Category C] [Category R] [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive R] [Linear k R] [Supercategory k R] (M : C) :
    (evaluation (k := k) (R := R) M).Additive where
  map_add {F G f g} := by
    change (f.app 0 M + g.app 0 M) + (f.app 1 M + g.app 1 M) =
      (f.app 0 M + f.app 1 M) + (g.app 0 M + g.app 1 M)
    abel

private instance evaluationLinear {k : Type u} [CommRing k] {C R : Type*}
    [Category C] [Category R] [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive R] [Linear k R] [Supercategory k R] (M : C) :
    (evaluation (k := k) (R := R) M).Linear k where
  map_smul f r := by
    change r • f.app 0 M + r • f.app 1 M = r • (f.app 0 M + f.app 1 M)
    exact (smul_add _ _ _).symm

private instance evaluationSuper {k : Type u} [CommRing k] {C R : Type*}
    [Category C] [Category R] [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive R] [Linear k R] [Supercategory k R] (M : C) :
    IsSuperfunctor k (evaluation (k := k) (R := R) M) where
  map_mem hf := total_mem hf M

private def sourceCapRow
    {k : Type u} [CommRing k] {A R : PiSCat.{u,u,u+1} k}
    {F : A ⟶ A} {S : A ⟶ R} (H : A ⟶ R) (e : S ≅ F ≫ H)
    (η : F ⟶ 𝟙 A) : S ⟶ H := e.hom ≫ (η ▷ H) ≫ (leftUnitor H).hom

private theorem sourceCapRow_mem
    {k : Type u} [CommRing k] {A R : PiSCat.{u,u,u+1} k}
    {F : A ⟶ A} {S : A ⟶ R} (H : A ⟶ R) (e : S ≅ F ≫ H)
    (η : F ⟶ 𝟙 A) {σ : ZMod 2}
    (he : e.hom ∈ parity (R := k) _ _ σ) (hη : η ∈ parity (R := k) _ _ σ) :
    sourceCapRow H e η ∈ parity (R := k) _ _ 0 := by
  simpa only [sourceCapRow, add_zero, SKM.zmod2_add_self] using
    comp_mem he (comp_mem (TwoSupercategory.whiskerRight_mem H hη)
      (TwoSupercategory.leftUnitor_hom_mem (R := k) H))

private theorem sourceCapRow_total
    {k : Type u} [CommRing k] {A R : PiSCat.{u,u,u+1} k}
    {F : A ⟶ A} {S : A ⟶ R} (H : A ⟶ R) (e : S ≅ F ≫ H)
    (η : F ⟶ 𝟙 A) (M : A) :
    (sourceCapRow H e η).total M =
      ((evaluation M).mapIso e).hom ≫ H.map (η.total M) := by
  rw [sourceCapRow, Superfunctor.comp_total, Superfunctor.comp_total]
  have hη : (η ▷ H).total M = H.map (η.total M) := by
    change H.map (η.app 0 M) + H.map (η.app 1 M) = H.map (η.app 0 M + η.app 1 M)
    exact (Functor.map_add H.toFunctor).symm
  have hid : ((leftUnitor H).hom).total M = 𝟙 (H.obj M) := SuperNatTrans.id_total H.toFunctor M
  rw [hη, hid]
  change e.hom.total M ≫ (H.map (η.total M) ≫ 𝟙 (H.obj M)) =
    e.hom.total M ≫ H.map (η.total M)
  erw [Category.comp_id]

private theorem coordinate_polynomial {C : Type*} [Category C] [Preadditive C]
    {S T : C} (e : T ≅ S) (d : End S) (n : ℕ) (h : (d ^ 2 + 1) ^ n = 0) :
    ((e.symm.conj d) ^ 2 + 1) ^ n = 0 := by
  let c : End S →+* End T := {
    toFun := e.symm.conj
    map_one' := map_one e.symm.conj
    map_mul' := fun a b => map_mul e.symm.conj a b
    map_zero' := by simp [Iso.conj_apply]
    map_add' := fun a b => by
      change e.hom ≫ (a + b) ≫ e.inv = _
      rw [Preadditive.add_comp, Preadditive.comp_add]
      rfl }
  have hc := congrArg c h
  simp only [map_pow, map_add, map_one, map_zero] at hc
  exact hc

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ)
local notation "cut" => probeCutoff D m
local notation "N" => probeOldVacuumRegular D Sc m
local notation "K" => oldContentAppend D Sc cut []

/-- The module category after adjoining the moving colour. -/
def raisedModulePiCategory (i : I) : PiSCat.{u,u,u+1} k where
  toSCat := SCat.of k (Superfunctor k (OldContentCategory D Sc cut [i]) (SVec k))
  pi := supermodulePiSupercategory

/-- The same chosen induction functor, between its actual content categories. -/
def inductionCell (i : I) : modulePiCategory D Sc m ⟶ raisedModulePiCategory D Sc m i :=
  show Superfunctor k (Superfunctor k (OldContentCategory D Sc cut []) (SVec k))
    (Superfunctor k (OldContentCategory D Sc cut [i]) (SVec k)) from ⟨induction (K i)⟩

/-- The same chosen restriction functor in the reverse direction. -/
def restrictionCell (i : I) : raisedModulePiCategory D Sc m i ⟶ modulePiCategory D Sc m :=
  show Superfunctor k (Superfunctor k (OldContentCategory D Sc cut [i]) (SVec k))
    (Superfunctor k (OldContentCategory D Sc cut []) (SVec k)) from ⟨restriction (K i)⟩

/-- The canonical source shift removal followed by the existing even
associator, in exactly the order of `homContentPreInverseSource`. -/
def preSource (R : PiSCat.{u,u,u+1} k) (i : I)
    (H : modulePiCategory D Sc m ⟶ R) :=
  (SKM.homPre (k := k) (inductionCell D Sc m i)).mapIso
    ((SKM.homParityShiftDatum (k := k) ((cut i - 1) • D.parity i)).iso
      (restrictionCell D Sc m i ≫ H)) ≪≫
    (associator (inductionCell D Sc m i) (restrictionCell D Sc m i) H).symm

omit [Fintype I] in
/-- Source shift removal retains its last-row degree; it is not an even
identification of the two input objects. -/
theorem preSource_mem (R : PiSCat.{u,u,u+1} k) (i : I)
    (H : modulePiCategory D Sc m ⟶ R) :
    (preSource D Sc m R i H).hom ∈ parity (R := k) _ _ ((cut i - 1) • D.parity i) := by
  simpa only [preSource, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, add_zero] using
    comp_mem (IsSuperfunctor.map_mem (F := SKM.homPre (k := k) (inductionCell D Sc m i))
      ((SKM.homParityShiftDatum (k := k) ((cut i - 1) • D.parity i)).hom_mem
        (restrictionCell D Sc m i ≫ H)))
      (inv_mem _ (TwoSupercategory.associator_hom_mem (R := k) _ _ _))

/-- The literal parity-shifted precomposition block evaluated at the probe. -/
def shiftedPreSourceObject (R : PiSCat.{u,u,u+1} k) (i : I)
    (H : modulePiCategory D Sc m ⟶ R) : R :=
  ((SKM.homPre (k := k) (inductionCell D Sc m i)).obj
    ((SKM.homParityShift (k := k) ((cut i - 1) • D.parity i)).obj
      (restrictionCell D Sc m i ≫ H))).obj N

/-- Evaluate that exact comparison on the original regular probe. -/
def preSourceComponent (R : PiSCat.{u,u,u+1} k) (i : I)
    (H : modulePiCategory D Sc m ⟶ R) :
    shiftedPreSourceObject D Sc m R i H ≅ H.obj (source D Sc m i) :=
  (evaluation N).mapIso (preSource D Sc m R i H)

/-- The cap row on the chosen shifted precomposition block. This map uses
the prescribed cap and source comparison, but asserts no left adjunction. -/
def shiftedPreCap (R : PiSCat.{u,u,u+1} k) (i : I) (hP : 0 < cut i)
    (H : modulePiCategory D Sc m ⟶ R) :
    shiftedPreSourceObject D Sc m R i H ⟶ H.obj N :=
  (sourceCapRow H (preSource D Sc m R i H) (capCell D Sc m i hP)).total N

/-- The exact prescribed cap after the canonical input comparison. -/
theorem shiftedPreCap_eq (R : PiSCat.{u,u,u+1} k) (i : I) (hP : 0 < cut i)
    (H : modulePiCategory D Sc m ⟶ R) :
    shiftedPreCap D Sc m R i hP H =
      (preSourceComponent D Sc m R i H).hom ≫ H.map (cap D Sc m i hP) := by
  rw [shiftedPreCap, sourceCapRow_total, capCell_total]
  rfl

/-- Each power of the same precomposition dot in those source coordinates. -/
def coordinatePreDotPower (R : PiSCat.{u,u,u+1} k) (i : I)
    (H : modulePiCategory D Sc m ⟶ R) (a : ℕ) : End (shiftedPreSourceObject D Sc m R i H) :=
  (preSourceComponent D Sc m R i H).hom ≫
    (preDotEnd D Sc m R i H ^ a) ≫ (preSourceComponent D Sc m R i H).inv

/-- In the chosen source coordinates the normalized cap is even, because
the source comparison and prescribed cap both have degree `(P-1)p`. -/
theorem shiftedPreCap_mem (R : PiSCat.{u,u,u+1} k) (i : I) (hP : 0 < cut i)
    (H : modulePiCategory D Sc m ⟶ R) :
    shiftedPreCap D Sc m R i hP H ∈ parity (R := k) _ _ 0 := by
  exact total_mem (sourceCapRow_mem H (preSource D Sc m R i H)
    (capCell D Sc m i hP) (preSource_mem D Sc m R i H) (capCell_mem D Sc m i hP)) N

/-- The same signed polynomial survives canonical source parity transport. -/
theorem coordinatePreDot_odd_polynomial (R : PiSCat.{u,u,u+1} k) (i : I) (hi : D.parity i = 1)
    (H : modulePiCategory D Sc m ⟶ R) :
    (coordinatePreDotPower D Sc m R i H 1 ^ 2 + 1) ^ m i = 0 := by
  simpa only [coordinatePreDotPower, pow_one, Iso.conj_apply, Iso.symm_inv, Iso.symm_hom] using
    coordinate_polynomial (preSourceComponent D Sc m R i H) (preDotEnd D Sc m R i H) (m i)
      (preDot_odd_polynomial D Sc m R i hi H)

end OddMath.QuiverHecke.ELVOld.ProbeVacuumCap
