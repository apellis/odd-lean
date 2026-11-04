import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightPreCap
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightVacuumDot
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCapPreDotSigns

/-! # Raw whole-weight pre-dots on the regular probe

SwappedActionAssembly F2 and SwappedVacuumNonpositiveBubbles §1 (2):
retain the raw induction dot through the chosen source parity comparison,
with the same source chart as the normalized pre-Hom counit.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
open CyclotomicAction
universe u
local instance preDotHomPi {k : Type u} [CommRing k] (A B : PiSCat.{u,u,u+1} k) :
    PiSupercategory k (A ⟶ B) := PiTwoSupercategory.homPiLeft A B

private theorem preSource_dot_sign
    {I X k : Type u} [AddCommGroup X] [CommRing k] {D : SKM.Datum I X}
    (T : SKM.RouquierFamily (k := k) (B := PiSCat.{u,u,u+1} k) D)
    (W : X → PiSCat.{u,u,u+1} k) (i : I) (muM : X) {muP nuP : X}
    (h : -nuP + D.α i = -muP) (Z : SKM.homWeightSector T.obj W nuP muM) :
    SKM.homReservoirDot T W i muM h ((SKM.homContentPreF T W i muM h).obj Z) ≫
      (SKM.homContentPreInverseSource T W i muM h Z).hom =
    koszulSign (D.parity i) (SKM.leftAdjParity D i (-nuP)) •
      ((SKM.homContentPreInverseSource T W i muM h Z).hom ≫ ((T.dot i h ▷ T.F i h) ▷ Z)) := by
  simp only [SKM.homReservoirDot, SKM.homContentPreInverseSource, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom, PiSCat.associator_inv, SKM.homPre]
  erw [Category.comp_id]
  exact TwoSupercategory.super_interchange (T.dot_mem i h)
    ((SKM.homParityShiftDatum (k := k) (SKM.leftAdjParity D i (-nuP))).hom_mem (T.F i h ≫ Z))

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

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ) (Λ : X)
  (hc : ∀ i, (probeCutoff D m i : ℤ) = D.h i Λ)
  (W : X → PiSCat.{u,u,u+1} k) (muM : X) (i : I) {muP : X}
  (h : -Λ + D.α i = -muP) (H : ProbeVacuumCap.modulePiCategory D Sc m ⟶ W muM)
local notation "T" => probeOldRouquierFamily D Sc m Λ hc
local notation "N₀" => regularProbe D Sc m Λ
local notation "Z" => preCapInput D Sc m Λ hc W muM H

private theorem vacuumAdjParity (hP : 0 < probeCutoff D m i) :
    SKM.leftAdjParity D i (-Λ) = (probeCutoff D m i - 1) • D.parity i := by
  have he : D.h i (-Λ) = - (probeCutoff D m i : ℤ) := by
    rw [map_neg, ← hc i]
  rw [SKM.leftAdjParity, he, Int.cast_neg, Int.cast_natCast, nsmul_eq_mul,
    Nat.cast_sub (by omega : 1 ≤ probeCutoff D m i), Nat.cast_one]
  generalize (probeCutoff D m i : ZMod 2) = a
  generalize D.parity i = p
  fin_cases a <;> fin_cases p <;> decide

/-- The raw chosen pre-Hom dot commutes with the same source chart as
the chosen pre-Hom counit. Both source-shift Koszul factors are retained
and matched before the comparison. -/
theorem vacuumPreDot_source (hP : 0 < probeCutoff D m i) :
    (SKM.homReservoirDot T W i muM h ((SKM.homContentPreF T W i muM h).obj Z)).total N₀ ≫
      (vacuumPreSourceIso D Sc m Λ hc W muM i h H).hom =
    (vacuumPreSourceIso D Sc m Λ hc W muM i h H).hom ≫
      ProbeVacuumCap.shiftedPreDot D Sc m (W muM) i H := by
  have hs := congrArg (fun f => f.total N₀) (preSource_dot_sign T W i muM h Z)
  rw [Superfunctor.comp_total, total_zsmul, Superfunctor.comp_total, rightWhisker_total] at hs
  have hv := congrArg H.toFunctor.map (vacuumLoopDot_source D Sc m Λ i h)
  rw [Functor.map_comp, Functor.map_comp] at hv
  have hn : (ProbeVacuumCap.preSourceComponent D Sc m (W muM) i H).inv ≫
      ProbeVacuumCap.shiftedPreDot D Sc m (W muM) i H =
    koszulSign (D.parity i) (SKM.leftAdjParity D i (-Λ)) •
      (H.map (ProbeVacuumCap.moduleDot D Sc m i) ≫
        (ProbeVacuumCap.preSourceComponent D Sc m (W muM) i H).inv) := by
    rw [ProbeVacuumCap.shiftedPreDot_coordinates, Preadditive.comp_zsmul]
    simp only [ProbeVacuumCap.coordinatePreDotPower, pow_one,
      ProbeVacuumCap.preDotEnd_eq, Category.assoc, Iso.inv_hom_id_assoc,
      vacuumAdjParity D m Λ hc i hP]
  simp only [vacuumPreSourceIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Category.assoc]
  rw [reassoc_of% hs, Preadditive.zsmul_comp]
  change koszulSign (D.parity i) (SKM.leftAdjParity D i (-Λ)) •
    ((SKM.homContentPreInverseSource T W i muM h Z).hom.total N₀ ≫
      H.map (vacuumLoopDot D Sc m Λ i h) ≫
        H.map ((vacuumCapSourceIso D Sc m Λ i h).hom) ≫
          (ProbeVacuumCap.preSourceComponent D Sc m (W muM) i H).inv) = _
  rw [reassoc_of% hv, hn, Preadditive.comp_zsmul, Preadditive.comp_zsmul]

end OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
