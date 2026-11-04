import OddMath.QuiverHecke.CyclotomicAction.ELVAbsentWindowInverseCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVRouquierFamily
import OddMath.SKM.RouquierHomPostPowers

/-! # The prescribed post-Hom unit at a reservoir content block

SwappedActionAssembly F2 and SwappedVacuumNonpositiveBubbles §1 (2):
evaluate the actual content-shifted post-Hom dotted unit, retaining its
output shift comparison and selected whole-weight successor chart.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor CyclotomicAction
universe u
local instance reservoirPostUnitHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

/-- The chosen dotted post-unit evaluates to the literal whole-weight
unit/dot word, after its prescribed adjacent-shift comparison. -/
theorem postCup_total
    {I X k : Type u} [AddCommGroup X] [CommRing k] {D : SKM.Datum I X}
    (T : X → PiSCat.{u,u,u+1} k)
    (W : SKM.RouquierFamily (k := k) (B := PiSCat.{u,u,u+1} k) D)
    (i : I) (β : I →₀ ℕ) (muP : X) {a b : X} (h : a + D.α i = b)
    (r : ℕ) (Z : SKM.homWeightSector T (W).obj muP a) (N : T (-muP)) :
    (SKM.homContentPostCup T W i β muP h r Z).total N ≫
      (SKM.homContentPostTargetIso T W i β muP h Z).hom.total N =
    ((W.adj i h).unit ≫ SKM.rouquierPower (W.dot i h) r ▷ W.F i h).total (Z.obj N) := by
  have hh := congrArg (fun f => f.total N)
    (SKM.homContentPostCup_coordinates T W i β muP h r Z)
  simp only [PiSCat.rightUnitor_inv, PiSCat.associator_inv, Category.id_comp] at hh
  erw [Superfunctor.comp_total, Superfunctor.comp_total] at hh
  erw [Superfunctor.comp_total]
  convert hh using 1; rfl

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (Λ : X) (hc : ∀ i, (cutoff i : ℤ) = D.h i Λ)
  (T : X → PiSCat.{u,u,u+1} k) (i : I) (β : I →₀ ℕ) (muP : X)
  {a b : X} (h : a + D.α i = b)
local notation "W" => elvRouquierFamily D Sc cutoff bound Λ hc

/-- The exact post-Hom cup at every reservoir output block is the given
stored-content unit column. The source Hom object and probe module are
arbitrary; no unit compatibility premise is supplied. -/
theorem reservoirPostCup_block (r : ℕ) (Z : SKM.homWeightSector T (W).obj muP a)
    (N : T (-muP)) (δ : WeightBlocks D Λ a) :
    ((SKM.homContentPostCup T W i β muP h r Z).total N) δ ≫
      ((SKM.homContentPostTargetIso T W i β muP h Z).hom.total N) δ ≫
        eqToHom (elvWeightFollowing_obj D Sc cutoff bound i Λ h δ (Z.obj N)) =
    unitDotColumn (elvBlockAppend D Sc cutoff bound i Λ h δ)
      (elvBlockGridDot_supernatural D Sc cutoff bound i Λ h δ) ((Z.obj N) δ) r := by
  have hp := congrFun (postCup_total T W i β muP h r Z N) δ
  change ((SKM.homContentPostCup T W i β muP h r Z).total N) δ ≫
      ((SKM.homContentPostTargetIso T W i β muP h Z).hom.total N) δ =
    ((((W).adj i h).unit ≫ SKM.rouquierPower ((W).dot i h) r ▷ (W).F i h).total (Z.obj N)) δ at hp
  have ht := congrArg (fun f => f ≫
    eqToHom (elvWeightFollowing_obj D Sc cutoff bound i Λ h δ (Z.obj N))) hp
  simpa only [Category.assoc] using
    ht.trans (elvWeightUnitPower_following_coordinates D Sc cutoff bound Λ i h (Z.obj N) δ r)

end OddMath.QuiverHecke.ELVOld
