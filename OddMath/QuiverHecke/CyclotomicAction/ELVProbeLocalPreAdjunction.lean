import OddMath.SKM.RouquierPreAdjunction
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeRouquierCap

/-! # Finite-local precomposition adjunction of the probe

For SwappedHomInversion §1, use the checked negative-height left adjunction
from the prescribed two adjacent local inverses on the given probe edge.
Its unshifted precomposition adjunction is constructed on the whole Hom
supercategory. Its counit evaluates to the already specified shifted cap,
including both diagonal Koszul factors. This supplies no arbitrary mate.
-/
noncomputable section
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
namespace OddMath.QuiverHecke.ELVOld.ProbeVacuumCap
open BalancedInduction CyclotomicCrossingTensor
universe u
local instance probeLocalPreAdjunctionPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

private def sourceIso {k : Type u} [CommRing k] {A B R : PiSCat.{u,u,u+1} k}
    (E : A ⟶ B) (F : B ⟶ A) (H : A ⟶ R) (σ : ZMod 2) :=
  (SKM.homPre (k := k) E).mapIso ((SKM.homParityShiftDatum (k := k) σ).iso (F ≫ H)) ≪≫
    (associator E F H).symm

private theorem total_zsmul {k : Type u} [CommRing k] {A R : PiSCat.{u,u,u+1} k}
    {F G : A ⟶ R} (η : F ⟶ G) (z : ℤ) (M : A) :
    (z • η).total M = z • η.total M := by
  change z • η.app 0 M + z • η.app 1 M = z • (η.app 0 M + η.app 1 M)
  exact (smul_add _ _ _).symm

private theorem whisker_total {k : Type u} [CommRing k] {A B R : PiSCat.{u,u,u+1} k}
    {F G : A ⟶ B} (η : F ⟶ G) (H : B ⟶ R) (M : A) :
    (η ▷ H).total M = H.map (η.total M) := by
  change H.map (η.app 0 M) + H.map (η.app 1 M) = H.map (η.app 0 M + η.app 1 M)
  exact (Functor.map_add H.toFunctor).symm

private theorem preCounit_total {k : Type u} [CommRing k] {A B R : PiSCat.{u,u,u+1} k}
    {E : A ⟶ B} {F : B ⟶ A} {σ : ZMod 2}
    (L : SKM.ShiftedSuperAdjunction (k := k) F E σ) (H : A ⟶ R) (M : A) :
    ((SKM.unshiftedPreAdjunction L R).counit.app H).total M =
      koszulSign σ σ • ((sourceIso E F H σ).hom.total M ≫ H.map (L.counit.total M)) := by
  rw [SKM.unshiftedPreAdjunction_counit_app, total_zsmul]
  have he : (sourceIso E F H σ).hom ≫ L.counit ▷ H ≫ (leftUnitor H).hom =
      E ◁ ((SKM.homParityShiftDatum (k := k) σ).iso (F ≫ H)).hom ≫
        (associator E F H).inv ≫ L.counit ▷ H ≫ (leftUnitor H).hom := by
    change (_ ≫ _) ≫ _ ≫ _ = _
    exact Category.assoc _ _ _
  rw [← he]
  rw [Superfunctor.comp_total, Superfunctor.comp_total, whisker_total]
  have hi : ((leftUnitor H).hom).total M = 𝟙 (H.obj M) := SuperNatTrans.id_total H.toFunctor M
  rw [hi]
  erw [Category.comp_id]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ)
local notation "cut" => probeCutoff D m
local notation "N" => probeOldVacuumRegular D Sc m
section Local
variable (i : I)
  {A : PiSCat.{u,u,u+1} k}
  {E₀ : A ⟶ modulePiCategory D Sc m} {F₀ : modulePiCategory D Sc m ⟶ A}
  (A₀ : SKM.SuperAdjunction (k := k) E₀ F₀) (x₀ : End E₀)
  (t : End (E₀ ≫ inductionCell D Sc m i))
  (L : SKM.SuperRouquierLoc A₀ (appendRightAdjunction D Sc m i)
    x₀ (inductionDotCell D Sc m i) t (D.parity i) (-((probeCutoff D m i : ℕ) : ℤ)))

section Adjacent
variable {Z : PiSCat.{u,u,u+1} k}
  {E₃ : raisedModulePiCategory D Sc m i ⟶ Z} {F₃ : Z ⟶ raisedModulePiCategory D Sc m i}
  (A₃ : SKM.SuperAdjunction (k := k) E₃ F₃) (x₃ : End E₃)
  (t' : End (inductionCell D Sc m i ≫ E₃))
  (U : SKM.SuperRouquierLoc (appendRightAdjunction D Sc m i) A₃
    (inductionDotCell D Sc m i) x₃ t' (D.parity i) (-((probeCutoff D m i : ℕ) : ℤ) + 2))
  (hP : 0 < probeCutoff D m i) (hsq : t ≫ t = 0) (hsq' : t' ≫ t' = 0)
  (hB : E₀ ◁ t' ≫ ((associator E₀ (inductionCell D Sc m i) E₃).inv ≫ t ▷ E₃ ≫
      (associator E₀ (inductionCell D Sc m i) E₃).hom) ≫ E₀ ◁ t' =
    ((associator E₀ (inductionCell D Sc m i) E₃).inv ≫ t ▷ E₃ ≫
      (associator E₀ (inductionCell D Sc m i) E₃).hom) ≫ E₀ ◁ t' ≫
      ((associator E₀ (inductionCell D Sc m i) E₃).inv ≫ t ▷ E₃ ≫
        (associator E₀ (inductionCell D Sc m i) E₃).hom))

end Adjacent
end Local
end OddMath.QuiverHecke.ELVOld.ProbeVacuumCap
