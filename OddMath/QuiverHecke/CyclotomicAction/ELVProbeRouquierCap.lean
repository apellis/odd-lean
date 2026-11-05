import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCapUniqueness
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCapPreDotSigns
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightSuperAdjunction
import OddMath.SKM.RouquierAdjacentLeftAdjunction

/-! # Comparing the inverse-defined Rouquier cap with the regular probe row

The existing left-adjunction route uses adjacent local Rouquier inverses,
not a separate Frobenius construction. At negative height the raw left cap
is an inverse row; its unit window forces its component at the regular
probe to be the specified native cap. The normalized counit additionally
retains the exact fixed scalar from `RouquierFTriangle`.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.ProbeVacuumCap
open BalancedInduction CyclotomicCrossingTensor
universe u

private theorem power_total
    {k : Type u} [CommRing k] {A B : PiSCat.{u,u,u+1} k}
    {F : A ⟶ B} (d : End F) (n : ℕ) (M : A) :
    (SKM.rouquierPower d n).total M = (show End (F.obj M) from d.total M) ^ n := by
  induction n with
  | zero => exact SuperNatTrans.id_total F.toFunctor M
  | succ n ih =>
    rw [SKM.rouquierPower, Superfunctor.comp_total, ih, pow_succ', End.mul_def]

private theorem whisker_total
    {k : Type u} [CommRing k] {A B R : PiSCat.{u,u,u+1} k}
    {F G : A ⟶ B} (η : F ⟶ G) (H : B ⟶ R) (M : A) :
    (η ▷ H).total M = H.map (η.total M) := by
  change H.map (η.app 0 M) + H.map (η.app 1 M) = H.map (η.app 0 M + η.app 1 M)
  exact (Functor.map_add H.toFunctor).symm

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ)
local notation "cut" => probeCutoff D m
local notation "N" => probeOldVacuumRegular D Sc m
local notation "K" => oldContentAppend D Sc cut []

/-- The existing ordinary right adjunction on the chosen native probe edge. -/
def appendRightAdjunction (i : I) :
    SKM.SuperAdjunction (k := k) (inductionCell D Sc m i) (restrictionCell D Sc m i) :=
  ordinaryEvenSuperAdjunction (inductionCell D Sc m i) (restrictionCell D Sc m i)
    (adjunction (K i)) (adjunctionUnit_mem (K i)) (adjunctionCounit_mem (K i))

section Local
variable (i : I)
  {A : PiSCat.{u,u,u+1} k}
  {E₀ : A ⟶ modulePiCategory D Sc m} {F₀ : modulePiCategory D Sc m ⟶ A}
  (A₀ : SKM.SuperAdjunction (k := k) E₀ F₀) (x₀ : End E₀)
  (t : End (E₀ ≫ inductionCell D Sc m i))
  (L : SKM.SuperRouquierLoc A₀ (appendRightAdjunction D Sc m i)
    x₀ (inductionDotCell D Sc m i) t (D.parity i) (-((probeCutoff D m i : ℕ) : ℤ)))

include L in

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
