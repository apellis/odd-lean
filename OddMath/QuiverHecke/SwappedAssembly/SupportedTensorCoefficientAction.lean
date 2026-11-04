import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorFamilies
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumTensorCoefficientMaps

/-! # Source coefficients on the supported tensor-vacuum words

SwappedVacuumCoordinates §§2–6: the full SYM action on the literal tensor
vacuum is retained through its input-weight equality and supported full
inclusion. Every specified path carries the same whiskered action, and
word Homs carry literal postcomposition with the original multiplication.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld VacuumTensorCoefficientMaps
universe u
local instance tensorCoefficientHomPi {k : Type u} [CommRing k] (A C : PiSCat.{u,u,u + 1} k) :
    PiSupercategory k (A ⟶ C) := PiTwoSupercategory.homPiLeft A C
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (L : I × ℕ → ℕ) (ΛP ΛR : X)
local notation "Tw" => parameterTwist D Sc
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "Z" => tensorVacuum D Sc m cutoff L ΛP ΛR

private def reindexCoefficientAction {x y z : X} (h : x = y)
    (F : probeOldWeightSpace D Tw m ΛP x ⟶ elvWeightSpace D Tw cutoff N ΛR z)
    (a : SYM D k →ₐ[k] End F) :
    SYM D k →ₐ[k] End (h ▸ F : probeOldWeightSpace D Tw m ΛP y ⟶
      elvWeightSpace D Tw cutoff N ΛR z) := by
  subst y
  exact a

private def tensorAmbientCoefficientAction : SYM D k →ₐ[k] End (Z).obj :=
  reindexCoefficientAction D Sc m cutoff L ΛP ΛR (probeWeight_vacuum D ΛP).symm
    (WeightTensorVacuum.selectedHom D Tw m cutoff ΛP ΛR L)
    (sourceCoefficientAction D Tw m cutoff L ΛP ΛR)

/-- The original SYM coefficient ring acts on the literal supported tensor vacuum. -/
def tensorVacuumCoefficientAction : SYM D k →ₐ[k] End Z where
  toFun a := ⟨tensorAmbientCoefficientAction D Sc m cutoff L ΛP ΛR a⟩
  map_one' := by
    apply InducedCategory.hom_ext
    exact (tensorAmbientCoefficientAction D Sc m cutoff L ΛP ΛR).map_one
  map_mul' a b := by
    apply InducedCategory.hom_ext
    exact (tensorAmbientCoefficientAction D Sc m cutoff L ΛP ΛR).map_mul a b
  map_zero' := by
    apply InducedCategory.hom_ext
    exact (tensorAmbientCoefficientAction D Sc m cutoff L ΛP ΛR).map_zero
  map_add' a b := by
    apply InducedCategory.hom_ext
    exact (tensorAmbientCoefficientAction D Sc m cutoff L ΛP ΛR).map_add a b
  commutes' r := by
    apply InducedCategory.hom_ext
    exact (tensorAmbientCoefficientAction D Sc m cutoff L ΛP ΛR).commutes r

/-- A literal supported path carries its coefficient by that same path functor. -/
def tensorPathCoefficientAction {l : List (Col I X)} {s : Sector I}
    (p : SPath l s (0,0)) : SYM D k →ₐ[k]
      End ((pathFunctor D Tw m cutoff N ΛP ΛR p).obj Z) :=
  (functorEndAction (pathFunctor D Tw m cutoff N ΛP ΛR p).toFunctor Z).comp
    (tensorVacuumCoefficientAction D Sc m cutoff L ΛP ΛR)

/-- Whole word Homs carry coefficients by postcomposition with the
path-whiskered literal tensor-vacuum map. -/
def tensorWordHomCoefficientAction {l : List (Col I X)} {s : Sector I}
    (p : SPath l s (0,0)) (G : H D Tw m cutoff N ΛP ΛR s) :
    SYM D k →ₐ[k] Module.End k (G ⟶ (pathFunctor D Tw m cutoff N ΛP ΛR p).obj Z) :=
  (postcompositionAlgHom G ((pathFunctor D Tw m cutoff N ΛP ΛR p).obj Z)).comp
    (tensorPathCoefficientAction D Sc m cutoff L ΛP ΛR p)

@[simp] theorem tensorWordHomCoefficientAction_apply {l : List (Col I X)} {s : Sector I}
    (p : SPath l s (0,0)) (G : H D Tw m cutoff N ΛP ΛR s)
    (a : SYM D k) (f : G ⟶ (pathFunctor D Tw m cutoff N ΛP ΛR p).obj Z) :
    tensorWordHomCoefficientAction D Sc m cutoff L ΛP ΛR p G a f =
      f ≫ tensorPathCoefficientAction D Sc m cutoff L ΛP ΛR p a := rfl

/-- The source family uses exactly the coefficient action on its chosen whole path object. -/
def tensorSourceCoefficientAction (s : List I) : SYM D k →ₐ[k]
    End (tensorSourceObject D Sc m cutoff ΛP ΛR L s) :=
  tensorPathCoefficientAction D Sc m cutoff L ΛP ΛR (tensorSourcePath D ΛP ΛR s)

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
