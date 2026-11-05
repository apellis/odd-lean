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

private theorem reindexCoefficientAction_ne_zero {x y z : X} (h : x = y)
    (F : probeOldWeightSpace D Tw m ΛP x ⟶ elvWeightSpace D Tw cutoff N ΛR z)
    (φ : SYM D k →ₐ[k] End F) (a : SYM D k) (ha : φ a ≠ 0) :
    reindexCoefficientAction D Sc m cutoff L ΛP ΛR h F φ a ≠ 0 := by
  subst y
  exact ha

/-- Passing to the supported full Hom and its formal input-weight presentation
retains every nonzero source coefficient endomorphism. -/
theorem tensorVacuumCoefficientAction_ne_zero (a : SYM D k)
    (ha : sourceCoefficientAction D Tw m cutoff L ΛP ΛR a ≠ 0) :
    tensorVacuumCoefficientAction D Sc m cutoff L ΛP ΛR a ≠ 0 := by
  intro hz
  have h := congrArg (fun f => f.hom) hz
  exact reindexCoefficientAction_ne_zero D Sc m cutoff L ΛP ΛR
    (probeWeight_vacuum D ΛP).symm
    (WeightTensorVacuum.selectedHom D Tw m cutoff ΛP ΛR L)
    (sourceCoefficientAction D Tw m cutoff L ΛP ΛR) a ha h

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

private def zeroObjectCoefficientAction {C : Type*} [Category* C] [Preadditive C] [Linear k C]
    (V : C) (hV : Limits.IsZero V) : SYM D k →ₐ[k] End V :=
  AlgHom.ofLinearMap 0 (hV.eq_of_src _ _) (fun _ _ => hV.eq_of_src _ _)

private def coefficientActionAtEquality {C : Type*} [Category* C] [Preadditive C] [Linear k C]
    {V V' : C} (h : V = V') (a : SYM D k →ₐ[k] End V) : SYM D k →ₐ[k] End V' := by
  subst V'
  exact a

/-- The chosen whole target family carries the source coefficient action at
its occupied vacuum sector and the unique action on each padded zero object. -/
def tensorTargetFamilyCoefficientAction (t : Sector I) : SYM D k →ₐ[k]
    End (tensorTargetFamily D Sc m cutoff ΛP ΛR L t) := by
  classical
  by_cases ht : t = (0,0)
  · subst t
    exact coefficientActionAtEquality D (tensorTargetFamily_zero D Sc m cutoff ΛP ΛR L).symm
      (tensorVacuumCoefficientAction D Sc m cutoff L ΛP ΛR)
  · exact zeroObjectCoefficientAction D _
      (tensorTargetFamily_isZero D Sc m cutoff ΛP ΛR L t ht)

/-- Every original formal endpoint of the chosen target family is retained
when whiskering the full coefficient by a path. -/
def tensorFamilyPathCoefficientAction {l : List (Col I X)} {s t : Sector I}
    (p : SPath l s t) : SYM D k →ₐ[k]
      End ((pathFunctor D Tw m cutoff N ΛP ΛR p).obj
        (tensorTargetFamily D Sc m cutoff ΛP ΛR L t)) :=
  (functorEndAction (pathFunctor D Tw m cutoff N ΛP ΛR p).toFunctor
    (tensorTargetFamily D Sc m cutoff ΛP ΛR L t)).comp
      (tensorTargetFamilyCoefficientAction D Sc m cutoff L ΛP ΛR t)

/-- The full chosen families carry the original coefficient ring on every
word-Hom component, with literal postcomposition on arbitrary source maps. -/
def tensorFamilyWordHomCoefficientAction {l : List (Col I X)} {s t : Sector I}
    (p : SPath l s t) (sourceWord : List I) : SYM D k →ₐ[k]
      Module.End k (tensorSourceFamily D Sc m cutoff ΛP ΛR L sourceWord s ⟶
        (pathFunctor D Tw m cutoff N ΛP ΛR p).obj
          (tensorTargetFamily D Sc m cutoff ΛP ΛR L t)) :=
  (postcompositionAlgHom (tensorSourceFamily D Sc m cutoff ΛP ΛR L sourceWord s)
    ((pathFunctor D Tw m cutoff N ΛP ΛR p).obj
      (tensorTargetFamily D Sc m cutoff ΛP ΛR L t))).comp
        (tensorFamilyPathCoefficientAction D Sc m cutoff L ΛP ΛR p)

@[simp] theorem tensorFamilyWordHomCoefficientAction_apply {l : List (Col I X)} {s t : Sector I}
    (p : SPath l s t) (sourceWord : List I) (a : SYM D k)
    (f : tensorSourceFamily D Sc m cutoff ΛP ΛR L sourceWord s ⟶
      (pathFunctor D Tw m cutoff N ΛP ΛR p).obj
        (tensorTargetFamily D Sc m cutoff ΛP ΛR L t)) :
    tensorFamilyWordHomCoefficientAction D Sc m cutoff L ΛP ΛR p sourceWord a f =
      f ≫ tensorFamilyPathCoefficientAction D Sc m cutoff L ΛP ΛR p a := rfl

private theorem reindexCoefficientAction_heq {x y z : X} (h : x = y)
    (F : probeOldWeightSpace D Tw m ΛP x ⟶ elvWeightSpace D Tw cutoff N ΛR z)
    (φ : SYM D k →ₐ[k] End F) (a : SYM D k) :
    HEq (reindexCoefficientAction D Sc m cutoff L ΛP ΛR h F φ a) (φ a) := by
  subst y
  rfl

omit [Fintype I] in
private theorem coefficientActionAtEquality_heq {C : Type*} [Category* C] [Preadditive C]
    [Linear k C] {V V' : C} (h : V = V') (φ : SYM D k →ₐ[k] End V) (a : SYM D k) :
    HEq (coefficientActionAtEquality D h φ a) (φ a) := by
  subst V'
  rfl

private theorem supportedHom_heq {V V' : H D Tw m cutoff N ΛP ΛR (0,0)} (h : V = V')
    {f : V ⟶ V} {f' : V' ⟶ V'} (hf : HEq f f') : HEq f.hom f'.hom := by
  subst V'
  cases hf
  rfl

/-- At the occupied vacuum sector, the chosen family coefficient is literally the
source coefficient on the selected tensor-vacuum Hom, across the input-weight
and supported-object equalities. -/
theorem tensorTargetFamilyCoefficientAction_zero_heq (a : SYM D k) :
    HEq (tensorTargetFamilyCoefficientAction D Sc m cutoff L ΛP ΛR (0,0) a).hom
      (sourceCoefficientAction D Tw m cutoff L ΛP ΛR a) := by
  have h1 : HEq (tensorTargetFamilyCoefficientAction D Sc m cutoff L ΛP ΛR (0,0) a)
      (tensorVacuumCoefficientAction D Sc m cutoff L ΛP ΛR a) := by
    unfold tensorTargetFamilyCoefficientAction
    simp only [↓reduceDIte]
    exact coefficientActionAtEquality_heq D _ _ a
  exact (supportedHom_heq D Sc m cutoff L ΛP ΛR (tensorTargetFamily_zero D Sc m cutoff ΛP ΛR L) h1).trans
    (reindexCoefficientAction_heq D Sc m cutoff L ΛP ΛR _ _ _ a)

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
