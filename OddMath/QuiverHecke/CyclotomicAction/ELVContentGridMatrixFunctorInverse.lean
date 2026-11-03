import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridMatrixFunctor
import OddMath.QuiverHecke.CyclotomicAction.ELVContentGridMatrixInverse

/-! # Input-natural inverses of the chosen content E/F matrices

Brundan--Ellis (1.13)--(1.14), DeformedMatrixComparison (4), (5).
The prescribed matrix module inverses assemble naturally on all input
maps, retaining their canonical finite-family endpoint comparisons.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor BalancedInduction
universe u v
private def natIsoFromHom {C : Type u} {D : Type v} [Category C] [Category D]
    {F G : C ⥤ D} (t : F ⟶ G) (e : ∀ N, F.obj N ≅ G.obj N)
    (he : ∀ N, (e N).hom = t.app N) : F ≅ G :=
  NatIso.ofComponents e (by
    intro M N f
    rw [he M, he N]
    exact t.naturality f)
private theorem natIsoFromHom_hom {C : Type u} {D : Type v} [Category C] [Category D]
    {F G : C ⥤ D} (t : F ⟶ G) (e : ∀ N, F.obj N ≅ G.obj N)
    (he : ∀ N, (e N).hom = t.app N) : (natIsoFromHom t e he).hom = t := by
  ext N
  exact he N

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i : I)
local notation "J₀" => oldContentAppend D Sc cutoff ν i
local notation "J₁" => oldContentAppend D Sc cutoff (i :: ν) i
local notation "mu" => contentUnitCount D cutoff i ((i :: ν : List I) : Multiset I)
local notation "mc" => contentCapCount D cutoff i ((i :: ν : List I) : Multiset I)

/-- The prescribed chosen content unit matrix is input-natural, including on odd maps. -/
def oldContentGridUnitMatrixFunctorNatIso
    (hh : 0 ≤ contentCrossingHeight D cutoff i ((i :: ν : List I) : Multiset I)) :
    gridUnitMatrixSourceFunctor (k := k) J₀ (D.parity i) mu ≅ induction (k := k) J₁ ⋙ restriction (k := k) J₁ :=
  natIsoFromHom (gridUnitMatrixInputNatTrans J₀ J₁
    (oldContentMatrixCross_supernatural D Sc cutoff ν i)
    (oldContentAppendDot_supernatural D Sc cutoff (i :: ν) i) mu)
    (fun N => gridUnitMatrixInputComponentIso J₀ J₁ mu N
      (oldContentGridUnitMatrixIso D Sc cutoff ν i N hh))
    (fun N => gridUnitMatrixInputComponentIso_hom J₀ J₁
      (oldContentMatrixCross_supernatural D Sc cutoff ν i)
      (oldContentAppendDot_supernatural D Sc cutoff (i :: ν) i) mu N _
      (oldContentGridUnitMatrixIso_hom D Sc cutoff ν i N hh))

/-- The prescribed chosen content cap matrix is input-natural, including on odd maps. -/
def oldContentGridCapMatrixFunctorNatIso
    (hh : contentCrossingHeight D cutoff i ((i :: ν : List I) : Multiset I) ≤ 0) :
    restriction (k := k) J₀ ⋙ induction (k := k) J₀ ≅ gridCapMatrixTargetFunctor (k := k) J₁ (D.parity i) mc :=
  natIsoFromHom (gridCapMatrixInputNatTrans J₀ J₁
    (oldContentMatrixCross_supernatural D Sc cutoff ν i)
    (oldContentAppendDot_supernatural D Sc cutoff ν i) mc)
    (fun N => gridCapMatrixInputComponentIso J₀ J₁ mc N
      (oldContentGridCapMatrixIso D Sc cutoff ν i N hh))
    (fun N => gridCapMatrixInputComponentIso_hom J₀ J₁
      (oldContentMatrixCross_supernatural D Sc cutoff ν i)
      (oldContentAppendDot_supernatural D Sc cutoff ν i) mc N _
      (oldContentGridCapMatrixIso_hom D Sc cutoff ν i N hh))

theorem oldContentGridUnitMatrixFunctorNatIso_hom
    (hh : 0 ≤ contentCrossingHeight D cutoff i ((i :: ν : List I) : Multiset I)) :
    (oldContentGridUnitMatrixFunctorNatIso D Sc cutoff ν i hh).hom =
      gridUnitMatrixInputNatTrans J₀ J₁ (oldContentMatrixCross_supernatural D Sc cutoff ν i)
        (oldContentAppendDot_supernatural D Sc cutoff (i :: ν) i) mu :=
  natIsoFromHom_hom _ _ _
theorem oldContentGridCapMatrixFunctorNatIso_hom
    (hh : contentCrossingHeight D cutoff i ((i :: ν : List I) : Multiset I) ≤ 0) :
    (oldContentGridCapMatrixFunctorNatIso D Sc cutoff ν i hh).hom =
      gridCapMatrixInputNatTrans J₀ J₁ (oldContentMatrixCross_supernatural D Sc cutoff ν i)
        (oldContentAppendDot_supernatural D Sc cutoff ν i) mc :=
  natIsoFromHom_hom _ _ _

/-- The given unit module matrix, retaining the explicit literal-family endpoint. -/
theorem oldContentGridUnitMatrixFunctorNatIso_hom_app
    (hh : 0 ≤ contentCrossingHeight D cutoff i ((i :: ν : List I) : Multiset I))
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k)) :
    (oldContentGridUnitMatrixFunctorNatIso D Sc cutoff ν i hh).hom.app N =
      eqToHom (gridUnitMatrixSourceFunctor_obj J₀ (D.parity i) mu N) ≫
        gridUnitMatrixModuleMap J₀ J₁ (oldContentMatrixCross_supernatural D Sc cutoff ν i)
          (oldContentAppendDot_supernatural D Sc cutoff (i :: ν) i) N mu := by
  rw [oldContentGridUnitMatrixFunctorNatIso_hom]
  exact gridUnitMatrixInputNatTrans_app J₀ J₁ _ _ mu N
/-- The given cap module matrix, retaining the explicit literal-family endpoint. -/
theorem oldContentGridCapMatrixFunctorNatIso_hom_app
    (hh : contentCrossingHeight D cutoff i ((i :: ν : List I) : Multiset I) ≤ 0)
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k)) :
    (oldContentGridCapMatrixFunctorNatIso D Sc cutoff ν i hh).hom.app N =
      gridCapMatrixModuleMap J₀ J₁ (oldContentMatrixCross_supernatural D Sc cutoff ν i)
        (oldContentAppendDot_supernatural D Sc cutoff ν i) N mc ≫
          eqToHom (gridCapMatrixTargetFunctor_obj J₁ (D.parity i) mc N).symm := by
  rw [oldContentGridCapMatrixFunctorNatIso_hom]
  exact gridCapMatrixInputNatTrans_app J₀ J₁ _ _ mc N

/-- Both directions of the input-natural unit isomorphism are even. -/
theorem oldContentGridUnitMatrixFunctorNatIso_even
    (hh : 0 ≤ contentCrossingHeight D cutoff i ((i :: ν : List I) : Multiset I))
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k)) :
    (oldContentGridUnitMatrixFunctorNatIso D Sc cutoff ν i hh).hom.app N ∈ parity (R := k) _ _ 0 ∧
      (oldContentGridUnitMatrixFunctorNatIso D Sc cutoff ν i hh).inv.app N ∈ parity (R := k) _ _ 0 := by
  have h : (oldContentGridUnitMatrixFunctorNatIso D Sc cutoff ν i hh).hom.app N ∈
      parity (R := k) _ _ 0 := by
    rw [oldContentGridUnitMatrixFunctorNatIso_hom]
    exact gridUnitMatrixInputNatTrans_app_mem J₀ J₁ _ _ mu N
  exact ⟨h, inv_mem ((oldContentGridUnitMatrixFunctorNatIso D Sc cutoff ν i hh).app N) h⟩
/-- Both directions of the input-natural cap isomorphism are even. -/
theorem oldContentGridCapMatrixFunctorNatIso_even
    (hh : contentCrossingHeight D cutoff i ((i :: ν :List I) : Multiset I) ≤ 0)
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k)) :
    (oldContentGridCapMatrixFunctorNatIso D Sc cutoff ν i hh).hom.app N ∈ parity (R := k) _ _ 0 ∧
      (oldContentGridCapMatrixFunctorNatIso D Sc cutoff ν i hh).inv.app N ∈ parity (R := k) _ _ 0 := by
  have h : (oldContentGridCapMatrixFunctorNatIso D Sc cutoff ν i hh).hom.app N ∈
      parity (R := k) _ _ 0 := by
    rw [oldContentGridCapMatrixFunctorNatIso_hom]
    exact gridCapMatrixInputNatTrans_app_mem J₀ J₁ _ _ mc N
  exact ⟨h, inv_mem ((oldContentGridCapMatrixFunctorNatIso D Sc cutoff ν i hh).app N) h⟩

end OddMath.QuiverHecke.ELVOld
