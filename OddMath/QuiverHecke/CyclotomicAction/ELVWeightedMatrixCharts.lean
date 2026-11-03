import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedMateComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVContentSingleLetterRelations

/-! # Source and target charts for weighted matrix transport

DeformedMatrixComparison (2), (4) requires invertible charts on the exact
source and target of the prescribed matrix. Induction preserves the genuine
restriction-square isomorphism, and the selected append comparison supplies
the quotient chart. No invertibility premise on a comparison map is imposed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  {R S : Superfunctor k C (SVec k)}

/-- The induction of a given module isomorphism on literal coends. -/
def inducedMapIsoLinearEquiv (e : R ≅ S) (w : A) :
    Obj J R.toFunctor w ≃ₗ[k] Obj J S.toFunctor w :=
  moduleIsoLinearEquiv ((induction J).mapIso e) w

/-- For an even given isomorphism, its induced total map is its exact
parity-zero coend component. -/
theorem inducedMapIsoLinearEquiv_hom (e : R ≅ S)
    (he : e.hom ∈ parity (R := k) _ _ 0) (w : A) :
    (inducedMapIsoLinearEquiv J e w).toLinearMap = mapComponent J e.hom 0 w := by
  have hp := IsSuperfunctor.map_mem (F := induction J) he
  have hz := Superfunctor.app_eq_zero_of_mem hp (by decide : (1 : ZMod 2) ≠ 0) w
  change ((induction J).map e.hom).total w = _
  rw [SuperNatTrans.total, hz, add_zero]
  rfl

end OddMath.QuiverHecke.ELVOld.BalancedInduction

namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (i : I)
local notation "J" => CyclotomicCrossingTensor.append D Sc cutoff i
local notation "Q" => oldTruncateFunctor D Sc cutoff N
local notation "T" => truncatedAppend D Sc cutoff N [i]
variable (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "RM" => weightedRestriction D Sc cutoff N M

/-- The inverse canonical restriction comparison has degree zero. -/
theorem weightedAppendRestrictionIso_inv_mem :
    (weightedAppendRestrictionIso D Sc cutoff N i M).inv ∈ parity (R := k) _ _ 0 :=
  Supercategory.inv_mem (weightedAppendRestrictionIso D Sc cutoff N i M)
    (weightedAppendRestrictionIso_hom_mem D Sc cutoff N i M)

/-- The selected append isomorphism is a linear equivalence of the literal
old and truncated induction coends. -/
def weightedAppendLinearEquiv (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj J (RM).toFunctor w ≃ₗ[k]
      BalancedInduction.Obj T M.toFunctor ((Q).obj w) :=
  moduleIsoLinearEquiv (appendWeightedModuleIso D Sc cutoff N i M) ((Q).obj w)

/-- Its forward map is the selected comparison, including all five legs. -/
theorem weightedAppendLinearEquiv_hom (w : OldCategory D Sc cutoff) :
    (weightedAppendLinearEquiv D Sc cutoff N i M w).toLinearMap =
      weightedAppendComparisonLinear D Sc cutoff N i M w := rfl

/-- The given input isomorphism is induced before the selected quotient
comparison. The input module stays independent of any restriction. -/
def weightedAppendSourceLinearEquiv
    (R : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (L : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
    (e : R ≅ weightedRestriction D Sc cutoff N L) (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj J R.toFunctor w ≃ₗ[k]
      BalancedInduction.Obj T L.toFunctor ((Q).obj w) :=
  (BalancedInduction.inducedMapIsoLinearEquiv J e w).trans
    (weightedAppendLinearEquiv D Sc cutoff N i L w)

theorem weightedAppendSourceLinearEquiv_hom
    (R : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (L : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
    (e : R ≅ weightedRestriction D Sc cutoff N L)
    (he : e.hom ∈ parity (R := k) _ _ 0) (w : OldCategory D Sc cutoff) :
    (weightedAppendSourceLinearEquiv D Sc cutoff N i R L e w).toLinearMap =
      weightedAppendSourceLinear D Sc cutoff N i R L e.hom w := by
  unfold weightedAppendSourceLinearEquiv
  rw [LinearEquiv.coe_trans, BalancedInduction.inducedMapIsoLinearEquiv_hom J e he w,
    weightedAppendLinearEquiv_hom]
  rfl

/-- The source chart first induces the inverse restriction-square isomorphism,
then applies the selected quotient comparison on the restricted module. -/
abbrev weightedMateSourceLinearEquiv (w : OldCategory D Sc cutoff) :=
  weightedAppendSourceLinearEquiv D Sc cutoff N i ((BalancedInduction.restriction J).obj RM)
    ((BalancedInduction.restriction T).obj M) (weightedAppendRestrictionIso D Sc cutoff N i M).symm w

/-- The chart uses exactly the source map in the ordered mate comparison. -/
theorem weightedMateSourceLinearEquiv_hom (w : OldCategory D Sc cutoff) :
    (weightedMateSourceLinearEquiv D Sc cutoff N i M w).toLinearMap =
      weightedAppendSourceLinear D Sc cutoff N i ((BalancedInduction.restriction J).obj RM)
        ((BalancedInduction.restriction T).obj M)
        (weightedAppendRestrictionIso D Sc cutoff N i M).inv w :=
  weightedAppendSourceLinearEquiv_hom D Sc cutoff N i ((BalancedInduction.restriction J).obj RM)
    ((BalancedInduction.restriction T).obj M) (weightedAppendRestrictionIso D Sc cutoff N i M).symm
    (weightedAppendRestrictionIso_inv_mem D Sc cutoff N i M) w

/-- The target chart is the same selected append comparison at the appended
old output word, exactly as in the ordered mate comparison. -/
abbrev weightedMateTargetLinearEquiv (w : OldCategory D Sc cutoff) :=
  weightedAppendLinearEquiv D Sc cutoff N i M ((J).obj w)

theorem weightedMateTargetLinearEquiv_hom (w : OldCategory D Sc cutoff) :
    (weightedMateTargetLinearEquiv D Sc cutoff N i M w).toLinearMap =
      weightedAppendComparisonLinear D Sc cutoff N i M ((J).obj w) := rfl

end OddMath.QuiverHecke.ELVOld
