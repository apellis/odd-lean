import OddMath.QuiverHecke.CyclotomicAction.ELVOldInductionBraid
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridBraid

/-! # The chosen old crossing on three successive inductions

Brundan–Ellis Definition 1.5: the canonical induction-composition charts
identify the independently whiskered double-induction crossings with the
direct triple-induction crossings. Their braid is transported through
that same chart, retaining the prescribed negative crossing.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open BalancedInduction
universe u

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (i : I)
local notation "J" => append D Sc cutoff i

/-- The canonical prefix-first flattening of three chosen inductions. -/
def oldTripleFlattening (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (induction J).obj ((induction J).obj ((induction J).obj M)) ≅
      (induction ((J ⋙ J) ⋙ J)).obj M :=
  (induction J).mapIso ((inductionComp J J).app M) ≪≫
    (inductionComp (J ⋙ J) J).app M

theorem oldTripleFlattening_suffix (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (oldTripleFlattening D Sc cutoff i M).hom =
      (inductionComp J J).hom.app ((induction J).obj M) ≫
        (inductionComp J (J ⋙ J)).hom.app M := by
  exact inductionTripleFlattening_suffix J J J M

theorem oldTripleFlattening_prefix_cross
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (induction J).map (equalCrossOnDoubleInduction D Sc cutoff i M) ≫
        (oldTripleFlattening D Sc cutoff i M).hom =
      (oldTripleFlattening D Sc cutoff i M).hom ≫ oldTriplePrefixCross D Sc cutoff i M := by
  exact inductionTripleFlattening_prefix_cross J J J
    (equalCross_supernatural D Sc cutoff i) M

theorem oldTripleFlattening_suffix_cross
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    equalCrossOnDoubleInduction D Sc cutoff i ((induction J).obj M) ≫
        (oldTripleFlattening D Sc cutoff i M).hom =
      (oldTripleFlattening D Sc cutoff i M).hom ≫ oldTripleSuffixCross D Sc cutoff i M := by
  exact inductionTripleFlattening_suffix_cross J J J
    (equalCross_supernatural D Sc cutoff i) M

/-- Both independent double-induction crossings satisfy the whole braid. -/
theorem oldNestedCross_braid (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (induction J).map (equalCrossOnDoubleInduction D Sc cutoff i M) ≫
        equalCrossOnDoubleInduction D Sc cutoff i ((induction J).obj M) ≫
          (induction J).map (equalCrossOnDoubleInduction D Sc cutoff i M) =
      equalCrossOnDoubleInduction D Sc cutoff i ((induction J).obj M) ≫
        (induction J).map (equalCrossOnDoubleInduction D Sc cutoff i M) ≫
          equalCrossOnDoubleInduction D Sc cutoff i ((induction J).obj M) :=
  gridDoubleCrossComponent_braid J J J
    (equalCross_supernatural D Sc cutoff i) (equalCross_supernatural D Sc cutoff i)
    (equalCrossComponent_braid D Sc cutoff i) M

/-- Evaluation of the chosen signed crossing retains the prescribed minus. -/
theorem signedEqualInductionCross_total
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (signedEqualInductionCross D Sc cutoff i).total M =
      -equalCrossOnDoubleInduction D Sc cutoff i M := by
  change -((equalCrossOnDoubleInduction_supernatural D Sc cutoff i).toSuperNatTrans.app 0 M) +
      -((equalCrossOnDoubleInduction_supernatural D Sc cutoff i).toSuperNatTrans.app 1 M) = _
  rw [← neg_add]
  exact congrArg Neg.neg (OddMath.HomogeneousSuperfunctorIso.homogeneous_total
    (equalCrossOnDoubleInduction_supernatural D Sc cutoff i) M)

/-- The literal negative crossing satisfies the whole nested-induction braid. -/
theorem signedOldNestedCross_braid
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (induction J).map ((signedEqualInductionCross D Sc cutoff i).total M) ≫
        (signedEqualInductionCross D Sc cutoff i).total ((induction J).obj M) ≫
          (induction J).map ((signedEqualInductionCross D Sc cutoff i).total M) =
      (signedEqualInductionCross D Sc cutoff i).total ((induction J).obj M) ≫
        (induction J).map ((signedEqualInductionCross D Sc cutoff i).total M) ≫
          (signedEqualInductionCross D Sc cutoff i).total ((induction J).obj M) := by
  simp only [signedEqualInductionCross_total, Functor.map_neg,
    Preadditive.neg_comp, Preadditive.comp_neg, neg_neg]
  exact congrArg Neg.neg (oldNestedCross_braid D Sc cutoff i M)

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
