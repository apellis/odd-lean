import OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendBraid
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionBraid

/-! # The old braid on direct triple induction

Brundan–Ellis Definition 1.5: the literal old prefix and suffix crossings
induce the braid on every balanced triple-append module. The superopposite
composition signs on the two three-crossing paths agree. Comparison with
three separately chosen induction functors remains a separate step.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open BalancedInduction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (i : I)

local notation "J" => append D Sc cutoff i

/-- Induce the physical prefix crossing after appending the third strand. -/
def oldTriplePrefixCross (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    End ((induction ((J ⋙ J) ⋙ J)).obj M) :=
  transformComponent ((equalCross_supernatural D Sc cutoff i).whiskerRight J) M

/-- Induce the physical suffix crossing at the already appended old word. -/
def oldTripleSuffixCross (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    End ((induction ((J ⋙ J) ⋙ J)).obj M) :=
  transformComponent ((equalCross_supernatural D Sc cutoff i).whiskerLeft J) M

/-- The whole balanced-module braid for the independent old crossings. -/
theorem oldTripleCross_braid (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    oldTriplePrefixCross D Sc cutoff i M ≫ oldTripleSuffixCross D Sc cutoff i M ≫
        oldTriplePrefixCross D Sc cutoff i M =
      oldTripleSuffixCross D Sc cutoff i M ≫ oldTriplePrefixCross D Sc cutoff i M ≫
        oldTripleSuffixCross D Sc cutoff i M := by
  exact transformComponent_braid ((J ⋙ J) ⋙ J)
    ((equalCross_supernatural D Sc cutoff i).whiskerRight J)
    ((equalCross_supernatural D Sc cutoff i).whiskerLeft J)
    (equalCrossComponent_braid D Sc cutoff i) M

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
