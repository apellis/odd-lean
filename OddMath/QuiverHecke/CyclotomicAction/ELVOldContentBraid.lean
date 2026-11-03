import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridBraid
import OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendBraid
import OddMath.QuiverHecke.CyclotomicAction.ELVContentMatrixEntries

/-! # The equal-colour braid on old content modules

Brundan–Ellis Definition 1.5: the selected negative crossings on three
successive fixed-content inductions satisfy the braid on every input
module. The literal old quotient supplies the source relation; no braid
or scalar-specialization faithfulness premise is imposed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i : I)
local notation "J" => oldContentAppend D Sc cutoff ν i
local notation "K" => oldContentAppend D Sc cutoff (i :: ν) i
local notation "L" => oldContentAppend D Sc cutoff (i :: i :: ν) i
local notation "γ" => oldContentEqualCross D Sc cutoff ν i
local notation "δ" => oldContentEqualCross D Sc cutoff (i :: ν) i
local notation "hγ" => oldContentMatrixCross_supernatural D Sc cutoff ν i
local notation "hδ" => oldContentMatrixCross_supernatural D Sc cutoff (i :: ν) i

/-- The old quotient braid retains all four consecutive content categories. -/
theorem oldContentEqualCross_braid (s : OldContentCategory D Sc cutoff ν) :
    (L).map (γ s) ≫ δ ((J).obj s) ≫ (L).map (γ s) =
      δ ((J).obj s) ≫ (L).map (γ s) ≫ δ ((J).obj s) :=
  equalCrossComponent_braid D Sc cutoff i s.obj

/-- The prescribed negative module crossings satisfy the entire braid. -/
theorem oldContentInductionCross_braid
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k)) :
    (induction L).map ((inductionModuleCross J K hγ).total M) ≫
        (inductionModuleCross K L hδ).total ((induction J).obj M) ≫
          (induction L).map ((inductionModuleCross J K hγ).total M) =
      (inductionModuleCross K L hδ).total ((induction J).obj M) ≫
        (induction L).map ((inductionModuleCross J K hγ).total M) ≫
          (inductionModuleCross K L hδ).total ((induction J).obj M) :=
  inductionModuleCross_braid J K L hγ hδ
    (oldContentEqualCross_braid D Sc cutoff ν i) M

end OddMath.QuiverHecke.ELVOld
