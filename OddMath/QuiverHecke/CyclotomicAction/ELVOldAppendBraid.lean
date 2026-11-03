import OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendCrossing
import OddMath.QuiverHecke.CyclotomicAction.Braid

/-! # The equal-colour braid in the untruncated old quotient

Brundan–Ellis Definition 1.5, the same-colour braid: the two independently
appended old crossings satisfy the braid before induction. This is the
coefficient input for the evaluated probe's three-induction relation.
No coefficient-power truncation or scalar faithfulness is used.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem affineEqual_braid (v : List I) (i : I) :
    (crossLast D Sc v i i ▷ (pres D Sc).obj (ob D [i])) ≫
        crossLast D Sc (v ++ [i]) i i ≫
          (crossLast D Sc v i i ▷ (pres D Sc).obj (ob D [i])) =
      crossLast D Sc (v ++ [i]) i i ≫
        (crossLast D Sc v i i ▷ (pres D Sc).obj (ob D [i])) ≫
          crossLast D Sc (v ++ [i]) i i := by
  rw [crossLast_whiskerRight_cl, crossLast, cl_comp_three, cl_comp_three]
  refine (braid_ne_gen D Sc v [] i i i (by simp) ?_ ?_ ?_ ?_ _ _).symm <;>
    simp [List.append_assoc]

/-- The literal prefix and suffix old crossings satisfy the three-strand braid. -/
theorem equalCrossComponent_braid (i : I) (s : OldCategory D Sc cutoff) :
    (append D Sc cutoff i).map (equalCrossComponent D Sc cutoff i s) ≫
        equalCrossComponent D Sc cutoff i ((append D Sc cutoff i).obj s) ≫
          (append D Sc cutoff i).map (equalCrossComponent D Sc cutoff i s) =
      equalCrossComponent D Sc cutoff i ((append D Sc cutoff i).obj s) ≫
        (append D Sc cutoff i).map (equalCrossComponent D Sc cutoff i s) ≫
          equalCrossComponent D Sc cutoff i ((append D Sc cutoff i).obj s) := by
  change (ideal D Sc cutoff (s.word ++ [i] ++ [i] ++ [i])
      (s.word ++ [i] ++ [i] ++ [i])).mkQ
      (rightContext D Sc cutoff [i] _ _
        (affineUnit D Sc cutoff _ _ (crossLast D Sc s.word i i)) ≫
        affineUnit D Sc cutoff _ _ (crossLast D Sc (s.word ++ [i]) i i) ≫
        rightContext D Sc cutoff [i] _ _
          (affineUnit D Sc cutoff _ _ (crossLast D Sc s.word i i))) =
    (ideal D Sc cutoff (s.word ++ [i] ++ [i] ++ [i])
      (s.word ++ [i] ++ [i] ++ [i])).mkQ
      (affineUnit D Sc cutoff _ _ (crossLast D Sc (s.word ++ [i]) i i) ≫
        rightContext D Sc cutoff [i] _ _
          (affineUnit D Sc cutoff _ _ (crossLast D Sc s.word i i)) ≫
        affineUnit D Sc cutoff _ _ (crossLast D Sc (s.word ++ [i]) i i))
  rw [rightContext_affineUnit]
  change (ideal D Sc cutoff _ _).mkQ (affineUnit D Sc cutoff _ _
      (crossLast D Sc s.word i i ▷ (pres D Sc).obj (ob D [i])) ≫
        affineUnit D Sc cutoff _ _ (crossLast D Sc (s.word ++ [i]) i i) ≫
          affineUnit D Sc cutoff _ _
            (crossLast D Sc s.word i i ▷ (pres D Sc).obj (ob D [i]))) =
    (ideal D Sc cutoff _ _).mkQ
      (affineUnit D Sc cutoff _ _ (crossLast D Sc (s.word ++ [i]) i i) ≫
        affineUnit D Sc cutoff _ _
          (crossLast D Sc s.word i i ▷ (pres D Sc).obj (ob D [i])) ≫
          affineUnit D Sc cutoff _ _ (crossLast D Sc (s.word ++ [i]) i i))
  rw [← affineUnit_comp, ← affineUnit_comp, ← affineUnit_comp, ← affineUnit_comp]
  exact congrArg (fun f =>
    (ideal D Sc cutoff (s.word ++ [i] ++ [i] ++ [i])
      (s.word ++ [i] ++ [i] ++ [i])).mkQ
      (affineUnit D Sc cutoff _ _ f)) (affineEqual_braid D Sc s.word i)

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
