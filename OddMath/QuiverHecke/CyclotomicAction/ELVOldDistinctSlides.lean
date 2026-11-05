import OddMath.QuiverHecke.CyclotomicAction.ELVDistinctModuleMate
import OddMath.QuiverHecke.CyclotomicAction.ELVContentAppendDot
import OddMath.QuiverHecke.CyclotomicAction.AppendMackeyRho

/-! # Distinct-colour slides in the old quotient

Brundan–Ellis (1.8): the literal old dots and positive distinct crossing
satisfy both signed slides before induction. These are the coefficient
inputs for the canonical-content and weight probe relations.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.Distinct
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem dot_affine (i : I) (s : OldCategory D Sc cutoff) :
    oldAppendDotComponent D Sc cutoff i s =
      (ideal D Sc cutoff _ _).mkQ (affineUnit D Sc cutoff _ _
        (dotE D Sc (s.word ++ [i]) s.word.length)) := by
  rw [oldAppendDotComponent_eq, appendMovingPower, pow_one]

private theorem lowerDot_affine (i j : I) (s : OldCategory D Sc cutoff) :
    (append D Sc cutoff j).map (oldAppendDotComponent D Sc cutoff i s) =
      (ideal D Sc cutoff _ _).mkQ (affineUnit D Sc cutoff _ _
        (dotE D Sc (s.word ++ [i] ++ [j]) s.word.length)) := by
  rw [dot_affine]
  change (ideal D Sc cutoff (s.word ++ [i] ++ [j]) (s.word ++ [i] ++ [j])).mkQ
    (rightContext D Sc cutoff [j] (s.word ++ [i]) (s.word ++ [i])
      (affineUnit D Sc cutoff (s.word ++ [i]) (s.word ++ [i])
        (dotE D Sc (s.word ++ [i]) s.word.length))) = _
  rw [rightContext_affineUnit]
  change (ideal D Sc cutoff (s.word ++ [i] ++ [j]) (s.word ++ [i] ++ [j])).mkQ
    (affineUnit D Sc cutoff (s.word ++ [i] ++ [j]) (s.word ++ [i] ++ [j])
      (dotE D Sc (s.word ++ [i]) s.word.length ▷ (pres D Sc).obj (ob D [j]))) = _
  rw [dotE_whiskerRight D Sc (s.word ++ [i]) [j] s.word.length (by simp)]

private theorem upperDot_affine (i j : I) (s : OldCategory D Sc cutoff) :
    oldAppendDotComponent D Sc cutoff i ((append D Sc cutoff j).obj s) =
      (ideal D Sc cutoff _ _).mkQ (affineUnit D Sc cutoff _ _
        (dotE D Sc (s.word ++ [j] ++ [i]) (s.word.length + 1))) := by
  simpa only [append, List.length_append, List.length_singleton] using
    dot_affine D Sc cutoff i ((append D Sc cutoff j).obj s)

/-- The source first dot exits on the second strand, retaining its sign. -/
theorem crossComponent_slide_first {i j : I} (hij : i ≠ j)
    (s : OldCategory D Sc cutoff) :
    (append D Sc cutoff i).map (oldAppendDotComponent D Sc cutoff j s) ≫
        crossComponent D Sc cutoff i j s =
      sign k (D.parity j * D.parity i) •
        (crossComponent D Sc cutoff i j s ≫
          oldAppendDotComponent D Sc cutoff j ((append D Sc cutoff i).obj s)) := by
  rw [lowerDot_affine, upperDot_affine]
  change oldComp D Sc cutoff _ _ _ ((ideal D Sc cutoff _ _).mkQ _)
      ((ideal D Sc cutoff _ _).mkQ _) = sign k (D.parity j * D.parity i) •
    oldComp D Sc cutoff _ _ _ ((ideal D Sc cutoff _ _).mkQ _)
      ((ideal D Sc cutoff _ _).mkQ _)
  rw [oldComp_mk, oldComp_mk, ← map_smul]
  simp only [append, Functor.comp_obj]
  rw [← affineUnit_comp, ← affineUnit_comp,
    dotE_comp_crossLast_ne D Sc s.word hij.symm, map_smul, ← sign_eq_zsign]

/-- The source second dot exits on the first strand with the same sign. -/
theorem crossComponent_slide_last {i j : I} (hij : i ≠ j)
    (s : OldCategory D Sc cutoff) :
    oldAppendDotComponent D Sc cutoff i ((append D Sc cutoff j).obj s) ≫
        crossComponent D Sc cutoff i j s =
      sign k (D.parity j * D.parity i) •
        (crossComponent D Sc cutoff i j s ≫
          (append D Sc cutoff j).map (oldAppendDotComponent D Sc cutoff i s)) := by
  rw [upperDot_affine, lowerDot_affine]
  change oldComp D Sc cutoff _ _ _ ((ideal D Sc cutoff _ _).mkQ _)
      ((ideal D Sc cutoff _ _).mkQ _) = sign k (D.parity j * D.parity i) •
    oldComp D Sc cutoff _ _ _ ((ideal D Sc cutoff _ _).mkQ _)
      ((ideal D Sc cutoff _ _).mkQ _)
  rw [oldComp_mk, oldComp_mk, ← map_smul]
  simp only [append, Functor.comp_obj]
  rw [← affineUnit_comp, ← affineUnit_comp,
    lastDotE_comp_crossLast_ne D Sc s.word hij.symm, map_smul, ← sign_eq_zsign]

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.Distinct
