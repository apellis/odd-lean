import OddMath.QuiverHecke.CyclotomicAction.ELVOldDistinctQuadratic
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridQuadratic

/-! # The literal original-parameter polynomial in the two OLD append dots

DeformedActionAssembly §6 (9): the ordered affine polynomial descends as
exactly the same polynomial in the two independent untruncated OLD dots.
No commutation or action relation is imposed on these dots.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Scalar affine endomorphisms map into the actual old quotient endomorphism algebra. -/
def oldAffineEndAlgHom (s : OldCategory D Sc cutoff) :
    End ((pres D Sc).obj (ob D s.word)) →ₐ[k] End s :=
  AlgHom.ofLinearMap
    ((ideal D Sc cutoff s.word s.word).mkQ.comp (affineUnit D Sc cutoff s.word s.word))
    (by
      change (ideal D Sc cutoff s.word s.word).mkQ (affineUnit D Sc cutoff s.word s.word (𝟙 _)) =
        (ideal D Sc cutoff s.word s.word).mkQ (𝟙 _)
      rw [affineUnit_id])
    (fun f g => by
      change (ideal D Sc cutoff s.word s.word).mkQ (affineUnit D Sc cutoff s.word s.word (g ≫ f)) =
        oldComp D Sc cutoff s.word s.word s.word
          ((ideal D Sc cutoff s.word s.word).mkQ (affineUnit D Sc cutoff s.word s.word g))
          ((ideal D Sc cutoff s.word s.word).mkQ (affineUnit D Sc cutoff s.word s.word f))
      rw [oldComp_mk, ← affineUnit_comp])

/-- Ordered signed source evaluations commute with algebra homomorphisms. -/
theorem elvSignedPairQuadEval_map {R S : Type*} [Ring R] [Algebra k R]
    [Ring S] [Algebra k S] (e : R →ₐ[k] S) (i j : I) (a b : R) :
    e (elvSignedPairQuadEval D Sc i j a b) = elvSignedPairQuadEval D Sc i j (e a) (e b) := by
  unfold elvSignedPairQuadEval
  split_ifs <;> simp only [map_smul, map_one, map_add, map_sum, map_mul, map_pow]

namespace CyclotomicCrossingTensor.Distinct

/-- The independently appended lower dot, whiskered into the two-letter source. -/
def pairFirstDot (i j : I) (s : OldCategory D Sc cutoff) :
    End (((append D Sc cutoff i) ⋙ (append D Sc cutoff j)).obj s) :=
  (append D Sc cutoff j).map (oldAppendDotComponent D Sc cutoff i s)

/-- The independent upper dot in the same source endomorphism algebra. -/
def pairSecondDot (i j : I) (s : OldCategory D Sc cutoff) :
    End (((append D Sc cutoff i) ⋙ (append D Sc cutoff j)).obj s) :=
  oldAppendDotComponent D Sc cutoff j ((append D Sc cutoff i).obj s)

theorem pairFirstDot_affine (i j : I) (s : OldCategory D Sc cutoff) :
    pairFirstDot D Sc cutoff i j s =
      oldAffineEndAlgHom D Sc cutoff (((append D Sc cutoff i) ⋙ (append D Sc cutoff j)).obj s)
        (dotE D Sc (s.word ++ [i] ++ [j]) s.word.length) := by
  rw [pairFirstDot, oldAppendDotComponent_eq, appendMovingPower, pow_one]
  change (ideal D Sc cutoff (s.word ++ [i] ++ [j]) (s.word ++ [i] ++ [j])).mkQ
    (rightContext D Sc cutoff [j] (s.word ++ [i]) (s.word ++ [i])
      (affineUnit D Sc cutoff (s.word ++ [i]) (s.word ++ [i])
        (dotE D Sc (s.word ++ [i]) s.word.length))) = _
  rw [rightContext_affineUnit]
  change (ideal D Sc cutoff (s.word ++ [i] ++ [j]) (s.word ++ [i] ++ [j])).mkQ
    (affineUnit D Sc cutoff (s.word ++ [i] ++ [j]) (s.word ++ [i] ++ [j])
      (dotE D Sc (s.word ++ [i]) s.word.length ▷ (pres D Sc).obj (ob D [j]))) = _
  rw [dotE_whiskerRight D Sc (s.word ++ [i]) [j] s.word.length (by simp)]
  rfl

theorem pairSecondDot_affine (i j : I) (s : OldCategory D Sc cutoff) :
    pairSecondDot D Sc cutoff i j s =
      oldAffineEndAlgHom D Sc cutoff (((append D Sc cutoff i) ⋙ (append D Sc cutoff j)).obj s)
        (dotE D Sc (s.word ++ [i] ++ [j]) (s.word.length + 1)) := by
  rw [pairSecondDot, oldAppendDotComponent_eq, appendMovingPower, pow_one]
  change (ideal D Sc cutoff (s.word ++ [i] ++ [j]) (s.word ++ [i] ++ [j])).mkQ
    (affineUnit D Sc cutoff (s.word ++ [i] ++ [j]) (s.word ++ [i] ++ [j])
      (dotE D Sc (s.word ++ [i] ++ [j]) (s.word ++ [i]).length)) =
    (ideal D Sc cutoff (s.word ++ [i] ++ [j]) (s.word ++ [i] ++ [j])).mkQ
      (affineUnit D Sc cutoff (s.word ++ [i] ++ [j]) (s.word ++ [i] ++ [j])
        (dotE D Sc (s.word ++ [i] ++ [j]) (s.word.length + 1)))
  rw [List.length_append, List.length_singleton]

/-- The source polynomial is literally the polynomial of the two chosen OLD dots. -/
theorem signedQuadraticComponent_pairDots (i j : I)
    (s : OldCategory D (parameterTwist D Sc) cutoff) :
    signedQuadraticComponent D Sc cutoff i j s =
      elvSignedPairQuadEval D Sc
        (R := End (((append D (parameterTwist D Sc) cutoff i) ⋙
          (append D (parameterTwist D Sc) cutoff j)).obj s)) i j
        (pairFirstDot D (parameterTwist D Sc) cutoff i j s)
        (pairSecondDot D (parameterTwist D Sc) cutoff i j s) := by
  rw [pairFirstDot_affine, pairSecondDot_affine, ← elvSignedPairQuadEval_map]
  rfl

end CyclotomicCrossingTensor.Distinct
end OddMath.QuiverHecke.ELVOld
