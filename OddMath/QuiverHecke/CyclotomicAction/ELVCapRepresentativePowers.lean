import OddMath.QuiverHecke.CyclotomicAction.ELVCrossingInputDot

/-! # Powers of the specified input-dot kernel operator

The input dot acts on an actual balanced representative by the prescribed
self-crossing sign, one old dot and total parity on the old coefficient.
Iteration below retains these operations separately. Applying the actual
descended contraction evaluates every power without a freeness or action
hypothesis. This is the representative input to DeformedMatrixComparison
(5); identifying categorical dotted counits still requires their map comparison.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open CategoryTheory StringDiagrams Supercategory
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Iterating the actual input operator keeps every coefficient twist. -/
theorem crossingInputDotAffine_iterate_representative
    (j : {j : I // D.parity j = 1}) (v s : List I) (n : ℕ)
    (b : hom D Sc cutoff v (s ++ [j.1])) (g : hom D Sc cutoff (s ++ [j.1]) v) :
    (crossingInputDotAffine D Sc cutoff j v)^[n]
      (shortTensor D Sc cutoff j.1 v s v g ((ideal D Sc cutoff v (s ++ [j.1])).mkQ b)) =
      (SKM.zsign k (D.parity j.1 * D.parity j.1)) ^ n •
        shortTensor D Sc cutoff j.1 v s v
          ((fun h : hom D Sc cutoff (s ++ [j.1]) v =>
            appendMovingPower D Sc cutoff j.1 s 1 ≫ h)^[n] g)
          ((ideal D Sc cutoff v (s ++ [j.1])).mkQ
            ((fun c : hom D Sc cutoff v (s ++ [j.1]) => twist k (D.parity j.1) c)^[n] b)) := by
  induction n with
  | zero => simp only [Function.iterate_zero, id_eq, pow_zero, one_smul]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, map_smul,
      crossingInputDotAffine_representative, smul_smul,
      Function.iterate_succ_apply', Function.iterate_succ_apply', pow_succ]

theorem inputContractionAffine_representative
    (j : {j : I // D.parity j = 1}) (v s : List I)
    (b : hom D Sc cutoff v (s ++ [j.1])) (g : hom D Sc cutoff (s ++ [j.1]) v) :
    inputContractionAffine D Sc cutoff j v
      (shortTensor D Sc cutoff j.1 v s v g ((ideal D Sc cutoff v (s ++ [j.1])).mkQ b)) =
      -(SKM.zsign k (D.parity j.1 * D.parity j.1)) •
        (ideal D Sc cutoff v v).mkQ (twist k (D.parity j.1) b ≫ g) := by
  simpa only [inputContraction_q] using inputContraction_representative D Sc cutoff j v s b g

/-- Every concrete dotted row is evaluated on an actual representative.
The scalar, total coefficient twist and ordered dot precomposition are explicit. -/
theorem inputContractionAffine_iterate_representative
    (j : {j : I // D.parity j = 1}) (v s : List I) (n : ℕ)
    (b : hom D Sc cutoff v (s ++ [j.1])) (g : hom D Sc cutoff (s ++ [j.1]) v) :
    inputContractionAffine D Sc cutoff j v
      ((crossingInputDotAffine D Sc cutoff j v)^[n]
        (shortTensor D Sc cutoff j.1 v s v g ((ideal D Sc cutoff v (s ++ [j.1])).mkQ b))) =
      (SKM.zsign k (D.parity j.1 * D.parity j.1)) ^ n •
        (-(SKM.zsign k (D.parity j.1 * D.parity j.1)) •
          (ideal D Sc cutoff v v).mkQ
            (twist k (D.parity j.1)
              ((fun c : hom D Sc cutoff v (s ++ [j.1]) => twist k (D.parity j.1) c)^[n] b) ≫
              (fun h : hom D Sc cutoff (s ++ [j.1]) v =>
                appendMovingPower D Sc cutoff j.1 s 1 ≫ h)^[n] g)) := by
  rw [crossingInputDotAffine_iterate_representative, map_smul,
    inputContractionAffine_representative]

/-- The same actual dotted row formula applies after cyclotomic descent. -/
theorem inputContraction_iterate_representative
    (j : {j : I // D.parity j = 1}) (v s : List I) (n : ℕ)
    (b : hom D Sc cutoff v (s ++ [j.1])) (g : hom D Sc cutoff (s ++ [j.1]) v) :
    inputContraction D Sc cutoff j v
      ((crossingInputDot D Sc cutoff j v)^[n]
        (q D Sc cutoff j.1 v v
          (shortTensor D Sc cutoff j.1 v s v g ((ideal D Sc cutoff v (s ++ [j.1])).mkQ b)))) =
      (SKM.zsign k (D.parity j.1 * D.parity j.1)) ^ n •
        (-(SKM.zsign k (D.parity j.1 * D.parity j.1)) •
          (ideal D Sc cutoff v v).mkQ
            (twist k (D.parity j.1)
              ((fun c : hom D Sc cutoff v (s ++ [j.1]) => twist k (D.parity j.1) c)^[n] b) ≫
              (fun h : hom D Sc cutoff (s ++ [j.1]) v =>
                appendMovingPower D Sc cutoff j.1 s 1 ≫ h)^[n] g)) := by
  rw [inputContraction_iterate_q]
  exact inputContractionAffine_iterate_representative D Sc cutoff j v s n b g

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
