import OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryInputDefect
import OddMath.QuiverHecke.CyclotomicAction.ELVSourcePolynomialQuotient
import OddMath.QuiverHecke.CyclotomicAction.ELVCyclotomicCrossCoordinates

/-! # Parity transport and representative correction for the cap coordinate

The input-oriented contraction in `DeformedMatrixComparison.md` §3 is
transported by total output parity, including exterior coefficients. The
actual defect on the corrected source section is also compared with the
uncorrected rho-compatible section. Corrected-rho preservation proves that
the zeroth contraction kills Pprime and hence descends to the original
cyclotomic source. Identification with the categorical counit and higher
dotted rows remains separate.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld
open CategoryTheory StringDiagrams Supercategory
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Total output parity cancels the twist on the first old factor and
transfers it to the second, without commuting either coefficient. -/
theorem oldTwist_inputDefect_crossing (i : I) (v s t : List I)
    (r : hom D Sc cutoff v (s ++ [i])) (g : hom D Sc cutoff (s ++ [i]) t) :
    oldTwist D Sc cutoff (D.parity i) v t
      (appendC0InputDefect D Sc cutoff i v t
        (appendCrossingClass D Sc cutoff i v s t r g) 0) =
      -(SKM.zsign k (D.parity i * D.parity i)) •
        (ideal D Sc cutoff v t).mkQ (r ≫ twist k (D.parity i) g) := by
  rw [appendC0InputDefect_crossing]
  simp only [Finsupp.smul_apply, Finsupp.single_eq_same, map_smul]
  congr 1
  change (ideal D Sc cutoff v t).mkQ
    (twist k (D.parity i) (twist k (D.parity i) r ≫ g)) = _
  rw [twist_comp, twist_twist]

/-- The zeroth contraction kills the actual source correction: corrected rho
preserves the short source and the prescribed P intertwines it. -/
theorem inputDefect_pMap_alpha (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I)
    (a : CyclotomicCrossingTensor.PprimeDomain D Sc cutoff j.1 v v) :
    appendC0InputDefect D Sc cutoff j.1 v v
      (pMap D Sc cutoff j.1 v (v ++ [j.1])
        (CyclotomicCrossingTensor.alpha D Sc cutoff j.1 v v a)) = 0 := by
  have h0 := CyclotomicCrossingTensor.appendC0_pMap_alpha D Sc cutoff p j v a
  have h1 : appendC0 D Sc cutoff j.1 v v
      (appendMovingPowerTarget D Sc cutoff j.1 v (v ++ [j.1]) 1
        (pMap D Sc cutoff j.1 v (v ++ [j.1])
          (CyclotomicCrossingTensor.alpha D Sc cutoff j.1 v v a))) = 0 := by
    rw [← pMap_boundaryRho, appendC0_pMap D Sc cutoff p j v,
      outputLongExtraction_boundaryRho,
      CyclotomicCrossingTensor.outputLongExtraction_alpha, map_zero, map_zero]
  simp only [appendC0InputDefect, LinearMap.sub_apply, LinearMap.comp_apply,
    h0, h1, map_zero, sub_self]

/-- Vanishing on the independently prescribed Pprime relation, before quotient. -/
theorem inputDefect_shortCross_pprime (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I)
    (a : CyclotomicCrossingTensor.PprimeDomain D Sc cutoff j.1 v v) :
    appendC0InputDefect D Sc cutoff j.1 v v
      (CyclotomicCrossingTensor.shortCross D Sc cutoff j.1 v v
        (CyclotomicCrossingTensor.pprime D Sc cutoff j.1 v v a)) = 0 := by
  have hs := LinearMap.congr_fun
    (CyclotomicCrossingTensor.shortColumn_square D Sc cutoff j.1 v v) a
  simp only [LinearMap.comp_apply] at hs
  rw [← hs]
  exact inputDefect_pMap_alpha D Sc cutoff p j v a

/-- The actual polynomial-constant defect changes by the prescribed Pprime
column when the source section is corrected. Row descent must kill this
specific correction before cap evaluation can be independent of the lift. -/
theorem inputDefect_pMap_sourceLongSection (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I)
    (f : ℕ →₀ Old D Sc cutoff v v) :
    appendC0InputDefect D Sc cutoff j.1 v v
      (pMap D Sc cutoff j.1 v (v ++ [j.1])
        (CyclotomicCrossingTensor.sourceLongSection D Sc cutoff p j.1 v f)) =
      appendC0InputDefect D Sc cutoff j.1 v v (outputLiftBoundary D Sc cutoff p j v f) -
        appendC0InputDefect D Sc cutoff j.1 v v
          (CyclotomicCrossingTensor.shortCross D Sc cutoff j.1 v v
            (CyclotomicCrossingTensor.pprime D Sc cutoff j.1 v v
              (CyclotomicCrossingTensor.extract D Sc cutoff j.1 v v
                (outputLongSection D Sc cutoff p j.1 v f)))) := by
  rw [CyclotomicCrossingTensor.sourceLongSection, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.comp_apply, map_sub, map_sub]
  have hs := LinearMap.congr_fun (CyclotomicCrossingTensor.shortColumn_square D Sc cutoff j.1 v v)
    (CyclotomicCrossingTensor.extract D Sc cutoff j.1 v v (outputLongSection D Sc cutoff p j.1 v f))
  simp only [LinearMap.comp_apply] at hs
  rw [hs]
  rfl

/-- The actual zeroth contraction is independent of the alpha correction. -/
theorem inputDefect_sourceLongSection_eq (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I)
    (f : ℕ →₀ Old D Sc cutoff v v) :
    appendC0InputDefect D Sc cutoff j.1 v v
      (pMap D Sc cutoff j.1 v (v ++ [j.1])
        (CyclotomicCrossingTensor.sourceLongSection D Sc cutoff p j.1 v f)) =
      appendC0InputDefect D Sc cutoff j.1 v v (outputLiftBoundary D Sc cutoff p j v f) := by
  rw [inputDefect_pMap_sourceLongSection,
    inputDefect_shortCross_pprime D Sc cutoff p j v, sub_zero]

namespace CyclotomicCrossingTensor

/-- The actual polynomial-constant contraction before the cyclotomic quotient. -/
def inputContractionAffine (j : {j : I // D.parity j = 1}) (v : List I) :
    ShortTarget D Sc cutoff j.1 v v →ₗ[k] Old D Sc cutoff v v where
  toFun z := appendC0InputDefect D Sc cutoff j.1 v v
    (shortCross D Sc cutoff j.1 v v z) 0
  map_add' a b := by simp only [map_add, Finsupp.add_apply]
  map_smul' a b := by simp only [map_smul, Finsupp.smul_apply, RingHom.id_apply]

theorem inputContractionAffine_ker_q (j : {j : I // D.parity j = 1}) (v : List I) :
    LinearMap.ker (q D Sc cutoff j.1 v v) ≤
      LinearMap.ker (inputContractionAffine D Sc cutoff j v) := by
  rw [← range_pprime_eq_ker_q]
  rintro z ⟨a, rfl⟩
  change appendC0InputDefect D Sc cutoff j.1 v v
    (shortCross D Sc cutoff j.1 v v (pprime D Sc cutoff j.1 v v a)) 0 = 0
  rw [inputDefect_shortCross_pprime D Sc cutoff 0 j v, Finsupp.zero_apply]

/-- Descent of this specified contraction to the original cyclotomic source.
No cap comparison or arbitrary replacement row is supplied as a hypothesis. -/
def inputContraction (j : {j : I // D.parity j = 1}) (v : List I) :
    Source D Sc cutoff j.1 v v →ₗ[k] Old D Sc cutoff v v :=
  ((LinearMap.ker (q D Sc cutoff j.1 v v)).liftQ
    (inputContractionAffine D Sc cutoff j v)
    (inputContractionAffine_ker_q D Sc cutoff j v)).comp
      ((q D Sc cutoff j.1 v v).quotKerEquivOfSurjective
        (q_surjective D Sc cutoff j.1 v v)).symm.toLinearMap

@[simp] theorem inputContraction_q (j : {j : I // D.parity j = 1}) (v : List I)
    (z : ShortTarget D Sc cutoff j.1 v v) :
    inputContraction D Sc cutoff j v (q D Sc cutoff j.1 v v z) =
      inputContractionAffine D Sc cutoff j v z := by
  simp only [inputContraction, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]

/-- The descended row retains the whole old-coefficient twist on representatives. -/
theorem inputContraction_representative (j : {j : I // D.parity j = 1})
    (v s : List I) (r : hom D Sc cutoff v (s ++ [j.1]))
    (g : hom D Sc cutoff (s ++ [j.1]) v) :
    inputContraction D Sc cutoff j v
      (q D Sc cutoff j.1 v v
        (shortTensor D Sc cutoff j.1 v s v g ((ideal D Sc cutoff v (s ++ [j.1])).mkQ r))) =
      -(SKM.zsign k (D.parity j.1 * D.parity j.1)) •
        (ideal D Sc cutoff v v).mkQ (twist k (D.parity j.1) r ≫ g) := by
  rw [inputContraction_q]
  change appendC0InputDefect D Sc cutoff j.1 v v
    (shortCross D Sc cutoff j.1 v v
      (shortTensor D Sc cutoff j.1 v s v g ((ideal D Sc cutoff _ _).mkQ r))) 0 = _
  rw [ShortCrossCoordinates.column_mk, appendC0InputDefect_crossing]
  simp only [Finsupp.smul_apply, Finsupp.single_eq_same]


/-- Canonical source shift and total output parity turn this actual
zeroth contraction into ordinary composition, with all coefficients retained. -/
theorem inputContraction_shifted_representative (j : {j : I // D.parity j = 1})
    (v s : List I) (r : hom D Sc cutoff v (s ++ [j.1]))
    (g : hom D Sc cutoff (s ++ [j.1]) v) :
    oldTwist D Sc cutoff (D.parity j.1) v v
      (inputContraction D Sc cutoff j v
        (q D Sc cutoff j.1 v v
          (shortTensor D Sc cutoff j.1 v s v (twist k (D.parity j.1) g)
            ((ideal D Sc cutoff v (s ++ [j.1])).mkQ r)))) =
      (ideal D Sc cutoff v v).mkQ (r ≫ g) := by
  rw [inputContraction_representative, map_smul]
  have he : oldTwist D Sc cutoff (D.parity j.1) v v
      ((ideal D Sc cutoff v v).mkQ
        (twist k (D.parity j.1) r ≫ twist k (D.parity j.1) g)) =
      (ideal D Sc cutoff v v).mkQ (r ≫ g) := by
    change (ideal D Sc cutoff v v).mkQ
      (twist k (D.parity j.1)
        (twist k (D.parity j.1) r ≫ twist k (D.parity j.1) g)) = _
    rw [← twist_comp, twist_twist]
  rw [he]
  simp [j.property, SKM.zsign]

end CyclotomicCrossingTensor

end OddMath.QuiverHecke.ELVOld
