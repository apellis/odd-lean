import OddMath.QuiverHecke.CyclotomicAction.ELVCapInputRecurrence
import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalSourceSplitting
import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalBoundary
import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalRhoExtraction

/-! # Input contraction and moving dot on arbitrary old Hom coefficients

The input-oriented maps of DeformedMatrixComparison, section 3, are the
prescribed append defect and moving operator. They descend through the
Pprime relations. Corrected-rho preservation of the long-extraction kernel
proves descent. These are concrete input-oriented operators on Source;
their categorical counit/dot comparison is a separate obligation.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld
open CategoryTheory StringDiagrams Supercategory
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem offDiagonalInputDefect_pMap_alpha (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I)
    (a : CyclotomicCrossingTensor.PprimeDomain D Sc cutoff j.1 v t) :
    appendC0InputDefect D Sc cutoff j.1 v t
      (pMap D Sc cutoff j.1 v (t ++ [j.1])
        (CyclotomicCrossingTensor.alpha D Sc cutoff j.1 v t a)) = 0 := by
  have h0 : appendC0 D Sc cutoff j.1 v t
      (pMap D Sc cutoff j.1 v (t ++ [j.1])
        (CyclotomicCrossingTensor.alpha D Sc cutoff j.1 v t a)) = 0 := by
    rw [appendC0_pMap_offDiagonal D Sc cutoff p j.1 v t,
      CyclotomicCrossingTensor.offDiagonalLongExtraction_alpha, map_zero]
  have h1 : appendC0 D Sc cutoff j.1 v t
      (appendMovingPowerTarget D Sc cutoff j.1 v (t ++ [j.1]) 1
        (pMap D Sc cutoff j.1 v (t ++ [j.1])
          (CyclotomicCrossingTensor.alpha D Sc cutoff j.1 v t a))) = 0 := by
    rw [← pMap_boundaryRho, appendC0_pMap_offDiagonal D Sc cutoff p j.1 v t,
      offDiagonalLongExtraction_boundaryRho,
      CyclotomicCrossingTensor.offDiagonalLongExtraction_alpha, map_zero, map_zero]
  simp only [appendC0InputDefect, LinearMap.sub_apply, LinearMap.comp_apply,
    h0, h1, map_zero, sub_self]

/-- Vanishing on the independently prescribed Pprime relation, before quotient. -/
theorem offDiagonalInputDefect_shortCross_pprime (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I)
    (a : CyclotomicCrossingTensor.PprimeDomain D Sc cutoff j.1 v t) :
    appendC0InputDefect D Sc cutoff j.1 v t
      (CyclotomicCrossingTensor.shortCross D Sc cutoff j.1 v t
        (CyclotomicCrossingTensor.pprime D Sc cutoff j.1 v t a)) = 0 := by
  have hs := LinearMap.congr_fun
    (CyclotomicCrossingTensor.shortColumn_square D Sc cutoff j.1 v t) a
  simp only [LinearMap.comp_apply] at hs
  rw [← hs]
  exact offDiagonalInputDefect_pMap_alpha D Sc cutoff p j v t a

namespace CyclotomicCrossingTensor

/-- The actual polynomial-constant contraction before the cyclotomic quotient. -/
def offDiagonalInputContractionAffine (j : {j : I // D.parity j = 1}) (v t : List I) :
    ShortTarget D Sc cutoff j.1 v t →ₗ[k] Old D Sc cutoff v t where
  toFun z := appendC0InputDefect D Sc cutoff j.1 v t
    (shortCross D Sc cutoff j.1 v t z) 0
  map_add' a b := by simp only [map_add, Finsupp.add_apply]
  map_smul' a b := by simp only [map_smul, Finsupp.smul_apply, RingHom.id_apply]

theorem offDiagonalInputContractionAffine_ker_q (j : {j : I // D.parity j = 1}) (v t : List I) :
    LinearMap.ker (q D Sc cutoff j.1 v t) ≤
      LinearMap.ker (offDiagonalInputContractionAffine D Sc cutoff j v t) := by
  rw [← range_pprime_eq_ker_q]
  rintro z ⟨a, rfl⟩
  change appendC0InputDefect D Sc cutoff j.1 v t
    (shortCross D Sc cutoff j.1 v t (pprime D Sc cutoff j.1 v t a)) 0 = 0
  rw [offDiagonalInputDefect_shortCross_pprime D Sc cutoff 0 j v t, Finsupp.zero_apply]

/-- Descent of this specified contraction to the original cyclotomic source.
No cap comparison or arbitrary replacement row is supplied as a hypothesis. -/
def offDiagonalInputContraction (j : {j : I // D.parity j = 1}) (v t : List I) :
    Source D Sc cutoff j.1 v t →ₗ[k] Old D Sc cutoff v t :=
  ((LinearMap.ker (q D Sc cutoff j.1 v t)).liftQ
    (offDiagonalInputContractionAffine D Sc cutoff j v t)
    (offDiagonalInputContractionAffine_ker_q D Sc cutoff j v t)).comp
      ((q D Sc cutoff j.1 v t).quotKerEquivOfSurjective
        (q_surjective D Sc cutoff j.1 v t)).symm.toLinearMap

@[simp] theorem offDiagonalInputContraction_q (j : {j : I // D.parity j = 1}) (v t : List I)
    (z : ShortTarget D Sc cutoff j.1 v t) :
    offDiagonalInputContraction D Sc cutoff j v t (q D Sc cutoff j.1 v t z) =
      offDiagonalInputContractionAffine D Sc cutoff j v t z := by
  simp only [offDiagonalInputContraction, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]

def offDiagonalCrossingInputDotAffine (j : {j : I // D.parity j = 1}) (v t : List I) :
    ShortTarget D Sc cutoff j.1 v t →ₗ[k] ShortTarget D Sc cutoff j.1 v t :=
  ShortCrossCoordinates.decode D Sc cutoff j.1 v t ∘ₗ
    appendMovingPowerTarget D Sc cutoff j.1 v (t ++ [j.1]) 1 ∘ₗ
      shortCross D Sc cutoff j.1 v t

/-- The moving input dot sends every Pprime relation to another Pprime relation. -/
theorem offDiagonalCrossingInputDotAffine_pprime (j : {j : I // D.parity j = 1}) (v t : List I)
    (a : PprimeDomain D Sc cutoff j.1 v t) :
    offDiagonalCrossingInputDotAffine D Sc cutoff j v t (pprime D Sc cutoff j.1 v t a) ∈
      LinearMap.range (pprime D Sc cutoff j.1 v t) := by
  have hz : boundaryRho D Sc cutoff j v (t ++ [j.1]) (alpha D Sc cutoff j.1 v t a) ∈
      LinearMap.range (alpha D Sc cutoff j.1 v t) := by
    rw [← ker_offDiagonalLongExtraction_eq_range_alpha D Sc cutoff 0 j.1 v t,
      LinearMap.mem_ker, offDiagonalLongExtraction_boundaryRho,
      offDiagonalLongExtraction_alpha, map_zero]
  obtain ⟨a', ha'⟩ := hz
  refine ⟨a', ?_⟩
  change pprime D Sc cutoff j.1 v t a' =
    ShortCrossCoordinates.decode D Sc cutoff j.1 v t
      (appendMovingPowerTarget D Sc cutoff j.1 v (t ++ [j.1]) 1
        (shortCross D Sc cutoff j.1 v t (pprime D Sc cutoff j.1 v t a)))
  have hs := LinearMap.congr_fun (shortColumn_square D Sc cutoff j.1 v t) a
  have hs' := LinearMap.congr_fun (shortColumn_square D Sc cutoff j.1 v t) a'
  simp only [LinearMap.comp_apply] at hs hs'
  rw [← hs, ← pMap_boundaryRho, ← ha', hs', ShortCrossCoordinates.decode_shortCross]

theorem offDiagonalCrossingInputDotAffine_ker_q (j : {j : I // D.parity j = 1}) (v t : List I) :
    LinearMap.ker (q D Sc cutoff j.1 v t) ≤
      (LinearMap.ker (q D Sc cutoff j.1 v t)).comap
        (offDiagonalCrossingInputDotAffine D Sc cutoff j v t) := by
  intro z hz
  rw [← range_pprime_eq_ker_q] at hz
  obtain ⟨a, rfl⟩ := hz
  change offDiagonalCrossingInputDotAffine D Sc cutoff j v t (pprime D Sc cutoff j.1 v t a) ∈
    LinearMap.ker (q D Sc cutoff j.1 v t)
  rw [← range_pprime_eq_ker_q]
  exact offDiagonalCrossingInputDotAffine_pprime D Sc cutoff j v t a

/-- Concrete transport of the moving input dot to the original cyclotomic source. -/
def offDiagonalCrossingInputDot (j : {j : I // D.parity j = 1}) (v t : List I) :
    Source D Sc cutoff j.1 v t →ₗ[k] Source D Sc cutoff j.1 v t :=
  let e := (q D Sc cutoff j.1 v t).quotKerEquivOfSurjective (q_surjective D Sc cutoff j.1 v t)
  e.toLinearMap ∘ₗ
    (LinearMap.ker (q D Sc cutoff j.1 v t)).mapQ
      (LinearMap.ker (q D Sc cutoff j.1 v t)) (offDiagonalCrossingInputDotAffine D Sc cutoff j v t)
      (offDiagonalCrossingInputDotAffine_ker_q D Sc cutoff j v t) ∘ₗ e.symm.toLinearMap

@[simp] theorem offDiagonalCrossingInputDot_q (j : {j : I // D.parity j = 1}) (v t : List I)
    (z : ShortTarget D Sc cutoff j.1 v t) :
    offDiagonalCrossingInputDot D Sc cutoff j v t (q D Sc cutoff j.1 v t z) =
      q D Sc cutoff j.1 v t (offDiagonalCrossingInputDotAffine D Sc cutoff j v t z) := by
  simp only [offDiagonalCrossingInputDot, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.mapQ_apply,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- Signed source-dot formula on full-coefficient representatives. -/
theorem offDiagonalCrossingInputDotAffine_representative (j : {j : I // D.parity j = 1})
    (v s t : List I) (r : hom D Sc cutoff v (s ++ [j.1]))
    (g : hom D Sc cutoff (s ++ [j.1]) t) :
    offDiagonalCrossingInputDotAffine D Sc cutoff j v t
      (shortTensor D Sc cutoff j.1 v s t g ((ideal D Sc cutoff v (s ++ [j.1])).mkQ r)) =
      SKM.zsign k (D.parity j.1 * D.parity j.1) •
        shortTensor D Sc cutoff j.1 v s t
          (appendMovingPower D Sc cutoff j.1 s 1 ≫ g)
          ((ideal D Sc cutoff v (s ++ [j.1])).mkQ (twist k (D.parity j.1) r)) := by
  change ShortCrossCoordinates.decode D Sc cutoff j.1 v t
    (appendMovingPowerTarget D Sc cutoff j.1 v (t ++ [j.1]) 1
      (shortCross D Sc cutoff j.1 v t
        (shortTensor D Sc cutoff j.1 v s t g ((ideal D Sc cutoff _ _).mkQ r)))) = _
  rw [ShortCrossCoordinates.column_mk, appendMovingPowerTarget_crossing_one]
  simp only [map_sub, map_smul, ShortCrossCoordinates.decode_embedding, smul_zero, sub_zero]
  rw [← ShortCrossCoordinates.column_mk, ShortCrossCoordinates.decode_shortCross]

theorem offDiagonalCrossingInputDot_iterate_q (j : {j : I // D.parity j = 1}) (v t : List I)
    (r : ℕ) (z : ShortTarget D Sc cutoff j.1 v t) :
    (offDiagonalCrossingInputDot D Sc cutoff j v t)^[r] (q D Sc cutoff j.1 v t z) =
      q D Sc cutoff j.1 v t ((offDiagonalCrossingInputDotAffine D Sc cutoff j v t)^[r] z) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih, offDiagonalCrossingInputDot_q, Function.iterate_succ_apply']

theorem offDiagonalInputContraction_iterate_q (j : {j : I // D.parity j = 1}) (v t : List I)
    (r : ℕ) (z : ShortTarget D Sc cutoff j.1 v t) :
    offDiagonalInputContraction D Sc cutoff j v t
      ((offDiagonalCrossingInputDot D Sc cutoff j v t)^[r] (q D Sc cutoff j.1 v t z)) =
      offDiagonalInputContractionAffine D Sc cutoff j v t ((offDiagonalCrossingInputDotAffine D Sc cutoff j v t)^[r] z) := by
  rw [offDiagonalCrossingInputDot_iterate_q, offDiagonalInputContraction_q]

end CyclotomicCrossingTensor
end OddMath.QuiverHecke.ELVOld

