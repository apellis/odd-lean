import OddMath.QuiverHecke.CyclotomicAction.ELVEvenOffDiagonalLeading
import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalSourceSplitting
import OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryInputDefect
import OddMath.QuiverHecke.CyclotomicAction.ELVCyclotomicCrossCoordinates

/-! # Even input contraction and dot on the cyclotomic source

The parity-zero input operators in DeformedMatrixComparison, section 3.
The ordinary moving dot preserves the long-extraction kernel. Consequently
the specified input defect and decoded dot descend through the prescribed
Pprime relations to Source, retaining every old coefficient.
The actual coefficient(0) module/counit attachment is separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem evenInputDefect_pMap_alpha (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    (v t : List I) (a : CyclotomicCrossingTensor.PprimeDomain D Sc cutoff i v t) :
    appendC0InputDefect D Sc cutoff i v t
      (pMap D Sc cutoff i v (t ++ [i])
        (CyclotomicCrossingTensor.alpha D Sc cutoff i v t a)) = 0 := by
  have h0 : appendC0 D Sc cutoff i v t
      (pMap D Sc cutoff i v (t ++ [i])
        (CyclotomicCrossingTensor.alpha D Sc cutoff i v t a)) = 0 := by
    rw [appendC0_pMap_offDiagonal D Sc cutoff p i v t,
      CyclotomicCrossingTensor.offDiagonalLongExtraction_alpha, map_zero]
  have h1 : appendC0 D Sc cutoff i v t
      (appendMovingPowerTarget D Sc cutoff i v (t ++ [i]) 1
        (pMap D Sc cutoff i v (t ++ [i])
          (CyclotomicCrossingTensor.alpha D Sc cutoff i v t a))) = 0 := by
    rw [← pMap_movingEvenDot D Sc cutoff i hi,
      appendC0_pMap_offDiagonal D Sc cutoff p i v t,
      offDiagonalLongExtraction_evenMoving D Sc cutoff p i hi,
      CyclotomicCrossingTensor.offDiagonalLongExtraction_alpha, map_zero, map_zero]
  simp only [appendC0InputDefect, LinearMap.sub_apply, LinearMap.comp_apply,
    h0, h1, map_zero, sub_self]

theorem evenInputDefect_shortCross_pprime (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    (v t : List I) (a : CyclotomicCrossingTensor.PprimeDomain D Sc cutoff i v t) :
    appendC0InputDefect D Sc cutoff i v t
      (CyclotomicCrossingTensor.shortCross D Sc cutoff i v t
        (CyclotomicCrossingTensor.pprime D Sc cutoff i v t a)) = 0 := by
  have hs := LinearMap.congr_fun (CyclotomicCrossingTensor.shortColumn_square D Sc cutoff i v t) a
  simp only [LinearMap.comp_apply] at hs
  rw [← hs]
  exact evenInputDefect_pMap_alpha D Sc cutoff p i hi v t a

namespace CyclotomicCrossingTensor

/-- The prescribed polynomial-constant defect on affine short coordinates. -/
def evenInputContractionAffine (i : I) (v t : List I) :
    ShortTarget D Sc cutoff i v t →ₗ[k] Old D Sc cutoff v t where
  toFun z := appendC0InputDefect D Sc cutoff i v t (shortCross D Sc cutoff i v t z) 0
  map_add' a b := by simp only [map_add, Finsupp.add_apply]
  map_smul' a b := by simp only [map_smul, Finsupp.smul_apply, RingHom.id_apply]

theorem evenInputContractionAffine_ker_q (i : I) (hi : D.parity i = 0) (v t : List I) :
    LinearMap.ker (q D Sc cutoff i v t) ≤
      LinearMap.ker (evenInputContractionAffine D Sc cutoff i v t) := by
  rw [← range_pprime_eq_ker_q]
  rintro z ⟨a, rfl⟩
  change appendC0InputDefect D Sc cutoff i v t
    (shortCross D Sc cutoff i v t (pprime D Sc cutoff i v t a)) 0 = 0
  rw [evenInputDefect_shortCross_pprime D Sc cutoff 0 i hi v t, Finsupp.zero_apply]

/-- The raw even cap row on the original source; its representative is minus composition. -/
def evenInputContraction (i : I) (hi : D.parity i = 0) (v t : List I) :
    Source D Sc cutoff i v t →ₗ[k] Old D Sc cutoff v t :=
  ((LinearMap.ker (q D Sc cutoff i v t)).liftQ
    (evenInputContractionAffine D Sc cutoff i v t)
    (evenInputContractionAffine_ker_q D Sc cutoff i hi v t)).comp
      ((q D Sc cutoff i v t).quotKerEquivOfSurjective
        (q_surjective D Sc cutoff i v t)).symm.toLinearMap

@[simp] theorem evenInputContraction_q (i : I) (hi : D.parity i = 0) (v t : List I)
    (z : ShortTarget D Sc cutoff i v t) :
    evenInputContraction D Sc cutoff i hi v t (q D Sc cutoff i v t z) =
      evenInputContractionAffine D Sc cutoff i v t z := by
  simp only [evenInputContraction, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]

/-- The input dot is the decoded ordinary append moving dot. -/
def evenCrossingInputDotAffine (i : I) (v t : List I) :
    ShortTarget D Sc cutoff i v t →ₗ[k] ShortTarget D Sc cutoff i v t :=
  ShortCrossCoordinates.decode D Sc cutoff i v t ∘ₗ
    appendMovingPowerTarget D Sc cutoff i v (t ++ [i]) 1 ∘ₗ
      shortCross D Sc cutoff i v t

theorem evenCrossingInputDotAffine_pprime (i : I) (hi : D.parity i = 0) (v t : List I)
    (a : PprimeDomain D Sc cutoff i v t) :
    evenCrossingInputDotAffine D Sc cutoff i v t (pprime D Sc cutoff i v t a) ∈
      LinearMap.range (pprime D Sc cutoff i v t) := by
  have hz : movingPowerTarget D Sc cutoff i v (t ++ [i]) 1 (by simp [hi])
      (alpha D Sc cutoff i v t a) ∈ LinearMap.range (alpha D Sc cutoff i v t) := by
    rw [← ker_offDiagonalLongExtraction_eq_range_alpha D Sc cutoff 0 i v t,
      LinearMap.mem_ker, offDiagonalLongExtraction_evenMoving D Sc cutoff 0 i hi,
      offDiagonalLongExtraction_alpha, map_zero]
  obtain ⟨a', ha'⟩ := hz
  refine ⟨a', ?_⟩
  change pprime D Sc cutoff i v t a' =
    ShortCrossCoordinates.decode D Sc cutoff i v t
      (appendMovingPowerTarget D Sc cutoff i v (t ++ [i]) 1
        (shortCross D Sc cutoff i v t (pprime D Sc cutoff i v t a)))
  have hs := LinearMap.congr_fun (shortColumn_square D Sc cutoff i v t) a
  have hs' := LinearMap.congr_fun (shortColumn_square D Sc cutoff i v t) a'
  simp only [LinearMap.comp_apply] at hs hs'
  rw [← hs, ← pMap_movingEvenDot D Sc cutoff i hi, ← ha', hs',
    ShortCrossCoordinates.decode_shortCross]

theorem evenCrossingInputDotAffine_ker_q (i : I) (hi : D.parity i = 0) (v t : List I) :
    LinearMap.ker (q D Sc cutoff i v t) ≤
      (LinearMap.ker (q D Sc cutoff i v t)).comap
        (evenCrossingInputDotAffine D Sc cutoff i v t) := by
  intro z hz
  rw [← range_pprime_eq_ker_q] at hz
  obtain ⟨a, rfl⟩ := hz
  change evenCrossingInputDotAffine D Sc cutoff i v t (pprime D Sc cutoff i v t a) ∈
    LinearMap.ker (q D Sc cutoff i v t)
  rw [← range_pprime_eq_ker_q]
  exact evenCrossingInputDotAffine_pprime D Sc cutoff i hi v t a

def evenCrossingInputDot (i : I) (hi : D.parity i = 0) (v t : List I) :
    Source D Sc cutoff i v t →ₗ[k] Source D Sc cutoff i v t :=
  let e := (q D Sc cutoff i v t).quotKerEquivOfSurjective (q_surjective D Sc cutoff i v t)
  e.toLinearMap ∘ₗ
    (LinearMap.ker (q D Sc cutoff i v t)).mapQ
      (LinearMap.ker (q D Sc cutoff i v t)) (evenCrossingInputDotAffine D Sc cutoff i v t)
      (evenCrossingInputDotAffine_ker_q D Sc cutoff i hi v t) ∘ₗ e.symm.toLinearMap

@[simp] theorem evenCrossingInputDot_q (i : I) (hi : D.parity i = 0) (v t : List I)
    (z : ShortTarget D Sc cutoff i v t) :
    evenCrossingInputDot D Sc cutoff i hi v t (q D Sc cutoff i v t z) =
      q D Sc cutoff i v t (evenCrossingInputDotAffine D Sc cutoff i v t z) := by
  simp only [evenCrossingInputDot, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.mapQ_apply,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

theorem evenCrossingInputDotAffine_representative (i : I) (hi : D.parity i = 0)
    (v s t : List I) (r : hom D Sc cutoff v (s ++ [i]))
    (g : hom D Sc cutoff (s ++ [i]) t) :
    evenCrossingInputDotAffine D Sc cutoff i v t
      (shortTensor D Sc cutoff i v s t g ((ideal D Sc cutoff v (s ++ [i])).mkQ r)) =
      shortTensor D Sc cutoff i v s t
        (appendMovingPower D Sc cutoff i s 1 ≫ g) ((ideal D Sc cutoff v (s ++ [i])).mkQ r) := by
  change ShortCrossCoordinates.decode D Sc cutoff i v t
    (appendMovingPowerTarget D Sc cutoff i v (t ++ [i]) 1
      (shortCross D Sc cutoff i v t
        (shortTensor D Sc cutoff i v s t g ((ideal D Sc cutoff _ _).mkQ r)))) = _
  rw [ShortCrossCoordinates.column_mk, appendMovingPowerTarget_crossing_one]
  simp only [map_sub, map_smul, ShortCrossCoordinates.decode_embedding, smul_zero, sub_zero]
  rw [← ShortCrossCoordinates.column_mk, ShortCrossCoordinates.decode_shortCross]
  simp only [hi, zero_mul, SKM.zsign_zero, one_smul, twist_zero]

theorem evenCrossingInputDot_iterate_q (i : I) (hi : D.parity i = 0) (v t : List I)
    (r : ℕ) (z : ShortTarget D Sc cutoff i v t) :
    (evenCrossingInputDot D Sc cutoff i hi v t)^[r] (q D Sc cutoff i v t z) =
      q D Sc cutoff i v t ((evenCrossingInputDotAffine D Sc cutoff i v t)^[r] z) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih, evenCrossingInputDot_q, Function.iterate_succ_apply']

theorem evenInputContraction_iterate_q (i : I) (hi : D.parity i = 0) (v t : List I)
    (r : ℕ) (z : ShortTarget D Sc cutoff i v t) :
    evenInputContraction D Sc cutoff i hi v t
      ((evenCrossingInputDot D Sc cutoff i hi v t)^[r] (q D Sc cutoff i v t z)) =
      evenInputContractionAffine D Sc cutoff i v t ((evenCrossingInputDotAffine D Sc cutoff i v t)^[r] z) := by
  rw [evenCrossingInputDot_iterate_q, evenInputContraction_q]

end CyclotomicCrossingTensor
end OddMath.QuiverHecke.ELVOld
