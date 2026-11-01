import OddMath.QuiverHecke.CyclotomicAction.ELVKernelMatrixCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVKernelOffContentMatrices

/-! # Concrete coefficient-kernel inverses at the target content count -/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem mate_row (i : I) (v t : OldCategory D Sc cutoff)
    (z : (IndResKernel.kernel (k := k) (append D Sc cutoff i) t).obj (op v)) :
    actualMateKernelComponent D Sc cutoff i v t z =
      matrixMateRow D Sc cutoff i v.word t.word
        (kernelSourceCoordinates D Sc cutoff i (op v) t z) := by
  have h := actualMateKernelLinear_row D Sc cutoff i (op v) t z
  rw [actualMateKernelLinear_eq_component] at h
  exact h

/-- The actual positive coefficient map is conjugate to the checked finite matrix. -/
def PositiveKernelEquiv (j : {j : I // D.parity j = 1})
    (v t : OldCategory D Sc cutoff) (m : ℕ)
    (hm : endpointQPDegree D cutoff j.1 v.word = outputSDegree D j.1 v.word + m) :
    (BalancedKernelTensor.piKernel (positiveKernelFamily D Sc cutoff j.1 m t)).obj (op v) ≃ₗ[k]
      Old D Sc cutoff (v.word ++ [j.1]) (t.word ++ [j.1]) :=
  (positiveKernelCoordinates D Sc cutoff j.1 m (op v) t).trans
    ((unitFamilyPlainCoordinates D Sc cutoff j.1 v.word t.word m).symm.trans
      (unitFamilyComponentEquiv D Sc cutoff 0 j v.word t.word m hm))

theorem PositiveKernelEquiv_apply (j : {j : I // D.parity j = 1})
    (v t : OldCategory D Sc cutoff) (m : ℕ)
    (hm : endpointQPDegree D cutoff j.1 v.word = outputSDegree D j.1 v.word + m)
    (z : (BalancedKernelTensor.piKernel (positiveKernelFamily D Sc cutoff j.1 m t)).obj (op v)) :
    PositiveKernelEquiv D Sc cutoff j v t m hm z =
      (actualPositiveKernelMap D Sc cutoff j.1 m t).app (op v) z := by
  classical
  rw [actualPositiveKernelMap_apply]
  unfold PositiveKernelEquiv
  simp only [LinearEquiv.trans_apply, unitFamilyComponentEquiv_actual,
    LinearEquiv.apply_symm_apply, positiveKernelCoordinates_fst, positiveKernelCoordinates_snd]
  rw [mate_row]
  rfl

/-- The actual negative coefficient map is conjugate to the checked finite matrix. -/
def NegativeKernelEquiv (j : {j : I // D.parity j = 1})
    (v t : OldCategory D Sc cutoff) (m : ℕ)
    (hm : outputSDegree D j.1 v.word = endpointQPDegree D cutoff j.1 v.word + m) :
    (IndResKernel.kernel (k := k) (append D Sc cutoff j.1) t).obj (op v) ≃ₗ[k]
      (BalancedKernelTensor.piKernel (negativeKernelFamily D Sc cutoff j.1 m t)).obj (op v) :=
  (kernelSourceCoordinates D Sc cutoff j.1 (op v) t).trans
    ((capFamilyComponentEquiv D Sc cutoff 0 j v.word t.word m hm).trans
      ((capFamilyComponentCoordinates D Sc cutoff j.1 v.word t.word m).trans
        (negativeKernelCoordinates D Sc cutoff j.1 m (op v) t).symm))

theorem NegativeKernelEquiv_apply (j : {j : I // D.parity j = 1})
    (v t : OldCategory D Sc cutoff) (m : ℕ)
    (hm : outputSDegree D j.1 v.word = endpointQPDegree D cutoff j.1 v.word + m)
    (z : (IndResKernel.kernel (k := k) (append D Sc cutoff j.1) t).obj (op v)) :
    NegativeKernelEquiv D Sc cutoff j v t m hm z =
      (actualNegativeKernelMap D Sc cutoff j.1 m t).app (op v) z := by
  apply (negativeKernelCoordinates D Sc cutoff j.1 m (op v) t).injective
  unfold NegativeKernelEquiv
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    capFamilyComponentEquiv_actual]
  apply Prod.ext
  · rw [negativeKernelCoordinates_fst, actualNegativeKernelMap_none, mate_row]
  · funext r
    rw [negativeKernelCoordinates_snd, actualNegativeKernelMap_some,
      actualCapKernelComponent_moduleCapRow]
    rfl

/-- The actual positive coefficient map is conjugate to the checked finite matrix. -/
def evenPositiveKernelEquiv (i : {i : I // D.parity i = 0})
    (v t : OldCategory D Sc cutoff) (m : ℕ)
    (hm : endpointQPDegree D cutoff i.1 v.word = outputSDegree D i.1 v.word + m) :
    (BalancedKernelTensor.piKernel (positiveKernelFamily D Sc cutoff i.1 m t)).obj (op v) ≃ₗ[k]
      Old D Sc cutoff (v.word ++ [i.1]) (t.word ++ [i.1]) :=
  (positiveKernelCoordinates D Sc cutoff i.1 m (op v) t).trans
    ((unitFamilyPlainCoordinates D Sc cutoff i.1 v.word t.word m).symm.trans
      (evenUnitFamilyComponentEquiv D Sc cutoff 0 i v.word t.word m hm))

theorem evenPositiveKernelEquiv_apply (i : {i : I // D.parity i = 0})
    (v t : OldCategory D Sc cutoff) (m : ℕ)
    (hm : endpointQPDegree D cutoff i.1 v.word = outputSDegree D i.1 v.word + m)
    (z : (BalancedKernelTensor.piKernel (positiveKernelFamily D Sc cutoff i.1 m t)).obj (op v)) :
    evenPositiveKernelEquiv D Sc cutoff i v t m hm z =
      (actualPositiveKernelMap D Sc cutoff i.1 m t).app (op v) z := by
  classical
  rw [actualPositiveKernelMap_apply]
  unfold evenPositiveKernelEquiv
  simp only [LinearEquiv.trans_apply, evenUnitFamilyComponentEquiv_actual,
    LinearEquiv.apply_symm_apply, positiveKernelCoordinates_fst, positiveKernelCoordinates_snd]
  rw [mate_row]
  rfl

/-- The actual negative coefficient map is conjugate to the checked finite matrix. -/
def evenNegativeKernelEquiv (i : {i : I // D.parity i = 0})
    (v t : OldCategory D Sc cutoff) (m : ℕ)
    (hm : outputSDegree D i.1 v.word = endpointQPDegree D cutoff i.1 v.word + m) :
    (IndResKernel.kernel (k := k) (append D Sc cutoff i.1) t).obj (op v) ≃ₗ[k]
      (BalancedKernelTensor.piKernel (negativeKernelFamily D Sc cutoff i.1 m t)).obj (op v) :=
  (kernelSourceCoordinates D Sc cutoff i.1 (op v) t).trans
    ((evenCapFamilyComponentEquiv D Sc cutoff 0 i v.word t.word m hm).trans
      ((capFamilyComponentCoordinates D Sc cutoff i.1 v.word t.word m).trans
        (negativeKernelCoordinates D Sc cutoff i.1 m (op v) t).symm))

theorem evenNegativeKernelEquiv_apply (i : {i : I // D.parity i = 0})
    (v t : OldCategory D Sc cutoff) (m : ℕ)
    (hm : outputSDegree D i.1 v.word = endpointQPDegree D cutoff i.1 v.word + m)
    (z : (IndResKernel.kernel (k := k) (append D Sc cutoff i.1) t).obj (op v)) :
    evenNegativeKernelEquiv D Sc cutoff i v t m hm z =
      (actualNegativeKernelMap D Sc cutoff i.1 m t).app (op v) z := by
  apply (negativeKernelCoordinates D Sc cutoff i.1 m (op v) t).injective
  unfold evenNegativeKernelEquiv
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    evenCapFamilyComponentEquiv_actual]
  apply Prod.ext
  · rw [negativeKernelCoordinates_fst, actualNegativeKernelMap_none, mate_row]
  · funext r
    rw [negativeKernelCoordinates_snd, actualNegativeKernelMap_some,
      actualCapKernelComponent_moduleCapRow]
    rfl

theorem PositiveKernelMap_bijective_of_height
    (j : {j : I // D.parity j = 1}) (v t : OldCategory D Sc cutoff) (m : ℕ)
    (hm : endpointQPDegree D cutoff j.1 v.word = outputSDegree D j.1 v.word + m) :
    Function.Bijective ((actualPositiveKernelMap D Sc cutoff j.1 m t).app (op v)) := by
  have h := (PositiveKernelEquiv D Sc cutoff j v t m hm).bijective
  simpa only [PositiveKernelEquiv_apply] using h

theorem NegativeKernelMap_bijective_of_height
    (j : {j : I // D.parity j = 1}) (v t : OldCategory D Sc cutoff) (m : ℕ)
    (hm : outputSDegree D j.1 v.word = endpointQPDegree D cutoff j.1 v.word + m) :
    Function.Bijective ((actualNegativeKernelMap D Sc cutoff j.1 m t).app (op v)) := by
  have h := (NegativeKernelEquiv D Sc cutoff j v t m hm).bijective
  simpa only [NegativeKernelEquiv_apply] using h

theorem evenPositiveKernelMap_bijective_of_height
    (j : {j : I // D.parity j = 0}) (v t : OldCategory D Sc cutoff) (m : ℕ)
    (hm : endpointQPDegree D cutoff j.1 v.word = outputSDegree D j.1 v.word + m) :
    Function.Bijective ((actualPositiveKernelMap D Sc cutoff j.1 m t).app (op v)) := by
  have h := (evenPositiveKernelEquiv D Sc cutoff j v t m hm).bijective
  simpa only [evenPositiveKernelEquiv_apply] using h

theorem evenNegativeKernelMap_bijective_of_height
    (j : {j : I // D.parity j = 0}) (v t : OldCategory D Sc cutoff) (m : ℕ)
    (hm : outputSDegree D j.1 v.word = endpointQPDegree D cutoff j.1 v.word + m) :
    Function.Bijective ((actualNegativeKernelMap D Sc cutoff j.1 m t).app (op v)) := by
  have h := (evenNegativeKernelEquiv D Sc cutoff j v t m hm).bijective
  simpa only [evenNegativeKernelEquiv_apply] using h

/-- The prescribed coefficient matrix is bijective at every source, with one count fixed by target content. -/
theorem actualPositiveKernelMap_bijective (i : I) (t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I)) (v : OldCategory D Sc cutoff) :
    Function.Bijective ((actualPositiveKernelMap D Sc cutoff i
      (contentUnitCount D cutoff i (t.word : Multiset I)) t).app (op v)) := by
  by_cases hc : (v.word : Multiset I) = (t.word : Multiset I)
  · let vc : OldContentCategory D Sc cutoff t.word := ⟨v, Multiset.coe_eq_coe.mp hc⟩
    have hm := oldContent_unitCount_height D Sc cutoff i t.word hh vc
    rcases parity_eq_zero_or_one (D.parity i) with hi | hi
    · exact evenPositiveKernelMap_bijective_of_height D Sc cutoff ⟨i, hi⟩ v t _ hm
    · exact PositiveKernelMap_bijective_of_height D Sc cutoff ⟨i, hi⟩ v t _ hm
  · exact actualPositiveKernelMap_bijective_of_content_ne D Sc cutoff i _ v t hc

/-- The prescribed coefficient matrix is bijective at every source, with one count fixed by target content. -/
theorem actualNegativeKernelMap_bijective (i : I) (t : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0) (v : OldCategory D Sc cutoff) :
    Function.Bijective ((actualNegativeKernelMap D Sc cutoff i
      (contentCapCount D cutoff i (t.word : Multiset I)) t).app (op v)) := by
  by_cases hc : (v.word : Multiset I) = (t.word : Multiset I)
  · let vc : OldContentCategory D Sc cutoff t.word := ⟨v, Multiset.coe_eq_coe.mp hc⟩
    have hm := oldContent_capCount_height D Sc cutoff i t.word hh vc
    rcases parity_eq_zero_or_one (D.parity i) with hi | hi
    · exact evenNegativeKernelMap_bijective_of_height D Sc cutoff ⟨i, hi⟩ v t _ hm
    · exact NegativeKernelMap_bijective_of_height D Sc cutoff ⟨i, hi⟩ v t _ hm
  · exact actualNegativeKernelMap_bijective_of_content_ne D Sc cutoff i _ v t hc

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
