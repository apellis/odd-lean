import OddMath.QuiverHecke.CyclotomicAction.ELVKernelMatrixCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVKernelOffContentMatrices

/-! # Coefficient-kernel matrix bijectivity
The target-fixed coefficient-kernel transfer of DeformedMatrixComparison section 4.
Comparisons use literal list endpoints before passing to boxed old objects.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private def oddPositiveCoordinates (j : {j : I // D.parity j = 1})
    (v t : List I) (m : ℕ)
    (hm : endpointQPDegree D cutoff j.1 v = outputSDegree D j.1 v + m) :
    (BalancedKernelTensor.piKernel (positiveKernelFamily D Sc cutoff j.1 m ⟨t⟩)).obj
      (op (⟨v⟩ : OldCategory D Sc cutoff)) ≃ₗ[k]
        Old D Sc cutoff (v ++ [j.1]) (t ++ [j.1]) :=
  (positiveKernelCoordinates D Sc cutoff j.1 m (op ⟨v⟩) ⟨t⟩).trans
    ((unitFamilyPlainCoordinates D Sc cutoff j.1 v t m).symm.trans
      (unitFamilyComponentEquiv D Sc cutoff 0 j v t m hm))

private theorem oddPositiveCoordinates_apply (j : {j : I // D.parity j = 1})
    (v t : List I) (m : ℕ)
    (hm : endpointQPDegree D cutoff j.1 v = outputSDegree D j.1 v + m)
    (z : (BalancedKernelTensor.piKernel (positiveKernelFamily D Sc cutoff j.1 m ⟨t⟩)).obj
      (op (⟨v⟩ : OldCategory D Sc cutoff))) :
    (oddPositiveCoordinates D Sc cutoff j v t m hm).toFun z =
      (positiveKernelMap D Sc cutoff j.1 m ⟨t⟩).app (op ⟨v⟩) z := by
  classical
  rw [positiveKernelMap_apply]
  change unitFamilyComponentEquiv D Sc cutoff 0 j v t m hm
    ((unitFamilyPlainCoordinates D Sc cutoff j.1 v t m).symm
      (positiveKernelCoordinates D Sc cutoff j.1 m (op ⟨v⟩) ⟨t⟩ z)) = _
  rw [unitFamilyComponentEquiv_eq]
  simp only [LinearEquiv.apply_symm_apply]
  rw [mateKernelComponent_row]
  apply congrArg₂ (fun x y => x + y)
  · apply congrArg (matrixMateRow D Sc cutoff j.1 v t)
    rfl
  · apply Finset.sum_congr rfl
    intro r _
    rfl

private def oddNegativeCoordinates (j : {j : I // D.parity j = 1})
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m) :
    (IndResKernel.kernel (k := k) (append D Sc cutoff j.1) ⟨t⟩).obj
      (op (⟨v⟩ : OldCategory D Sc cutoff)) ≃ₗ[k]
    (BalancedKernelTensor.piKernel (negativeKernelFamily D Sc cutoff j.1 m ⟨t⟩)).obj
      (op (⟨v⟩ : OldCategory D Sc cutoff)) :=
  (kernelSourceCoordinates D Sc cutoff j.1 (op ⟨v⟩) ⟨t⟩).trans
    ((capFamilyComponentEquiv D Sc cutoff 0 j v t m hm).trans
      ((capFamilyComponentCoordinates D Sc cutoff j.1 v t m).trans
        (negativeKernelCoordinates D Sc cutoff j.1 m (op ⟨v⟩) ⟨t⟩).symm))

private theorem oddNegativeCoordinates_apply (j : {j : I // D.parity j = 1})
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m)
    (z : (IndResKernel.kernel (k := k) (append D Sc cutoff j.1) ⟨t⟩).obj
      (op (⟨v⟩ : OldCategory D Sc cutoff))) :
    (oddNegativeCoordinates D Sc cutoff j v t m hm).toFun z =
      (negativeKernelMap D Sc cutoff j.1 m ⟨t⟩).app (op ⟨v⟩) z := by
  apply (negativeKernelCoordinates D Sc cutoff j.1 m (op ⟨v⟩) ⟨t⟩).injective
  change capFamilyComponentCoordinates D Sc cutoff j.1 v t m
      (capFamilyComponentEquiv D Sc cutoff 0 j v t m hm
        (kernelSourceCoordinates D Sc cutoff j.1 (op ⟨v⟩) ⟨t⟩ z)) = _
  rw [capFamilyComponentEquiv_eq]
  apply Prod.ext
  · rw [negativeKernelCoordinates_fst, negativeKernelMap_none,
      mateKernelComponent_row]
    apply congrArg (matrixMateRow D Sc cutoff j.1 v t)
    rfl
  · funext r
    rw [negativeKernelCoordinates_snd, negativeKernelMap_some,
      capKernelComponent_moduleCapRow]
    apply congrArg ((moduleCapRow D Sc cutoff j.1
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) r.val).total
        (⟨t⟩ : OldCategory D Sc cutoff))
    rfl

private def evenPositiveCoordinates (j : {j : I // D.parity j = 0})
    (v t : List I) (m : ℕ)
    (hm : endpointQPDegree D cutoff j.1 v = outputSDegree D j.1 v + m) :
    (BalancedKernelTensor.piKernel (positiveKernelFamily D Sc cutoff j.1 m ⟨t⟩)).obj
      (op (⟨v⟩ : OldCategory D Sc cutoff)) ≃ₗ[k]
        Old D Sc cutoff (v ++ [j.1]) (t ++ [j.1]) :=
  (positiveKernelCoordinates D Sc cutoff j.1 m (op ⟨v⟩) ⟨t⟩).trans
    ((unitFamilyPlainCoordinates D Sc cutoff j.1 v t m).symm.trans
      (evenUnitFamilyComponentEquiv D Sc cutoff 0 j v t m hm))

private theorem evenPositiveCoordinates_apply (j : {j : I // D.parity j = 0})
    (v t : List I) (m : ℕ)
    (hm : endpointQPDegree D cutoff j.1 v = outputSDegree D j.1 v + m)
    (z : (BalancedKernelTensor.piKernel (positiveKernelFamily D Sc cutoff j.1 m ⟨t⟩)).obj
      (op (⟨v⟩ : OldCategory D Sc cutoff))) :
    (evenPositiveCoordinates D Sc cutoff j v t m hm).toFun z =
      (positiveKernelMap D Sc cutoff j.1 m ⟨t⟩).app (op ⟨v⟩) z := by
  classical
  rw [positiveKernelMap_apply]
  change evenUnitFamilyComponentEquiv D Sc cutoff 0 j v t m hm
    ((unitFamilyPlainCoordinates D Sc cutoff j.1 v t m).symm
      (positiveKernelCoordinates D Sc cutoff j.1 m (op ⟨v⟩) ⟨t⟩ z)) = _
  rw [evenUnitFamilyComponentEquiv_eq]
  simp only [LinearEquiv.apply_symm_apply]
  rw [mateKernelComponent_row]
  apply congrArg₂ (fun x y => x + y)
  · apply congrArg (matrixMateRow D Sc cutoff j.1 v t)
    rfl
  · apply Finset.sum_congr rfl
    intro r _
    rfl

private def evenNegativeCoordinates (j : {j : I // D.parity j = 0})
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m) :
    (IndResKernel.kernel (k := k) (append D Sc cutoff j.1) ⟨t⟩).obj
      (op (⟨v⟩ : OldCategory D Sc cutoff)) ≃ₗ[k]
    (BalancedKernelTensor.piKernel (negativeKernelFamily D Sc cutoff j.1 m ⟨t⟩)).obj
      (op (⟨v⟩ : OldCategory D Sc cutoff)) :=
  (kernelSourceCoordinates D Sc cutoff j.1 (op ⟨v⟩) ⟨t⟩).trans
    ((evenCapFamilyComponentEquiv D Sc cutoff 0 j v t m hm).trans
      ((capFamilyComponentCoordinates D Sc cutoff j.1 v t m).trans
        (negativeKernelCoordinates D Sc cutoff j.1 m (op ⟨v⟩) ⟨t⟩).symm))

private theorem evenNegativeCoordinates_apply (j : {j : I // D.parity j = 0})
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m)
    (z : (IndResKernel.kernel (k := k) (append D Sc cutoff j.1) ⟨t⟩).obj
      (op (⟨v⟩ : OldCategory D Sc cutoff))) :
    (evenNegativeCoordinates D Sc cutoff j v t m hm).toFun z =
      (negativeKernelMap D Sc cutoff j.1 m ⟨t⟩).app (op ⟨v⟩) z := by
  apply (negativeKernelCoordinates D Sc cutoff j.1 m (op ⟨v⟩) ⟨t⟩).injective
  change capFamilyComponentCoordinates D Sc cutoff j.1 v t m
      (evenCapFamilyComponentEquiv D Sc cutoff 0 j v t m hm
        (kernelSourceCoordinates D Sc cutoff j.1 (op ⟨v⟩) ⟨t⟩ z)) = _
  rw [evenCapFamilyComponentEquiv_eq]
  apply Prod.ext
  · rw [negativeKernelCoordinates_fst, negativeKernelMap_none,
      mateKernelComponent_row]
    apply congrArg (matrixMateRow D Sc cutoff j.1 v t)
    rfl
  · funext r
    rw [negativeKernelCoordinates_snd, negativeKernelMap_some,
      capKernelComponent_moduleCapRow]
    apply congrArg ((moduleCapRow D Sc cutoff j.1
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) r.val).total
        (⟨t⟩ : OldCategory D Sc cutoff))
    rfl

theorem PositiveKernelMap_bijective_of_height
    (j : {j : I // D.parity j = 1}) (v t : OldCategory D Sc cutoff) (m : ℕ)
    (hm : endpointQPDegree D cutoff j.1 v.word = outputSDegree D j.1 v.word + m) :
    Function.Bijective ((positiveKernelMap D Sc cutoff j.1 m t).app (op v)) := by
  rcases v with ⟨v⟩
  rcases t with ⟨t⟩
  have heq : (oddPositiveCoordinates D Sc cutoff j v t m hm).toFun =
      (positiveKernelMap D Sc cutoff j.1 m ⟨t⟩).app (op ⟨v⟩) :=
    funext (oddPositiveCoordinates_apply D Sc cutoff j v t m hm)
  rw [← heq]
  exact (oddPositiveCoordinates D Sc cutoff j v t m hm).bijective

theorem NegativeKernelMap_bijective_of_height
    (j : {j : I // D.parity j = 1}) (v t : OldCategory D Sc cutoff) (m : ℕ)
    (hm : outputSDegree D j.1 v.word = endpointQPDegree D cutoff j.1 v.word + m) :
    Function.Bijective ((negativeKernelMap D Sc cutoff j.1 m t).app (op v)) := by
  rcases v with ⟨v⟩
  rcases t with ⟨t⟩
  have heq : (oddNegativeCoordinates D Sc cutoff j v t m hm).toFun =
      (negativeKernelMap D Sc cutoff j.1 m ⟨t⟩).app (op ⟨v⟩) :=
    funext (oddNegativeCoordinates_apply D Sc cutoff j v t m hm)
  rw [← heq]
  exact (oddNegativeCoordinates D Sc cutoff j v t m hm).bijective

theorem evenPositiveKernelMap_bijective_of_height
    (j : {j : I // D.parity j = 0}) (v t : OldCategory D Sc cutoff) (m : ℕ)
    (hm : endpointQPDegree D cutoff j.1 v.word = outputSDegree D j.1 v.word + m) :
    Function.Bijective ((positiveKernelMap D Sc cutoff j.1 m t).app (op v)) := by
  rcases v with ⟨v⟩
  rcases t with ⟨t⟩
  have heq : (evenPositiveCoordinates D Sc cutoff j v t m hm).toFun =
      (positiveKernelMap D Sc cutoff j.1 m ⟨t⟩).app (op ⟨v⟩) :=
    funext (evenPositiveCoordinates_apply D Sc cutoff j v t m hm)
  rw [← heq]
  exact (evenPositiveCoordinates D Sc cutoff j v t m hm).bijective

theorem evenNegativeKernelMap_bijective_of_height
    (j : {j : I // D.parity j = 0}) (v t : OldCategory D Sc cutoff) (m : ℕ)
    (hm : outputSDegree D j.1 v.word = endpointQPDegree D cutoff j.1 v.word + m) :
    Function.Bijective ((negativeKernelMap D Sc cutoff j.1 m t).app (op v)) := by
  rcases v with ⟨v⟩
  rcases t with ⟨t⟩
  have heq : (evenNegativeCoordinates D Sc cutoff j v t m hm).toFun =
      (negativeKernelMap D Sc cutoff j.1 m ⟨t⟩).app (op ⟨v⟩) :=
    funext (evenNegativeCoordinates_apply D Sc cutoff j v t m hm)
  rw [← heq]
  exact (evenNegativeCoordinates D Sc cutoff j v t m hm).bijective

private theorem colourParityCases (P : I → Prop)
    (he : ∀ j : {j : I // D.parity j = 0}, P j.1)
    (ho : ∀ j : {j : I // D.parity j = 1}, P j.1) (i : I) : P i := by
  rcases parity_eq_zero_or_one (D.parity i) with hi | hi
  · exact he ⟨i, hi⟩
  · exact ho ⟨i, hi⟩

private theorem positiveKernelMap_bijective_of_height (i : I)
    (v t : OldCategory D Sc cutoff) (m : ℕ) (hm : endpointQPDegree D cutoff i v.word = outputSDegree D i v.word + m) :
    Function.Bijective ((positiveKernelMap D Sc cutoff i m t).app (op v)) :=
  colourParityCases D (fun i => ∀ (v t : OldCategory D Sc cutoff) (m : ℕ),
    endpointQPDegree D cutoff i v.word = outputSDegree D i v.word + m →
      Function.Bijective ((positiveKernelMap D Sc cutoff i m t).app (op v)))
    (evenPositiveKernelMap_bijective_of_height D Sc cutoff)
    (PositiveKernelMap_bijective_of_height D Sc cutoff) i v t m hm

private theorem negativeKernelMap_bijective_of_height (i : I)
    (v t : OldCategory D Sc cutoff) (m : ℕ) (hm : outputSDegree D i v.word = endpointQPDegree D cutoff i v.word + m) :
    Function.Bijective ((negativeKernelMap D Sc cutoff i m t).app (op v)) :=
  colourParityCases D (fun i => ∀ (v t : OldCategory D Sc cutoff) (m : ℕ),
    outputSDegree D i v.word = endpointQPDegree D cutoff i v.word + m →
      Function.Bijective ((negativeKernelMap D Sc cutoff i m t).app (op v)))
    (evenNegativeKernelMap_bijective_of_height D Sc cutoff)
    (NegativeKernelMap_bijective_of_height D Sc cutoff) i v t m hm

/-- The prescribed coefficient matrix is bijective at every source, with one count fixed by target content. -/
theorem positiveKernelMap_bijective (i : I) (t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I)) (v : OldCategory D Sc cutoff) :
    Function.Bijective ((positiveKernelMap D Sc cutoff i
      (contentUnitCount D cutoff i (t.word : Multiset I)) t).app (op v)) := by
  by_cases hc : (v.word : Multiset I) = (t.word : Multiset I)
  · let vc : OldContentCategory D Sc cutoff t.word := ⟨v, Multiset.coe_eq_coe.mp hc⟩
    have hm := oldContent_unitCount_height D Sc cutoff i t.word hh vc
    change endpointQPDegree D cutoff i v.word = outputSDegree D i v.word +
      contentUnitCount D cutoff i (t.word : Multiset I) at hm
    exact positiveKernelMap_bijective_of_height D Sc cutoff i v t
      (contentUnitCount D cutoff i (t.word : Multiset I)) hm
  · exact positiveKernelMap_bijective_of_content_ne D Sc cutoff i _ v t hc

/-- The prescribed coefficient matrix is bijective at every source, with one count fixed by target content. -/
theorem negativeKernelMap_bijective (i : I) (t : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0) (v : OldCategory D Sc cutoff) :
    Function.Bijective ((negativeKernelMap D Sc cutoff i
      (contentCapCount D cutoff i (t.word : Multiset I)) t).app (op v)) := by
  by_cases hc : (v.word : Multiset I) = (t.word : Multiset I)
  · let vc : OldContentCategory D Sc cutoff t.word := ⟨v, Multiset.coe_eq_coe.mp hc⟩
    have hm := oldContent_capCount_height D Sc cutoff i t.word hh vc
    exact negativeKernelMap_bijective_of_height D Sc cutoff i v t
      (contentCapCount D cutoff i (t.word : Multiset I)) hm
  · exact negativeKernelMap_bijective_of_content_ne D Sc cutoff i _ v t hc

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
