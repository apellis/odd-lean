import OddMath.QuiverHecke.CyclotomicAction.ELVActualKernelMatrices
import OddMath.QuiverHecke.CyclotomicAction.ELVOffContentZero

/-! # Actual finite kernel matrices off their target content -/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem bijective_of_subsingleton {V W : Type u}
    [Subsingleton V] [Subsingleton W] [Nonempty V] (f : V → W) : Function.Bijective f :=
  ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨Classical.choice inferInstance, Subsingleton.elim _ _⟩⟩

/-- With different contents every finite positive coefficient space vanishes. -/
theorem actualPositiveKernelMap_bijective_of_content_ne (i : I) (m : ℕ)
    (v t : OldCategory D Sc cutoff)
    (h : (v.word : Multiset I) ≠ (t.word : Multiset I)) :
    Function.Bijective ((actualPositiveKernelMap D Sc cutoff i m t).app (op v)) := by
  letI := oldCategory_hom_subsingleton_of_content_ne D Sc cutoff h
  letI := indResKernel_subsingleton_of_content_ne D Sc cutoff (append D Sc cutoff i) h
  letI := append_hom_subsingleton_of_content_ne D Sc cutoff i h
  haveI : Subsingleton ((BalancedKernelTensor.piKernel
      (positiveKernelFamily D Sc cutoff i m t)).obj (op v)) := by
    refine ⟨fun x y => ?_⟩
    funext a
    cases a with
    | none => exact Subsingleton.elim _ _
    | some r => exact Subsingleton.elim _ _
  exact bijective_of_subsingleton _

/-- With different contents every finite negative coefficient space vanishes. -/
theorem actualNegativeKernelMap_bijective_of_content_ne (i : I) (m : ℕ)
    (v t : OldCategory D Sc cutoff)
    (h : (v.word : Multiset I) ≠ (t.word : Multiset I)) :
    Function.Bijective ((actualNegativeKernelMap D Sc cutoff i m t).app (op v)) := by
  letI := oldCategory_hom_subsingleton_of_content_ne D Sc cutoff h
  letI := indResKernel_subsingleton_of_content_ne D Sc cutoff (append D Sc cutoff i) h
  letI := append_hom_subsingleton_of_content_ne D Sc cutoff i h
  haveI : Subsingleton ((BalancedKernelTensor.piKernel
      (negativeKernelFamily D Sc cutoff i m t)).obj (op v)) := by
    refine ⟨fun x y => ?_⟩
    funext a
    cases a with
    | none => exact Subsingleton.elim _ _
    | some r => exact Subsingleton.elim _ _
  exact bijective_of_subsingleton _

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
