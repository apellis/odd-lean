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
  ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨Classical.choice inferInstance, Subsingleton.elim _ _⟩⟩

/-- With different contents every finite positive coefficient space vanishes. -/
theorem positiveKernelMap_bijective_of_content_ne (i : I) (m : ℕ)
    (v t : OldCategory D Sc cutoff)
    (h : (v.word : Multiset I) ≠ (t.word : Multiset I)) :
    Function.Bijective ((positiveKernelMap D Sc cutoff i m t).app (op v)) := by
  have hnone : Subsingleton ((positiveKernelFamily D Sc cutoff i m t none).obj (op v)) := by
    change Subsingleton (IndResKernel.Component (k := k) (append D Sc cutoff i) v t)
    exact indResKernel_subsingleton_of_content_ne D Sc cutoff (append D Sc cutoff i) h
  have hsome (r : Fin m) : Subsingleton ((positiveKernelFamily D Sc cutoff i m t (some r)).obj (op v)) := by
    change Subsingleton (v ⟶ t)
    exact oldCategory_hom_subsingleton_of_content_ne D Sc cutoff h
  have ht : Subsingleton ((BalancedKernelTensor.inductionKernel (k := k)
      (append D Sc cutoff i) ((append D Sc cutoff i).obj t)).obj (op v)) := by
    change Subsingleton ((append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t)
    exact append_hom_subsingleton_of_content_ne D Sc cutoff i h
  have hs : Subsingleton ((BalancedKernelTensor.piKernel
      (positiveKernelFamily D Sc cutoff i m t)).obj (op v)) := by
    refine ⟨fun x y => ?_⟩
    funext a
    cases a with
    | none => exact hnone.elim _ _
    | some r => exact (hsome r).elim _ _
  exact @bijective_of_subsingleton _ _ hs ht ⟨0⟩ _

/-- With different contents every finite negative coefficient space vanishes. -/
theorem negativeKernelMap_bijective_of_content_ne (i : I) (m : ℕ)
    (v t : OldCategory D Sc cutoff)
    (h : (v.word : Multiset I) ≠ (t.word : Multiset I)) :
    Function.Bijective ((negativeKernelMap D Sc cutoff i m t).app (op v)) := by
  have hnone : Subsingleton ((negativeKernelFamily D Sc cutoff i m t none).obj (op v)) := by
    change Subsingleton ((append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t)
    exact append_hom_subsingleton_of_content_ne D Sc cutoff i h
  have hsome (r : Fin m) : Subsingleton ((negativeKernelFamily D Sc cutoff i m t (some r)).obj (op v)) := by
    change Subsingleton (v ⟶ t)
    exact oldCategory_hom_subsingleton_of_content_ne D Sc cutoff h
  have hs : Subsingleton ((IndResKernel.kernel (k := k) (append D Sc cutoff i) t).obj (op v)) := by
    change Subsingleton (IndResKernel.Component (k := k) (append D Sc cutoff i) v t)
    exact indResKernel_subsingleton_of_content_ne D Sc cutoff (append D Sc cutoff i) h
  have ht : Subsingleton ((BalancedKernelTensor.piKernel
      (negativeKernelFamily D Sc cutoff i m t)).obj (op v)) := by
    refine ⟨fun x y => ?_⟩
    funext a
    cases a with
    | none => exact hnone.elim _ _
    | some r => exact (hsome r).elim _ _
  exact @bijective_of_subsingleton _ _ hs ht ⟨0⟩ _

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
