/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.HomDimension
import OddMath.QuiverHecke.CyclotomicAction.ELVHomGrading
import OddMath.QuiverHecke.CyclotomicAction.ELVContentModule
import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientTruncation
import OddMath.QuiverHecke.CentreFinite

/-! # Lower degree bounds for cyclotomic kernels

Finite permutations of the boundary content give a uniform lower source
bound without finiteness of the colour set. Homogeneous sandwiches of the
first-position relation then have a cutoff-dependent lower degree.
-/
noncomputable section
open CategoryTheory StringDiagrams GradedSupercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (sy : SKM.Symmetrizer D)
  (Sc : SKM.Scalars D k) (hc : Sc.Homogeneous)

/-- Different contents have zero full coefficient Hom. -/
theorem hom_eq_zero_of_not_perm (cutoff : I → ℕ) {v w : List I}
    (h : ¬ w.Perm v) (f : hom D Sc cutoff v w) : f = 0 := by
  change f = (0 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff ⊗[k]
    ((pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)))
  refine TensorProduct.inductionOn (motive := fun z => z = 0) f
    (fun a g => ?_) (fun a b ha hb => ?_)
  · rw [QuiverHecke.hom_eq_zero_of_not_perm D Sc h g, TensorProduct.tmul_zero]
  · rw [ha, hb, add_zero]

end OddMath.QuiverHecke.ELVOld
