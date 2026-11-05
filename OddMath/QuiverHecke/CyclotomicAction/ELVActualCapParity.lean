import OddMath.QuiverHecke.CyclotomicAction.ELVActualCapInput

/-! # Parity and dot transport for the actual shifted source

The source comparison is the induced map of the actual restriction parity
isomorphism followed by the prescribed even coefficient comparison.
Its odd parity and the odd shifted counit are established on these fixed
module maps. The actual induction dot anticommutes with this canonical
source comparison; no chosen-J or matrix premise is supplied.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

abbrev unshiftedSourceModule (i : I) (v : List I) :
    Superfunctor k (OldCategory D Sc cutoff) (SVec k) :=
  (BalancedInduction.induction (append D Sc cutoff i)).obj
    ((BalancedInduction.restriction (append D Sc cutoff i)).obj
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))

theorem coefficientModuleBackward_mem (i : I) (v : List I) :
    coefficientModuleBackward D Sc cutoff i v ∈ parity (R := k) _ _ 0 := by
  apply Superfunctor.mem_parity_iff_isHomogeneous.mpr
  intro q hq
  funext s
  rw [coefficientModuleBackward_app, ite_eq_right hq]
  rfl

def parityCoefficientMap (i : I) (v : List I) :
    (BalancedInduction.restriction (append D Sc cutoff i)).obj
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) ⟶
      coefficientOneModule D Sc cutoff i v :=
  (BalancedInduction.restriction (append D Sc cutoff i)).map
      (supermoduleParityIso
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).inv ≫
    coefficientModuleBackward D Sc cutoff i v

theorem parityCoefficientMap_mem (i : I) (v : List I) :
    parityCoefficientMap D Sc cutoff i v ∈ parity (R := k) _ _ 1 := by
  have h := map_mem (BalancedInduction.restriction (append D Sc cutoff i))
    (inv_mem _
      (supermoduleParityIso_hom_mem
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))))
  simpa only [parityCoefficientMap, add_zero] using
    comp_mem h (coefficientModuleBackward_mem D Sc cutoff i v)

theorem shiftedSourceParityIso_hom_eq_induction_map (i : I) (v : List I) :
    (shiftedSourceParityIso D Sc cutoff i v).hom =
      (BalancedInduction.induction (append D Sc cutoff i)).map
        (parityCoefficientMap D Sc cutoff i v) := by
  change (BalancedInduction.induction (append D Sc cutoff i)).map
      ((BalancedInduction.restriction (append D Sc cutoff i)).map
        (supermoduleParityIso
          (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).inv) ≫
    (BalancedInduction.induction (append D Sc cutoff i)).map
      (coefficientModuleBackward D Sc cutoff i v) = _
  rw [← CategoryTheory.Functor.map_comp]
  rfl

theorem shiftedSourceParityIso_hom_mem (i : I) (v : List I) :
    (shiftedSourceParityIso D Sc cutoff i v).hom ∈ parity (R := k) _ _ 1 := by
  rw [shiftedSourceParityIso_hom_eq_induction_map]
  exact map_mem (BalancedInduction.induction (append D Sc cutoff i))
    (parityCoefficientMap_mem D Sc cutoff i v)

theorem odd_total_eq_app_one
    {M N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)} {f : M ⟶ N}
    (hf : f ∈ parity (R := k) M N 1) (t : OldCategory D Sc cutoff) :
    f.total t = f.app 1 t := by
  change f.app 0 t + f.app 1 t = f.app 1 t
  rw [Superfunctor.app_eq_zero_of_mem hf (by decide) t, zero_add]

theorem odd_total_mem
    {M N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)} {f : M ⟶ N}
    (hf : f ∈ parity (R := k) M N 1) (t : OldCategory D Sc cutoff) :
    f.total t ∈ parity (R := k) (M.obj t) (N.obj t) 1 := by
  rw [odd_total_eq_app_one D Sc cutoff hf t]
  exact f.app_mem 1 t

theorem inductionDot_mem (j : {j : I // D.parity j = 1})
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (t : OldCategory D Sc cutoff) :
    inductionDot D Sc cutoff j.1 M t ∈ parity (R := k)
      (((BalancedInduction.induction (append D Sc cutoff j.1)).obj M).obj t)
      (((BalancedInduction.induction (append D Sc cutoff j.1)).obj M).obj t) 1 := by
  change BalancedInduction.transformLinear (oldAppendDot_supernatural D Sc cutoff j.1) M t ∈
    parity (R := k) (BalancedInduction.superspace (append D Sc cutoff j.1) M.toFunctor t)
      (BalancedInduction.superspace (append D Sc cutoff j.1) M.toFunctor t) 1
  have hp := congrArg (fun q : ZMod 2 =>
    parity (R := k) (BalancedInduction.superspace (append D Sc cutoff j.1) M.toFunctor t)
      (BalancedInduction.superspace (append D Sc cutoff j.1) M.toFunctor t) q) j.property
  exact hp ▸ BalancedInduction.transformLinear_mem
    (oldAppendDot_supernatural D Sc cutoff j.1) M t

/-- The outer Koszul sign for the actual odd dot and the canonical odd J. -/
theorem inductionDot_sourceParity (j : {j : I // D.parity j = 1})
    (v t : List I)
    (z : (unshiftedSourceModule D Sc cutoff j.1 v).obj
      (⟨t⟩ : OldCategory D Sc cutoff)) :
    inductionDot D Sc cutoff j.1 (coefficientOneModule D Sc cutoff j.1 v)
      (⟨t⟩ : OldCategory D Sc cutoff)
      ((shiftedSourceParityIso D Sc cutoff j.1 v).hom.total
        (⟨t⟩ : OldCategory D Sc cutoff) z) =
      -(shiftedSourceParityIso D Sc cutoff j.1 v).hom.total
        (⟨t⟩ : OldCategory D Sc cutoff)
        (inductionDot D Sc cutoff j.1
          ((BalancedInduction.restriction (append D Sc cutoff j.1)).obj
            (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))
          (⟨t⟩ : OldCategory D Sc cutoff) z) := by
  let f := parityCoefficientMap D Sc cutoff j.1 v
  have hf := map_mem (BalancedInduction.induction (append D Sc cutoff j.1))
    (parityCoefficientMap_mem D Sc cutoff j.1 v)
  have hj : (shiftedSourceParityIso D Sc cutoff j.1 v).hom.total
      (⟨t⟩ : OldCategory D Sc cutoff) =
      BalancedInduction.mapComponent (append D Sc cutoff j.1) f 1
        (⟨t⟩ : OldCategory D Sc cutoff) := by
    rw [shiftedSourceParityIso_hom_eq_induction_map,
      odd_total_eq_app_one D Sc cutoff hf]
    rfl
  simp only [hj]
  have h := congrArg (fun g => g z)
    (BalancedInduction.transform_mapComponent
      (oldAppendDot_supernatural D Sc cutoff j.1)
      ((BalancedInduction.restriction (append D Sc cutoff j.1)).obj
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))
      f 1 (⟨t⟩ : OldCategory D Sc cutoff))
  have hs : sign k (D.parity j.1 * 1) = -1 := by
    rw [mul_one, j.property, sign_one]
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, hs, neg_one_smul] at h
  change BalancedInduction.transformLinear (oldAppendDot_supernatural D Sc cutoff j.1)
      (coefficientOneModule D Sc cutoff j.1 v) (⟨t⟩ : OldCategory D Sc cutoff)
      (BalancedInduction.mapComponent (append D Sc cutoff j.1) f 1
        (⟨t⟩ : OldCategory D Sc cutoff) z) =
    -BalancedInduction.mapComponent (append D Sc cutoff j.1) f 1
      (⟨t⟩ : OldCategory D Sc cutoff)
      (BalancedInduction.transformLinear (oldAppendDot_supernatural D Sc cutoff j.1)
        ((BalancedInduction.restriction (append D Sc cutoff j.1)).obj
          (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))
        (⟨t⟩ : OldCategory D Sc cutoff) z)
  exact h

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor

