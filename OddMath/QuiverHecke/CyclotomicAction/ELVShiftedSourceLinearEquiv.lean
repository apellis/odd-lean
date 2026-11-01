import OddMath.QuiverHecke.CyclotomicAction.ELVShiftedCoefficientModule

/-! # The linear equivalence of the canonical actual source isomorphism

The component totals of the fixed shiftedSourceParityIso are inverse linear
maps. Composing with the literal coefficient(1) comparison identifies the
actual induction-restriction carrier with the prescribed balanced Source.
The actual counit square is retained. Higher dot/cap normalization is separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The underlying component equivalence of the fixed actual source isomorphism. -/
def shiftedSourceCanonicalEquiv (j : {j : I // D.parity j = 1}) (v t : List I) :
    ((BalancedInduction.induction (append D Sc cutoff j.1)).obj
      ((BalancedInduction.restriction (append D Sc cutoff j.1)).obj
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))).obj
          (⟨t⟩ : OldCategory D Sc cutoff) ≃ₗ[k]
      Source D Sc cutoff j.1 v t where
  toLinearMap := (coefficientOneSourceEquiv D Sc cutoff j v t).toLinearMap.comp
    ((shiftedSourceParityIso D Sc cutoff j.1 v).hom.total (⟨t⟩ : OldCategory D Sc cutoff))
  invFun z := (shiftedSourceParityIso D Sc cutoff j.1 v).inv.total
    (⟨t⟩ : OldCategory D Sc cutoff) ((coefficientOneSourceEquiv D Sc cutoff j v t).symm z)
  left_inv x := by
    change (shiftedSourceParityIso D Sc cutoff j.1 v).inv.total
      (⟨t⟩ : OldCategory D Sc cutoff)
      ((coefficientOneSourceEquiv D Sc cutoff j v t).symm
        (coefficientOneSourceEquiv D Sc cutoff j v t
          ((shiftedSourceParityIso D Sc cutoff j.1 v).hom.total
            (⟨t⟩ : OldCategory D Sc cutoff) x))) = x
    rw [LinearEquiv.symm_apply_apply]
    have h := congrArg (fun f => SuperNatTrans.total f (⟨t⟩ : OldCategory D Sc cutoff))
      (shiftedSourceParityIso D Sc cutoff j.1 v).hom_inv_id
    rw [Superfunctor.comp_total] at h
    have hx := LinearMap.congr_fun h x
    simpa only [SuperNatTrans.total, Superfunctor.id_app_zero,
      Superfunctor.id_app_one, add_zero, LinearMap.id_apply] using hx
  right_inv z := by
    change coefficientOneSourceEquiv D Sc cutoff j v t
      ((shiftedSourceParityIso D Sc cutoff j.1 v).hom.total
        (⟨t⟩ : OldCategory D Sc cutoff)
        ((shiftedSourceParityIso D Sc cutoff j.1 v).inv.total
          (⟨t⟩ : OldCategory D Sc cutoff)
          ((coefficientOneSourceEquiv D Sc cutoff j v t).symm z))) = z
    apply (coefficientOneSourceEquiv D Sc cutoff j v t).symm.injective
    rw [LinearEquiv.symm_apply_apply]
    have h := congrArg (fun f => SuperNatTrans.total f (⟨t⟩ : OldCategory D Sc cutoff))
      (shiftedSourceParityIso D Sc cutoff j.1 v).inv_hom_id
    rw [Superfunctor.comp_total] at h
    have hz := LinearMap.congr_fun h ((coefficientOneSourceEquiv D Sc cutoff j v t).symm z)
    simpa only [SuperNatTrans.total, Superfunctor.id_app_zero,
      Superfunctor.id_app_one, add_zero, LinearMap.id_apply] using hz

@[simp] theorem shiftedSourceCanonicalEquiv_apply (j : {j : I // D.parity j = 1})
    (v t : List I)
    (x : ((BalancedInduction.induction (append D Sc cutoff j.1)).obj
      ((BalancedInduction.restriction (append D Sc cutoff j.1)).obj
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))).obj
          (⟨t⟩ : OldCategory D Sc cutoff)) :
    shiftedSourceCanonicalEquiv D Sc cutoff j v t x =
      coefficientOneSourceEquiv D Sc cutoff j v t
        ((shiftedSourceParityIso D Sc cutoff j.1 v).hom.total
          (⟨t⟩ : OldCategory D Sc cutoff) x) := rfl

/-- The canonical component equivalence retains the actual adjunction counit square. -/
theorem shiftedSourceCanonicalEquiv_counit (j : {j : I // D.parity j = 1})
    (v t : List I)
    (x : ((BalancedInduction.induction (append D Sc cutoff j.1)).obj
      ((BalancedInduction.restriction (append D Sc cutoff j.1)).obj
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))).obj
          (⟨t⟩ : OldCategory D Sc cutoff)) :
    (shiftedSourceCounit D Sc cutoff j.1 v).total (⟨t⟩ : OldCategory D Sc cutoff)
      ((coefficientOneSourceEquiv D Sc cutoff j v t).symm
        (shiftedSourceCanonicalEquiv D Sc cutoff j v t x)) =
      ((BalancedInduction.adjunctionCounit (append D Sc cutoff j.1)).app
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).total
          (⟨t⟩ : OldCategory D Sc cutoff) x := by
  rw [shiftedSourceCanonicalEquiv_apply, LinearEquiv.symm_apply_apply]
  have h := congrArg (fun f => SuperNatTrans.total f (⟨t⟩ : OldCategory D Sc cutoff))
    (shiftedSourceParityIso_counit D Sc cutoff j.1 v)
  rw [Superfunctor.comp_total] at h
  exact LinearMap.congr_fun h x

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
