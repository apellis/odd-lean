import OddMath.Frontier.EQLiftDerivedSmall

/-!
# Derived tensor products with acyclic K-projective bimodules vanish

Generic.

* `catModule_isAcyclic_hom_of_isContractible`: for a contractible dg module `M` over a dg category, every Hom
  complex `HOM(M, N)` is acyclic (a cocycle of degree `n` is a morphism `M ⟶ N⟦n⟧`, null-homotopic since `M` is
  contractible);
* `derivedTensor_isZero_obj`: if every `B(-, Y)` of a dg bimodule `B` is contractible, `B ⊗^L (-)` sends every
  object to a zero object (its right adjoint `RHOM(B, -)` does);
* `bimoduleDerivedTensor_isZero_obj`: for dg rings, if the dg bimodule `M` is K-projective and acyclic as a left
  dg `A`-module, then `M ⊗^L_B (-) : D(B) ⥤ D(A)` sends every object to a zero object.
-/

noncomputable section

set_option linter.unusedSectionVars false

open CategoryTheory Limits

namespace OddMath.Frontier.EQLift

open DG

section CatModule

variable {C : Type*} [Category C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C]

theorem catModule_isAcyclic_hom_of_isContractible {M : CatModule C} (hM : CatModule.IsContractible M)
    (N : CatModule C) : DG.IsAcyclic (CatModule.HOM M N) := by
  refine CatModule.isAcyclic_hom_iff.mpr fun n m hmn z hz => ?_
  have hz' : CatModule.δ 0 1 (z.rightShift n 0 (zero_add n)) = 0 := by
    rw [CatModule.Cochain.δ_rightShift z n 0 1 (zero_add n) (n + 1) (add_comm 1 n), hz,
      CatModule.Cochain.rightShift_zero, _root_.smul_zero]
  obtain ⟨h, hh⟩ := CatModule.homotopic_zero_iff_exists.mp
    (hM.homotopic_zero_of_left
      (CatModule.Cocycle.homOf (CatModule.Cocycle.mk _ 1 (zero_add 1) hz')))
  refine ⟨koszulSign n • h.rightUnshift m (by omega), ?_⟩
  rw [CatModule.δ_units_smul, CatModule.Cochain.δ_rightUnshift h m (by omega) n 0 (zero_add n), smul_smul,
    Int.units_mul_self, one_smul, ← hh, CatModule.Cocycle.cochain_ofHom_homOf_eq_coe,
    CatModule.Cocycle.mk_coe, CatModule.Cochain.rightUnshift_rightShift]

end CatModule

section Derived

universe w₁ w₂ w v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [∀ X Y : D, DGAddCommGroup (X ⟶ Y)] [DGCategory D]
  (B : CatBimodule.{max u₁ u₂ v₁ w} D C) (hB : ∀ Y : C, CatModule.IsKProjective (B.left Y))
  [CatModule.HasDerivedCategory.{w₁, max u₁ u₂ v₁ w} C] [CatModule.HasDerivedCategory.{w₂, max u₁ u₂ v₁ w} D]

/-- If every `B(-, Y)` is contractible, `RHOM(B, -)` sends every object to a zero object. -/
theorem rhom_isZero_obj (hc : ∀ Y, CatModule.IsContractible (B.left Y))
    (W : CatModule.DerivedCategory.{w₂, max u₁ u₂ v₁ w} D) :
    IsZero ((CatModule.DerivedCategory.rhom B hB).obj W) := by
  have := Localization.essSurj (CatModule.DerivedCategory.Q (C := D)) (CatModule.quasiIso D)
  refine IsZero.of_iso ?_ ((CatModule.DerivedCategory.rhom B hB).mapIso
    (CatModule.DerivedCategory.Q.objObjPreimageIso W).symm)
  refine IsZero.of_iso ?_ ((CatModule.DerivedCategory.QCompRhomIso B hB).app _)
  exact (CatModule.DerivedCategory.isZero_Q_obj_iff _).mpr fun Y =>
    catModule_isAcyclic_hom_of_isContractible (hc Y) _

/-- If every `B(-, Y)` is contractible, `B ⊗^L (-)` sends every object to a zero object. -/
theorem derivedTensor_isZero_obj (hc : ∀ Y, CatModule.IsContractible (B.left Y))
    (X : CatModule.DerivedCategory.{w₁, max u₁ u₂ v₁ w} C) :
    IsZero ((CatModule.DerivedCategory.derivedTensor.{w₁, w₂} B hB).obj X) := by
  rw [IsZero.iff_id_eq_zero]
  apply ((CatModule.DerivedCategory.derivedTensorAdjunction B hB).homEquiv _ _).injective
  exact (rhom_isZero_obj B hB hc _).eq_of_tgt _ _

end Derived

section Ring

universe w₁ w₂ w₃ w₄

open OddMath.Frontier.EQFunctor

variable {A B : Type} [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B] [DGAddCommGroup B] [DGRing B]
  (M : Type) [AddCommGroup M] [DGAddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M] [DGBimodule A B M]
  (hM : DG.IsKProjective.{0} A M)
  [CatModule.HasDerivedCategory.{w₁, 0} (SingleObj B)] [CatModule.HasDerivedCategory.{w₂, 0} (SingleObj A)]
  [DG.HasDerivedCategory.{w₃, 0} B] [DG.HasDerivedCategory.{w₄, 0} A]

/-- **`M ⊗^L_B (-)` vanishes when `M` is K-projective and acyclic as a left dg `A`-module.** -/
theorem bimoduleDerivedTensor_isZero_obj (hac : DG.IsAcyclic M) (Y : DG.DerivedCategory.{w₃, 0} B) :
    IsZero ((bimoduleDerivedTensor.{w₁, w₂, w₃, w₄} A B M hM).obj Y) :=
  (CatModule.DerivedCategory.singleObjEquivalence A).functor.map_isZero
    (derivedTensor_isZero_obj _ (catBimodule_left_isKProjective A B M hM)
      (fun Y => catBimodule_left_isKProjective A B M hM Y _ (fun _ => hac) (𝟙 _)) _)

end Ring

end OddMath.Frontier.EQLift
