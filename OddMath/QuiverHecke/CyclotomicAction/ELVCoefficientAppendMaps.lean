import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientModuleMaps

/-! # Coefficient module maps under append induction and restriction

The source-word coefficient action in `SwappedVacuumCoordinates.md`, §6,
uses the original coefficient action after appending a word. The signed
balanced tensor comparison below identifies these maps literally.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Append induction preserves the full coefficient module map. Its tensor
formula includes both the coefficient slide and the source-map parity twist. -/
theorem coefficientModuleAction_induction (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    (BalancedInduction.induction (append D Sc cutoff i)).map
        (coefficientModuleAction D Sc cutoff M a) =
      coefficientModuleAction D Sc cutoff
        ((BalancedInduction.induction (append D Sc cutoff i)).obj M) a := by
  apply Superfunctor.hom_ext
  intro p w
  let J := append D Sc cutoff i
  let b := GradedAlgebra.proj (SKM.SYM.elvCoefficientParity D cutoff) p a
  have hb : b ∈ SKM.SYM.elvCoefficientParity D cutoff p :=
    (DirectSum.decompose (SKM.SYM.elvCoefficientParity D cutoff) a p).property
  change BalancedInduction.mapComponent J (coefficientModuleAction D Sc cutoff M a) p w =
    BalancedInduction.postcompose J M.toFunctor (coefficientEndomorphism D Sc cutoff w.word b)
  apply BalancedInduction.hom_ext
  intro v h m
  rw [BalancedInduction.mapComponent_tensor, coefficientModuleAction_app,
    BalancedInduction.postcompose_tensor]
  change BalancedInduction.tensor J M.toFunctor v (twist k p h)
    (M.map (X := v) (Y := v) (coefficientEndomorphism D Sc cutoff v.word b) m) = _
  rw [← BalancedInduction.balance]
  have he : J.map (X := v) (Y := v) (coefficientEndomorphism D Sc cutoff v.word b) =
      (coefficientEndomorphism D Sc cutoff (J.obj v).word b : J.obj v ⟶ J.obj v) :=
    append_coefficientEndomorphism D Sc cutoff i v.word b
  rw [he]
  have hs := coefficientEndomorphism_slide D Sc cutoff hb (J.obj v).word w.word h
  rw [← hs]

/-- Append restriction also preserves the original coefficient module map,
including its odd homogeneous component. -/
theorem coefficientModuleAction_restriction (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    (BalancedInduction.restriction (append D Sc cutoff i)).map
        (coefficientModuleAction D Sc cutoff M a) =
      coefficientModuleAction D Sc cutoff
        ((BalancedInduction.restriction (append D Sc cutoff i)).obj M) a := by
  apply Superfunctor.hom_ext
  intro p v
  change (coefficientModuleAction D Sc cutoff M a).app p ((append D Sc cutoff i).obj v) =
    M.map ((append D Sc cutoff i).map (X := v) (Y := v)
      (coefficientEndomorphism D Sc cutoff v.word
        (GradedAlgebra.proj (SKM.SYM.elvCoefficientParity D cutoff) p a)))
  rw [coefficientModuleAction_app, append_coefficientEndomorphism]
  rfl

variable (L : I × ℕ → ℕ)

/-- The literal power-quotient action also commutes with induction inside
its preserved module category; no weighted quotient replaces A/T. -/
theorem powerModuleCoefficientAction_induction (i : I)
    (M : CoefficientPowerModules D Sc cutoff (elementaryCoefficients (k := k) D cutoff) L)
    (a : CoefficientPowerQuotient (k := k) D cutoff L) :
    (BalancedInduction.induction (append D Sc cutoff i)).map
        (powerModuleCoefficientAction D Sc cutoff L M a) =
      powerModuleCoefficientAction D Sc cutoff L
        ((CoefficientPowerModules.induction D Sc cutoff
          (elementaryCoefficients (k := k) D cutoff) L
          (elementaryCoefficients_even (k := k) D cutoff) i).obj M) a := by
  obtain ⟨b, rfl⟩ := RingCon.mkₐ_surjective (α := k)
    (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon a
  change (BalancedInduction.induction (append D Sc cutoff i)).map
      (coefficientModuleAction D Sc cutoff M.obj b) =
    coefficientModuleAction D Sc cutoff
      ((BalancedInduction.induction (append D Sc cutoff i)).obj M.obj) b
  exact coefficientModuleAction_induction D Sc cutoff i M.obj b

/-- Restriction retains the same quotient coefficient endomorphisms. -/
theorem powerModuleCoefficientAction_restriction (i : I)
    (M : CoefficientPowerModules D Sc cutoff (elementaryCoefficients (k := k) D cutoff) L)
    (a : CoefficientPowerQuotient (k := k) D cutoff L) :
    (BalancedInduction.restriction (append D Sc cutoff i)).map
        (powerModuleCoefficientAction D Sc cutoff L M a) =
      powerModuleCoefficientAction D Sc cutoff L
        ((CoefficientPowerModules.restriction D Sc cutoff
          (elementaryCoefficients (k := k) D cutoff) L i).obj M) a := by
  obtain ⟨b, rfl⟩ := RingCon.mkₐ_surjective (α := k)
    (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon a
  change (BalancedInduction.restriction (append D Sc cutoff i)).map
      (coefficientModuleAction D Sc cutoff M.obj b) =
    coefficientModuleAction D Sc cutoff
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj M.obj) b
  exact coefficientModuleAction_restriction D Sc cutoff i M.obj b

end OddMath.QuiverHecke.ELVOld
