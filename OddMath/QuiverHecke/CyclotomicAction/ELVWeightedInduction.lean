import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedModuleDescent
import OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendSuperfunctor
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleAdjunction
import OddMath.QuiverHecke.CyclotomicAction.ELVPScalarBalance

/-! # Append induction preserves weighted coefficient annihilation
The reservoir quotient transport in SwappedVacuumCoordinates §6 uses the
actual old append functor and balanced induction. Full coefficient parity
is retained in the scalar slide before applying coend balance.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem oldQuotient_twist (v w : List I) (p : ZMod 2) (f : hom D Sc cutoff v w) :
    twist k p (X := (⟨v⟩ : OldCategory D Sc cutoff)) (Y := ⟨w⟩)
      ((ideal D Sc cutoff v w).mkQ f) =
      (ideal D Sc cutoff v w).mkQ
        (twist k p (X := obj D Sc cutoff v) (Y := obj D Sc cutoff w) f) := by
  simp only [twist_apply, oldCategory_proj, oldProj_mk, map_add, map_smul]

/-- The prescribed full coefficient monomial at an old word. -/
def oldCoefficientBasis (v : List I) (a : SKM.SYM.CoefficientIndex D) :
    (⟨v⟩ : OldCategory D Sc cutoff) ⟶ ⟨v⟩ :=
  (ideal D Sc cutoff v v).mkQ
    (coefficientIdentity D Sc cutoff v (SKM.SYM.coefficientBasis D k a))

/-- The complete output parity twist appears in the coefficient slide. -/
theorem oldCoefficientBasis_slide (v w : List I) (a : SKM.SYM.CoefficientIndex D)
    (f : (⟨v⟩ : OldCategory D Sc cutoff) ⟶ ⟨w⟩) :
    f ≫ oldCoefficientBasis D Sc cutoff w a =
      oldCoefficientBasis D Sc cutoff v a ≫
        twist k (a.2.card : ZMod 2) (X := (⟨v⟩ : OldCategory D Sc cutoff)) (Y := ⟨w⟩) f := by
  obtain ⟨f, rfl⟩ := (ideal D Sc cutoff v w).mkQ_surjective f
  have ha := SKM.SYM.elvModelQuotient_mem D (cutoff := cutoff)
    (SKM.SYM.coefficientBasis_mem_parity D k a)
  simp only [SKM.SYM.elvModelQuotient, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.symm_apply_apply] at ha
  have he := congrArg ((ideal D Sc cutoff v w).mkQ)
    (ELVPScalar.scalar_slide_homogeneous D Sc cutoff ha f)
  rw [oldQuotient_twist]
  exact he

@[simp] theorem append_oldCoefficientBasis (i : I) (v : List I)
    (a : SKM.SYM.CoefficientIndex D) :
    (CyclotomicCrossingTensor.append D Sc cutoff i).map
      (oldCoefficientBasis D Sc cutoff v a) =
      oldCoefficientBasis D Sc cutoff (v ++ [i]) a := by
  change (ideal D Sc cutoff (v ++ [i]) (v ++ [i])).mkQ
    (rightContext D Sc cutoff [i] v v
      (coefficientIdentity D Sc cutoff v (SKM.SYM.coefficientBasis D k a))) = _
  rw [rightContext_coefficientIdentity]
  rfl

/-- Actual old append induction preserves the annihilator class of the
weighted coefficient ideal, including its odd monomials. -/
theorem induced_killsWeightedCoefficients (N : ℕ) (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M) :
    KillsWeightedCoefficients D Sc cutoff N
      (BalancedInduction.induced (CyclotomicCrossingTensor.append D Sc cutoff i) M) := by
  intro w a ha
  let J := CyclotomicCrossingTensor.append D Sc cutoff i
  change BalancedInduction.postcompose J M.toFunctor
    (oldCoefficientBasis D Sc cutoff w a) = 0
  apply BalancedInduction.hom_ext
  rintro ⟨v⟩ h m
  rw [BalancedInduction.postcompose_tensor, oldCoefficientBasis_slide]
  have hc : oldCoefficientBasis D Sc cutoff (v ++ [i]) a =
      J.map (oldCoefficientBasis D Sc cutoff v a) :=
    (append_oldCoefficientBasis D Sc cutoff i v a).symm
  rw [hc, BalancedInduction.balance]
  have hz : M.toFunctor.map (oldCoefficientBasis D Sc cutoff v a) = 0 := hM v a ha
  rw [hz, LinearMap.zero_apply]
  simp only [BalancedInduction.tensor, TensorProduct.tmul_zero, map_zero,
    LinearMap.zero_apply]

/-- The reservoir-side induced module consequently exists on the literal
weighted quotient, on the same balanced tensor vector spaces. -/
def weightedInducedModule (N : ℕ) (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M) :
    Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k) :=
  weightedModule D Sc cutoff N
    (BalancedInduction.induced (CyclotomicCrossingTensor.append D Sc cutoff i) M)
    (induced_killsWeightedCoefficients D Sc cutoff N i M hM)

end OddMath.QuiverHecke.ELVOld
