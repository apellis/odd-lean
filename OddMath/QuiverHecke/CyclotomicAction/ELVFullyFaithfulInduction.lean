import OddMath.QuiverHecke.CyclotomicAction.ELVQuotientInduction
import OddMath.QuiverHecke.CyclotomicAction.ELVOldContentCategory

/-! # Extension from a full content category

The balanced induction unit along a fully faithful functor is an isomorphism.
This gives the content-module extension needed in SwappedVacuumCoordinates §6,
without an equivalence with arbitrary modules on the whole old category.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory TensorProduct
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Preadditive D] [Linear k D]
  (J : C ⥤ D) [J.Full] [J.Faithful] [J.Additive] [J.Linear k]

/-- Full faithfulness makes the inverse Hom map linear. -/
def preimageLinearMap (v w : C) : (J.obj v ⟶ J.obj w) →ₗ[k] (v ⟶ w) where
  toFun := J.preimage
  map_add' f g := J.map_injective (by simp)
  map_smul' r f := J.map_injective (by simp)

variable (M : C ⥤ SVec k) [M.Additive] [M.Linear k]

/-- Evaluation after lifting the coefficient arrow through the full inclusion. -/
def fullyFaithfulEvaluationTensor (w v : C) :
    (J.obj v ⟶ J.obj w) ⊗[k] M.obj v →ₗ[k] M.obj w :=
  TensorProduct.lift ((M.mapLinearMap (R := k)).comp (preimageLinearMap J v w))

/-- The inverse of the unit, on the same balanced quotient used for induction. -/
def fullyFaithfulUnitInverse (w : C) : Obj J M (J.obj w) →ₗ[k] M.obj w :=
  lift J M (J.obj w) (fullyFaithfulEvaluationTensor J M w) (by
    intro v v' f h m
    change M.map (J.preimage (J.map f ≫ h)) m =
      M.map (J.preimage h) (M.map f m)
    rw [Functor.preimage_comp, Functor.preimage_map, M.map_comp]
    rfl)

@[simp] theorem fullyFaithfulUnitInverse_tensor (w v : C)
    (h : J.obj v ⟶ J.obj w) (m : M.obj v) :
    fullyFaithfulUnitInverse J M w (tensor J M v h m) = M.map (J.preimage h) m := by
  rw [fullyFaithfulUnitInverse, lift_tensor]
  rfl

theorem fullyFaithfulUnitInverse_unit (w : C) :
    fullyFaithfulUnitInverse J M w ∘ₗ unit J M w = LinearMap.id := by
  ext m
  change fullyFaithfulUnitInverse J M w (unit J M w m) = m
  rw [unit_apply, fullyFaithfulUnitInverse_tensor, Functor.preimage_id, M.map_id]
  rfl

theorem unit_fullyFaithfulUnitInverse (w : C) :
    unit J M w ∘ₗ fullyFaithfulUnitInverse J M w = LinearMap.id := by
  apply hom_ext
  intro v h m
  change unit J M w (fullyFaithfulUnitInverse J M w (tensor J M v h m)) =
    tensor J M v h m
  rw [fullyFaithfulUnitInverse_tensor, unit_apply]
  have hb := balance J M (J.preimage h) (𝟙 (J.obj w)) m
  rw [Functor.map_preimage, Category.comp_id] at hb
  exact hb.symm

variable [Supercategory k C] [Supercategory k D] [IsSuperfunctor k J]

/-- Pointwise unit isomorphisms, natural in all source arrows. -/
def fullyFaithfulUnitNatIso (L : Superfunctor k C (SVec k)) :
    L.toFunctor ≅ ((restriction J).obj (induced J L)).toFunctor :=
  NatIso.ofComponents (fun w =>
    { hom := unit J L.toFunctor w
      inv := fullyFaithfulUnitInverse J L.toFunctor w
      hom_inv_id := fullyFaithfulUnitInverse_unit J L.toFunctor w
      inv_hom_id := unit_fullyFaithfulUnitInverse J L.toFunctor w })
    (fun f => (unit_naturality J L.toFunctor f).symm)

/-- Restricting the induced extension recovers the original supermodule. -/
def fullyFaithfulUnitIso (L : Superfunctor k C (SVec k)) :
    L ≅ (restriction J).obj (induced J L) :=
  moduleIsoOfEvenNatIso _ _ (fullyFaithfulUnitNatIso J L)
    (fun w => unit_mem J L w)
    (fun w => Supercategory.inv_mem ((fullyFaithfulUnitNatIso J L).app w)
      (unit_mem J L w))

/-- The extension comparison uses the established adjunction unit. -/
theorem fullyFaithfulUnitIso_hom (L : Superfunctor k C (SVec k)) :
    (fullyFaithfulUnitIso J L).hom = (adjunctionUnit J).app L := by
  apply Superfunctor.hom_ext
  intro p v
  rfl

/-- The comparison is natural against all supernatural module maps. -/
def fullyFaithfulUnitNaturalIso :
    𝟭 (Superfunctor k C (SVec k)) ≅ induction J ⋙ restriction J :=
  NatIso.ofComponents (fullyFaithfulUnitIso J) (by
    intro L N f
    simp only [fullyFaithfulUnitIso_hom]
    exact (adjunctionUnit J).naturality f)

end OddMath.QuiverHecke.ELVOld.BalancedInduction

namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (ν : List I)

/-- A fixed-content module has a canonical extension to the whole old category,
whose restriction is isomorphic to the original module. -/
def oldContentExtensionUnitIso (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k)) :
    M ≅ (BalancedInduction.restriction (oldContentInclusion D Sc cutoff ν)).obj
      (BalancedInduction.induced (oldContentInclusion D Sc cutoff ν) M) :=
  BalancedInduction.fullyFaithfulUnitIso (oldContentInclusion D Sc cutoff ν) M

end OddMath.QuiverHecke.ELVOld
