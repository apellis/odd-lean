import OddMath.Frontier.EQHalfGradedUnitParity
import DG.HalfGraded.SuperK0

/-!
# The low-rank unit on compact parity and super Grothendieck groups

The comparisons below use the existing compact internal shifts and parity object map.
The induced super Grothendieck equivalence is descended from `compactK0Equiv` through
its actual parity relations, not through a newly defined quotient or transported shift.
No numerical Grothendieck-group or tensor-product formula is asserted.
-/

noncomputable section
universe w w₂
namespace OddMath.Frontier.EQHalfGradedUnit
open CategoryTheory DG

variable {N : ℕ}
  [CatModule.HasDerivedCategory.{w, w} (WeightCategory source.Regraded)]
  [CatModule.HasDerivedCategory.{w₂, w} (WeightCategory (target N).Regraded)]

/-- The existing perfect induction commutes with the existing compact internal shifts. -/
def perfectInductionInternalShiftIso (hN : N ≤ 1) (s : ℤ) :
    CatModule.DerivedCategory.perfectInduction (weightFunctor N) ⋙
        (CatModule.DerivedCategory.compactInternalShiftAction (target N).Regraded).functor s ≅
      (CatModule.DerivedCategory.compactInternalShiftAction source.Regraded).functor s ⋙
        CatModule.DerivedCategory.perfectInduction (weightFunctor N) :=
  NatIso.ofComponents
    (fun X => ObjectProperty.isoMk _ ((derivedEquivalenceInternalShiftIso hN s).app X.obj))
    (fun f => by
      apply (compactSubcategory _).ι.map_injective
      exact (derivedEquivalenceInternalShiftIso hN s).hom.naturality f.hom)

/-- Actual perfect induction commutes with the pinned compact parity object map. -/
def perfectInductionParityIso (hN : N ≤ 1)
    (X : CatModule.PerfectDerivedCategory.{w, w} (WeightCategory source.Regraded)) :
    (CatModule.DerivedCategory.perfectInduction (weightFunctor N)).obj
        (HalfGradedDGRing.parityShiftCompact source X) ≅
      HalfGradedDGRing.parityShiftCompact (target N)
        ((CatModule.DerivedCategory.perfectInduction (weightFunctor N)).obj X) :=
  ObjectProperty.isoMk _ ((derivedEquivalenceParityIso hN).app X.obj).symm

/-- On every compact class, the existing K₀ equivalence respects actual parity. -/
theorem compactK0Equiv_parity (hN : N ≤ 1)
    (X : CatModule.PerfectDerivedCategory.{w, w} (WeightCategory source.Regraded)) :
    compactK0Equiv hN (DG.K0.mk (HalfGradedDGRing.parityShiftCompact source X)) =
      DG.K0.mk (HalfGradedDGRing.parityShiftCompact (target N)
        ((CatModule.DerivedCategory.perfectInduction (weightFunctor N)).obj X)) := by
  rw [compactK0Equiv, DGCategory.K0.mapEquivOfIsQuasiEquivalence_apply,
    DGCategory.K0.map_mk]
  exact DG.K0.mk_eq_of_iso (perfectInductionParityIso hN X)

/-- On every compact class, the same equivalence respects every actual internal shift. -/
theorem compactK0Equiv_internalShift (hN : N ≤ 1) (s : ℤ)
    (X : CatModule.PerfectDerivedCategory.{w, w} (WeightCategory source.Regraded)) :
    compactK0Equiv hN (DG.K0.mk
        (((CatModule.DerivedCategory.compactInternalShiftAction source.Regraded).functor s).obj X)) =
      DG.K0.mk
        (((CatModule.DerivedCategory.compactInternalShiftAction (target N).Regraded).functor s).obj
          ((CatModule.DerivedCategory.perfectInduction (weightFunctor N)).obj X)) := by
  rw [compactK0Equiv, DGCategory.K0.mapEquivOfIsQuasiEquivalence_apply,
    DGCategory.K0.map_mk]
  exact DG.K0.mk_eq_of_iso ((perfectInductionInternalShiftIso hN s).app X).symm

/-- The original compact equivalence acts by actual perfect induction on object classes. -/
theorem compactK0Equiv_mk (hN : N ≤ 1)
    (X : CatModule.PerfectDerivedCategory.{w, w} (WeightCategory source.Regraded)) :
    compactK0Equiv hN (DG.K0.mk X) =
      DG.K0.mk ((CatModule.DerivedCategory.perfectInduction (weightFunctor N)).obj X) := by
  rw [compactK0Equiv, DGCategory.K0.mapEquivOfIsQuasiEquivalence_apply,
    DGCategory.K0.map_mk]

/-- The actual parity-relation subgroups correspond under the original compact K₀ equivalence. -/
theorem compactK0Equiv_parityRelations (hN : N ≤ 1) :
    (K0Rel.parityRelations (HalfGradedDGRing.parityShiftCompact source)).map
        (compactK0Equiv hN).toAddMonoidHom =
      K0Rel.parityRelations (HalfGradedDGRing.parityShiftCompact (target N)) := by
  simp only [K0Rel.parityRelations, AddMonoidHom.map_closure]
  apply le_antisymm
  · apply (AddSubgroup.closure_le _).mpr
    rintro _ ⟨_, ⟨X, rfl⟩, rfl⟩
    apply AddSubgroup.subset_closure
    refine ⟨(CatModule.DerivedCategory.perfectInduction (weightFunctor N)).obj X, ?_⟩
    change compactK0Equiv hN
      (DG.K0.mk (HalfGradedDGRing.parityShiftCompact source X) - DG.K0.mk X) = _
    rw [map_sub, compactK0Equiv_parity, compactK0Equiv_mk]
  · apply (AddSubgroup.closure_le _).mpr
    rintro _ ⟨Y, rfl⟩
    let E := derivedEquivalence hN
    have : E.symm.functor.Additive := E.toAdjunction.right_adjoint_additive
    let X : CatModule.PerfectDerivedCategory.{w, w} (WeightCategory source.Regraded) :=
      ⟨E.inverse.obj Y.obj, Y.property.map_of_equivalence E.symm⟩
    have he : (CatModule.DerivedCategory.perfectInduction (weightFunctor N)).obj X ≅ Y :=
      ObjectProperty.isoMk _ (E.counitIso.app Y.obj)
    have hp : HalfGradedDGRing.parityShiftCompact (target N)
        ((CatModule.DerivedCategory.perfectInduction (weightFunctor N)).obj X) ≅
        HalfGradedDGRing.parityShiftCompact (target N) Y :=
      ObjectProperty.isoMk _ ((HalfGradedDGRing.parityShiftD (target N)).mapIso
        (E.counitIso.app Y.obj))
    apply AddSubgroup.subset_closure
    refine ⟨DG.K0.mk (HalfGradedDGRing.parityShiftCompact source X) - DG.K0.mk X,
      ⟨X, rfl⟩, ?_⟩
    change compactK0Equiv hN
      (DG.K0.mk (HalfGradedDGRing.parityShiftCompact source X) - DG.K0.mk X) = _
    rw [map_sub, compactK0Equiv_parity, compactK0Equiv_mk,
      DG.K0.mk_eq_of_iso he, DG.K0.mk_eq_of_iso hp]

/-- Descent of the original compact K₀ equivalence to the pinned parity quotients. -/
def compactParityQuotientEquiv (hN : N ≤ 1) :
    DGCategory.K0.{w, w} (WeightCategory source.Regraded) ⧸
        K0Rel.parityRelations (HalfGradedDGRing.parityShiftCompact source) ≃+
      DGCategory.K0.{w₂, w} (WeightCategory (target N).Regraded) ⧸
        K0Rel.parityRelations (HalfGradedDGRing.parityShiftCompact (target N)) :=
  QuotientAddGroup.congr _ _ (compactK0Equiv hN) (compactK0Equiv_parityRelations hN)

/-- The actual compact super Grothendieck groups are equivalent in ranks zero and one. -/
def superK0cEquiv (hN : N ≤ 1) :
    HalfGradedDGRing.SuperK0c.{w, w} source ≃+
      HalfGradedDGRing.SuperK0c.{w₂, w} (target N) :=
  (HalfGradedDGRing.superK0cEquiv source).trans
    ((compactParityQuotientEquiv hN).trans (HalfGradedDGRing.superK0cEquiv (target N)).symm)

/-- The super equivalence sends every compact object class to actual perfect induction. -/
theorem superK0cEquiv_mk (hN : N ≤ 1)
    (X : CatModule.PerfectDerivedCategory.{w, w} (WeightCategory source.Regraded)) :
    superK0cEquiv hN (K0Rel.mk X) =
      K0Rel.mk ((CatModule.DerivedCategory.perfectInduction (weightFunctor N)).obj X) := by
  apply (HalfGradedDGRing.superK0cEquiv (target N)).injective
  simp only [superK0cEquiv, AddEquiv.trans_apply, AddEquiv.apply_symm_apply,
    HalfGradedDGRing.superK0cEquiv_mk]
  change QuotientAddGroup.mk (compactK0Equiv hN (DG.K0.mk X)) = _
  rw [compactK0Equiv_mk]

end OddMath.Frontier.EQHalfGradedUnit
