import OddMath.QuiverHecke.CyclotomicAction.ELVInductionUnitInverseNaturality
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridRouquierPowers

/-! # The finite dotted-unit boundary in the module Rouquier target

Brundan–Ellis (1.13) at a vacuum: the prescribed even unit matrix inverse
supplies homogeneous coefficient cells, their finite window and their
reconstruction identity. The ordinary unit and signed dot are unchanged.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open scoped BigOperators
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
private def evaluation {k : Type u} [CommRing k] {C R : Type*}
    [Category C] [Category R] [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive R] [Linear k R] [Supercategory k R] (M : C) :
    Superfunctor k C R ⥤ R where
  obj F := F.obj M
  map f := f.total M
  map_id F := SuperNatTrans.id_total F.toFunctor M
  map_comp f g := Superfunctor.comp_total f g M
private instance evaluationAdditive {k : Type u} [CommRing k] {C R : Type*}
    [Category C] [Category R] [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive R] [Linear k R] [Supercategory k R] (M : C) :
    (evaluation (k := k) (R := R) M).Additive where
  map_add {F G f g} := by
    change (f.app 0 M + g.app 0 M) + (f.app 1 M + g.app 1 M) =
      (f.app 0 M + f.app 1 M) + (g.app 0 M + g.app 1 M)
    abel

variable {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
  (m : ℕ)
  (e : ∀ M, OddMath.FiniteSupermodule.product (unitColumnModuleFamily p M m) ≅
    (restriction J).obj ((induction J).obj M))
  (he : ∀ M, (e M).hom = unitColumnModuleMap J hα M m)

/-- The finite inverse row, zero outside its prescribed window. -/
def inductionVacuumCoefficient (n : ℕ) :
    inductionModuleCell (k := k) J ≫ restrictionModuleCell (k := k) J ⟶
      𝟙 (inductionModulePiCategory (k := k) C) :=
  if hn : n < m then unitColumnInverseTransformation J hα m e he ⟨n, hn⟩ else 0

theorem inductionVacuumCoefficient_mem (n : ℕ) :
    inductionVacuumCoefficient J hα m e he n ∈ parity (R := k) _ _ ((n : ZMod 2) * p) := by
  unfold inductionVacuumCoefficient
  split_ifs with hn
  · simpa only [unitColumnInverseTransformation, nsmul_eq_mul] using
      Superfunctor.IsSupernatural.toSuperNatTrans_mem
        (F := inductionModuleCell (k := k) J ≫ restrictionModuleCell (k := k) J)
        (G := 𝟙 (inductionModulePiCategory (k := k) C))
        (unitColumnInverseRow_supernatural J hα m e he ⟨n, hn⟩)
  · exact Submodule.zero_mem _

theorem inductionVacuumCoefficient_total (n : ℕ) (hn : n < m)
    (M : Superfunctor k C (SVec k)) :
    (inductionVacuumCoefficient J hα m e he n).total M =
      unitColumnInverseRow J M m (e M) ⟨n, hn⟩ := by
  rw [inductionVacuumCoefficient, dite_eq_left hn, unitColumnInverseTransformation_total]

private theorem coefficient_entry (j l : ℕ) (hj : j < m) (hl : l < m) :
    SKM.RouquierBoundary.cup (inductionModuleAdjunction (k := k) J) (inductionModuleDot J hα) j ≫
      inductionVacuumCoefficient J hα m e he l =
        if j = l then 𝟙 (𝟙 (inductionModulePiCategory (k := k) C)) else 0 := by
  classical
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro M
  rw [inductionModuleUnitPower_eq, Superfunctor.comp_total,
    gridUnitColumnTransformation_total, inductionVacuumCoefficient_total J hα m e he l hl]
  have h := unitDotColumn_inverseRow J hα M m (e M) (he M) ⟨j, hj⟩ ⟨l, hl⟩
  simp only [Fin.mk.injEq] at h
  by_cases hjl : j = l
  · rw [ite_eq_left hjl] at h ⊢
    exact h.trans (SuperNatTrans.id_total (𝟭 (Superfunctor k C (SVec k))) M).symm
  · rw [ite_eq_right hjl] at h ⊢
    simpa only [SuperNatTrans.total, Superfunctor.zero_app, zero_add] using h

private theorem coefficient_reconstruction :
    (∑ n ∈ Finset.range m, inductionVacuumCoefficient J hα m e he n ≫
      SKM.RouquierBoundary.cup (inductionModuleAdjunction (k := k) J) (inductionModuleDot J hα) n) =
        𝟙 (inductionModuleCell (k := k) J ≫ restrictionModuleCell (k := k) J) := by
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro M
  change (evaluation M).map _ = (evaluation M).map _
  rw [CategoryTheory.Functor.map_sum, CategoryTheory.Functor.map_id]
  simp only [CategoryTheory.Functor.map_comp]
  have hs :
      (∑ n ∈ Finset.range m,
        (inductionVacuumCoefficient J hα m e he n).total M ≫
          (SKM.RouquierBoundary.cup (inductionModuleAdjunction (k := k) J)
            (inductionModuleDot J hα) n).total M) =
      ∑ r : Fin m, unitColumnInverseRow J M m (e M) r ≫ unitDotColumn J hα M r.val := by
    classical
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro n hn
    rw [inductionVacuumCoefficient_total J hα m e he n (Finset.mem_range.mp hn),
      inductionModuleUnitPower_eq, gridUnitColumnTransformation_total]
    rw [dite_eq_left (Finset.mem_range.mp hn)]
  exact hs.trans (sum_unitColumnInverseRow_unitDotColumn J hα M m (e M) (he M))

/-- The existing Rouquier boundary record is constructed from the specified
unit matrix isomorphisms. The input is supplied by the constructed old
missing-colour module inverse, not by an extra inverse premise there. -/
def inductionVacuumCoefficients :
    SKM.RouquierBoundary.Coefficients (inductionModuleAdjunction (k := k) J)
      (inductionModuleDot J hα) p m where
  dot_mem := inductionModuleDot_mem J hα
  coeff := inductionVacuumCoefficient J hα m e he
  coeff_mem := inductionVacuumCoefficient_mem J hα m e he
  total := coefficient_reconstruction J hα m e he
  entry := coefficient_entry J hα m e he

end OddMath.QuiverHecke.ELVOld.BalancedInduction
