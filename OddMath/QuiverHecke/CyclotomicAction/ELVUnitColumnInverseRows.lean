import OddMath.Algebra.MatrixInverseTransport
import OddMath.QuiverHecke.CyclotomicAction.ELVUnitColumnMatrices

/-! # Canonical unshifted coefficient rows of inverse unit matrices

The normalized left cap in DeformedMatrixComparison is a specified inverse
unit-matrix coordinate, followed by its original canonical source unshift.
The common-chart comparison below transports that exact row. The ordinary
right counit is a different field and is not substituted for it.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
section Rows
variable {k C : Type u} [CommRing k] [Category.{u} C]
  [Preadditive C] [Linear k C] [Supercategory k C]
  (M : Superfunctor k C (SVec k)) (w : C) (p : ZMod 2) (m : ℕ)
local instance unitInverseRowPi : PiSupercategory k (Superfunctor k C (SVec k)) :=
  supermodulePiSupercategory

/-- Project to precisely the r-th shifted value slot and remove its given shift. -/
def unitColumnUnshift (r : Fin m) : unitColumnSourceSpace p M m w ⟶ M.obj w :=
  SVec.ofHom (SVec.toLinearMap
    (((SKM.homParityShiftDatum (k := k) (r.val • p)).iso M).hom.total w) ∘ₗ LinearMap.proj r)

theorem unitColumnUnshift_apply (r : Fin m) (x : unitColumnSourceSpace p M m w) :
    unitColumnUnshift M w p m r x =
      ((SKM.homParityShiftDatum (k := k) (r.val • p)).iso M).hom.total w (x r) := rfl

/-- A specified inverse coefficient row, with exactly its canonical unshift. -/
def unitColumnInverseRow {W : SVec k} (e : unitColumnSourceSpace p M m w ≅ W) (r : Fin m) :
    W ⟶ M.obj w := e.inv ≫ unitColumnUnshift M w p m r

theorem unitColumnInverseRow_apply {W : SVec k} (e : unitColumnSourceSpace p M m w ≅ W)
    (r : Fin m) (x : W) :
    unitColumnInverseRow M w p m e r x =
      ((SKM.homParityShiftDatum (k := k) (r.val • p)).iso M).hom.total w (e.inv x r) := rfl

private theorem unitColumnInverseRow_linear {W : SVec k}
    (e : unitColumnSourceSpace p M m w ≅ W) (r : Fin m) :
    SVec.toLinearMap (unitColumnInverseRow M w p m e r) =
      SVec.toLinearMap (unitColumnUnshift M w p m r) ∘ₗ SVec.toLinearMap e.inv :=
  SVec.toLinearMap_comp e.inv (unitColumnUnshift M w p m r)
end Rows

section Coordinates
variable {k C D : Type u} [CommRing k] [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
  (M : Superfunctor k C (SVec k)) (N : Superfunctor k D (SVec k))
  (w : C) (v : D) (e : M.obj w ≃ₗ[k] N.obj v) (p : ZMod 2) (m : ℕ)

/-- The actual coordinate product intertwines the original unshifts. -/
theorem unitColumnUnshift_coordinate (r : Fin m) :
    SVec.toLinearMap (unitColumnUnshift N v p m r) ∘ₗ
        (unitColumnFamilyEquiv M N w v e p m).toLinearMap =
      e.toLinearMap ∘ₗ SVec.toLinearMap (unitColumnUnshift M w p m r) := by
  apply LinearMap.ext
  intro x
  exact shiftedModuleValueLinearEquiv_hom_coordinate M N w v e (r.val • p) (x r)
end Coordinates

section CommonComparison
variable {k C₀ C₁ C₂ : Type u} [CommRing k]
  [Category.{u} C₀] [Preadditive C₀] [Linear k C₀] [Supercategory k C₀]
  [Category.{u} C₁] [Preadditive C₁] [Linear k C₁] [Supercategory k C₁]
  [Category.{u} C₂] [Preadditive C₂] [Linear k C₂] [Supercategory k C₂]
  (M₀ : Superfunctor k C₀ (SVec k)) (M₁ : Superfunctor k C₁ (SVec k))
  (M₂ : Superfunctor k C₂ (SVec k)) (w₀ : C₀) (w₁ : C₁) (w₂ : C₂)
  (d : M₀.obj w₀ ≃ₗ[k] M₁.obj w₁) (d' : M₀.obj w₀ ≃ₗ[k] M₂.obj w₂)
  (p : ZMod 2) (m : ℕ) {B W W' : SVec k}
  (b : B ≃ₗ[k] W) (t : B ≃ₗ[k] W')
  (e : unitColumnSourceSpace p M₁ m w₁ ≅ W)
  (f : unitColumnSourceSpace p M₂ m w₂ ≅ W')
  (r : unitColumnSourceSpace p M₀ m w₀ →ₗ[k] B)

/-- Two proved forward matrix squares transport the specified inverse row
and its full canonical unshift. These hypotheses are supplied by the chosen
content and scalar matrix comparisons in the concrete left-cap application. -/
theorem unitColumnInverseRow_compare_common
    (hOld : b.toLinearMap ∘ₗ r = SVec.toLinearMap e.hom ∘ₗ
      (unitColumnFamilyEquiv M₀ M₁ w₀ w₁ d p m).toLinearMap)
    (hNew : t.toLinearMap ∘ₗ r = SVec.toLinearMap f.hom ∘ₗ
      (unitColumnFamilyEquiv M₀ M₂ w₀ w₂ d' p m).toLinearMap) (a : Fin m) :
    (d.symm.trans d').toLinearMap ∘ₗ SVec.toLinearMap (unitColumnInverseRow M₁ w₁ p m e a) =
      SVec.toLinearMap (unitColumnInverseRow M₂ w₂ p m f a) ∘ₗ (b.symm.trans t).toLinearMap := by
  have hMatrix := OddMath.FiniteSuperspace.commonChart_square
    (unitColumnFamilyEquiv M₀ M₁ w₀ w₁ d p m) b
    (unitColumnFamilyEquiv M₀ M₂ w₀ w₂ d' p m) t e f r hOld hNew
  have hCoordinate := OddMath.FiniteSuperspace.commonCoordinate_square
    (unitColumnFamilyEquiv M₀ M₁ w₀ w₁ d p m)
    (unitColumnFamilyEquiv M₀ M₂ w₀ w₂ d' p m) d d'
    (SVec.toLinearMap (unitColumnUnshift M₀ w₀ p m a))
    (SVec.toLinearMap (unitColumnUnshift M₁ w₁ p m a))
    (SVec.toLinearMap (unitColumnUnshift M₂ w₂ p m a))
    (unitColumnUnshift_coordinate M₀ M₁ w₀ w₁ d p m a)
    (unitColumnUnshift_coordinate M₀ M₂ w₀ w₂ d' p m a)
  have h := OddMath.FiniteSuperspace.inverse_row_square e f
    (unitColumnFamilyEquiv M₀ M₁ w₀ w₁ d p m |>.symm.trans
      (unitColumnFamilyEquiv M₀ M₂ w₀ w₂ d' p m)).toLinearMap
    (b.symm.trans t).toLinearMap (d.symm.trans d').toLinearMap
    (SVec.toLinearMap (unitColumnUnshift M₁ w₁ p m a))
    (SVec.toLinearMap (unitColumnUnshift M₂ w₂ p m a)) hMatrix hCoordinate
  simpa only [unitColumnInverseRow_linear] using h
end CommonComparison
end OddMath.QuiverHecke.ELVOld.BalancedInduction
