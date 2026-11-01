import OddMath.QuiverHecke.CyclotomicAction.ELVUnitFamilyCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVEvenUnitPositiveInverse

/-! # Even shifted unit-family component coordinates
DeformedMatrixComparison (6) and the positive profile of section 4
specialize to identity coefficient units for an even moving colour.
The actual ordered-mate comparison remains separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped BigOperators
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open OddMath.LowPolynomialCoordinates
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
local instance evenUnitFamilyPi : PiSupercategory k (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :=
  supermodulePiSupercategory

/-- Even ordinary columns require the identity coefficient diagonal. -/
theorem unitCoefficientDiagonal_even (i : {i : I // D.parity i = 0})
    (v t : List I) (m : ℕ) (b : Fin m → Old D Sc cutoff v t) :
    unitCoefficientDiagonal D Sc cutoff (D.parity i.1) v t m b = b := by
  ext r
  simp only [unitCoefficientDiagonal_apply, inductionUnitDotSign, i.property,
    smul_zero, sign_zero, one_smul]

/-- The literal even polynomial window in finite coordinates. -/
def evenUnitWindowVectorEquiv (i : I) (v t : List I) (m : ℕ)
    (hm : endpointQPDegree D cutoff i v = outputSDegree D i v + m) :
    (Fin m → Old D Sc cutoff v t) ≃ₗ[k] evenBoundaryRowWindow D Sc cutoff i v t :=
  (lowVectorEquiv (k := k) (M := Old D Sc cutoff v t) m).trans
    (LinearEquiv.ofEq _ _ (evenBoundaryRowWindow_eq_height D Sc cutoff i v t m hm).symm)

/-- Canonical parity coordinates and the literal even coefficient window. -/
def evenUnitFamilyComponentCoordinates (i : {i : I // D.parity i = 0})
    (v t : List I) (m : ℕ)
    (hm : endpointQPDegree D cutoff i.1 v = outputSDegree D i.1 v + m) :
    ((a : Option (Fin m)) →
      (unitMatrixFamily D Sc cutoff i.1
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m a).obj
          (⟨t⟩ : OldCategory D Sc cutoff)) ≃ₗ[k]
    ((((BalancedInduction.induction (append D Sc cutoff i.1)).obj
      ((BalancedInduction.restriction (append D Sc cutoff i.1)).obj
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))).obj
          (⟨t⟩ : OldCategory D Sc cutoff)) × evenBoundaryRowWindow D Sc cutoff i.1 v t) :=
  (unitFamilyPlainCoordinates D Sc cutoff i.1 v t m).trans
    ((LinearEquiv.refl k _).prodCongr
      (evenUnitWindowVectorEquiv D Sc cutoff i.1 v t m hm))

/-- The even shifted-family component inverse, with unscaled ordinary unit columns. -/
def evenUnitFamilyComponentEquiv (p : ZMod 2) (i : {i : I // D.parity i = 0})
    (v t : List I) (m : ℕ)
    (hm : endpointQPDegree D cutoff i.1 v = outputSDegree D i.1 v + m) :
    ((a : Option (Fin m)) →
      (unitMatrixFamily D Sc cutoff i.1
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m a).obj
          (⟨t⟩ : OldCategory D Sc cutoff)) ≃ₗ[k]
      Old D Sc cutoff (v ++ [i.1]) (t ++ [i.1]) :=
  (evenUnitFamilyComponentCoordinates D Sc cutoff i v t m hm).trans
    (evenUnitPositiveMatrixEquiv D Sc cutoff p i v t (by omega))

/-- Every even unit slot is the ordinary adjunction-unit/dot column. -/
theorem evenUnitFamilyComponentEquiv_apply (p : ZMod 2) (i : {i : I // D.parity i = 0})
    (v t : List I) (m : ℕ)
    (hm : endpointQPDegree D cutoff i.1 v = outputSDegree D i.1 v + m)
    (x : (a : Option (Fin m)) →
      (unitMatrixFamily D Sc cutoff i.1
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m a).obj
          (⟨t⟩ : OldCategory D Sc cutoff)) :
    evenUnitFamilyComponentEquiv D Sc cutoff p i v t m hm x =
      -toCyclotomic D Sc cutoff i.1 v t
        (evenSourceEquiv D Sc cutoff i v t
          (unitFamilyPlainCoordinates D Sc cutoff i.1 v t m x).1) +
      ∑ r : Fin m, inductionUnitDotColumn D Sc cutoff i.1 v t r.val
        ((unitFamilyPlainCoordinates D Sc cutoff i.1 v t m x).2 r) := by
  rw [evenUnitFamilyComponentEquiv, LinearEquiv.trans_apply]
  rw [show (evenUnitFamilyComponentCoordinates D Sc cutoff i v t m hm x) =
      ((unitFamilyPlainCoordinates D Sc cutoff i.1 v t m x).1,
        evenUnitWindowVectorEquiv D Sc cutoff i.1 v t m hm
          (unitFamilyPlainCoordinates D Sc cutoff i.1 v t m x).2) from rfl]
  have he := evenUnitPositiveMatrixEquiv_apply D Sc cutoff p i v t (by omega)
    (unitFamilyPlainCoordinates D Sc cutoff i.1 v t m x).1
    (evenUnitWindowVectorEquiv D Sc cutoff i.1 v t m hm
      (unitFamilyPlainCoordinates D Sc cutoff i.1 v t m x).2)
  refine he.trans ?_
  congr 1
  rw [evenUnitDotPolynomialMap_eq]
  change unitDotPolynomialMap D Sc cutoff i.1 v t
    ((lowVectorEquiv (k := k) (M := Old D Sc cutoff v t) m
      (unitFamilyPlainCoordinates D Sc cutoff i.1 v t m x).2).val) = _
  have h := unitDotPolynomialMap_diagonal D Sc cutoff i.1 v t m
    (unitFamilyPlainCoordinates D Sc cutoff i.1 v t m x).2
  rw [unitCoefficientDiagonal_even D Sc cutoff i] at h
  exact h

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor

