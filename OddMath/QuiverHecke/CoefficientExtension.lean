/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.BubbleParity
import OddMath.QuiverHecke.Presentation
import StringDiagrams.Super.Superalgebra
import StringDiagrams.Super.BoxProduct

/-!
# The coefficient-extended affine quiver-Hecke supercategory

Research issue #345, supporting Brundan–Ellis §8. This is an actual
supercategory with tensor-product Hom modules and Koszul composition, using
the source-independent coefficient algebra. It does not construct an SKM
action or assert that the abstract bubble map is faithful.

We use the algebra-isomorphic polynomial/exterior model of `SYM`. The box
product handles mixed-colour Hom spaces without requiring a global unit in
the locally unital `H_n` algebra. Its existing universe convention places
the ground ring and colour/weight types in a common universe.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams StringDiagrams.Supercategory
open scoped TensorProduct Classical
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

abbrev CoefficientH := BoxProd k (SuperalgebraCat (SKM.SYM.polynomialExteriorParity D k)) (H D Sc)

def coefficientObj (t : List I) : CoefficientH D Sc :=
  ⟨SuperalgebraCat.star _, (pres D Sc).obj (ob D t)⟩

/-- A coefficient times an independent affine upward morphism. -/
def coefficientHom {t t' : List I} (a : SKM.SYM.PolynomialExterior D k)
    (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) :
    coefficientObj D Sc t ⟶ coefficientObj D Sc t' :=
  BoxProd.tmulHom (SuperalgebraCat.ofElem a) f

/-- Composition includes the actual Koszul sign. In diagrammatic order,
the coefficient multiplication is reversed, as for endomorphism rings. -/
theorem coefficientHom_comp {t t' t'' : List I} {p q : ZMod 2}
    {a : SKM.SYM.PolynomialExterior D k}
    (ha : a ∈ SKM.SYM.polynomialExteriorParity D k p)
    (b : SKM.SYM.PolynomialExterior D k)
    (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t'))
    {g : (pres D Sc).obj (ob D t') ⟶ (pres D Sc).obj (ob D t'')}
    (hg : g ∈ Supercategory.parity (R := k) _ _ q) :
    coefficientHom D Sc a f ≫ coefficientHom D Sc b g =
      koszulSign p q • coefficientHom D Sc (b * a) (f ≫ g) :=
  BoxProd.tmulHom_comp_tmulHom
    (X := coefficientObj D Sc t) (Y := coefficientObj D Sc t') (Z := coefficientObj D Sc t'')
    ha f (SuperalgebraCat.ofElem b) hg

/-- The full abstract source coefficient is inserted through a proved algebra
equivalence, so no relation among its odd parameters is introduced. -/
def sourceCoefficientHom {t t' : List I} (a : SKM.SYM D k)
    (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) :
    coefficientObj D Sc t ⟶ coefficientObj D Sc t' :=
  coefficientHom D Sc (SKM.SYM.polynomialExteriorEquiv D k a) f

theorem odd_coefficient_comp_odd {t t' t'' : List I}
    (i : {i : I // D.parity i = 1})
    (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t'))
    {g : (pres D Sc).obj (ob D t') ⟶ (pres D Sc).obj (ob D t'')}
    (hg : g ∈ Supercategory.parity (R := k) _ _ 1) :
    sourceCoefficientHom D Sc (SKM.SYM.delta D k i) f ≫
      sourceCoefficientHom D Sc 1 g =
      -sourceCoefficientHom D Sc (SKM.SYM.delta D k i) (f ≫ g) := by
  unfold sourceCoefficientHom
  rw [map_one, coefficientHom_comp D Sc (SKM.SYM.polynomialExterior_delta_mem_odd D k i) _ _ hg]
  simp [koszulSign]

/-- Hom spaces are the genuine module tensor with the full abstract source
coefficient algebra, transported only through its proved algebra equivalence. -/
def sourceTensorEquiv (t t' : List I) :
    (SKM.SYM D k ⊗[k] ((pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t'))) ≃ₗ[k]
      (coefficientObj D Sc t ⟶ coefficientObj D Sc t') :=
  TensorProduct.congr (SKM.SYM.polynomialExteriorEquiv D k).toLinearEquiv (LinearEquiv.refl k _)

@[simp] theorem sourceTensorEquiv_tmul {t t' : List I} (a : SKM.SYM D k)
    (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) :
    sourceTensorEquiv D Sc t t' (a ⊗ₜ[k] f) = sourceCoefficientHom D Sc a f := rfl

end OddMath.QuiverHecke
