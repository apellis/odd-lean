/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.WeightedCoefficientSeparation
import OddMath.QuiverHecke.HomDimension

/-!
# The placement sign on the coefficient-extended Hom space

Research issue #345, toward Brundan–Ellis §8. Moving a coefficient `a` of `SYM` past an
affine morphism `f` costs the Koszul sign `(-1)^{|a||f|}`. On the tensor basis
`coefficientBasis a ⊗ nf i` both factors are homogeneous: the coefficient has the parity of
its exterior part and the normal form has parity `NFIdx.par`. The placement sign is the
linear involution that is diagonal in this basis with these signs. Being diagonal, it
preserves every span of basis vectors, in particular the weight window `ExtendedAtMost`.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
open scoped Classical TensorProduct
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

variable (k) in
/-- The sign `(-1)^{|a||i|}` of a tensor basis vector. -/
def placementSignCoeff {t t' : List I} (x : SKM.SYM.CoefficientIndex D × NFIdx t t') : k :=
  if ((x.1.2.card : ZMod 2) * x.2.par D) = 0 then 1 else -1

variable (k) in
theorem placementSignCoeff_mul_self {t t' : List I}
    (x : SKM.SYM.CoefficientIndex D × NFIdx t t') :
    placementSignCoeff k D x * placementSignCoeff k D x = 1 := by
  unfold placementSignCoeff
  split_ifs <;> simp

/-- The placement sign as a linear endomorphism, diagonal in the tensor basis. -/
def placementSignMap (t t' : List I) :
    (coefficientObj D Sc t ⟶ coefficientObj D Sc t') →ₗ[k]
      (coefficientObj D Sc t ⟶ coefficientObj D Sc t') :=
  (extensionBasis D Sc t t').constr k fun x => placementSignCoeff k D x • extensionBasis D Sc t t' x

theorem placementSignMap_basis (t t' : List I) (x : SKM.SYM.CoefficientIndex D × NFIdx t t') :
    placementSignMap D Sc t t' (extensionBasis D Sc t t' x) =
      placementSignCoeff k D x • extensionBasis D Sc t t' x := by
  simp [placementSignMap, Module.Basis.constr_basis]

theorem placementSignMap_involutive (t t' : List I) :
    Function.Involutive (placementSignMap D Sc t t') := by
  intro y
  have h : (placementSignMap D Sc t t').comp (placementSignMap D Sc t t') = LinearMap.id :=
    (extensionBasis D Sc t t').ext fun x => by
      simp only [LinearMap.comp_apply, placementSignMap_basis, map_smul, smul_smul,
        placementSignCoeff_mul_self, one_smul, LinearMap.id_apply]
  exact LinearMap.congr_fun h y

/-- **The placement sign**: the involution `a ⊗ f ↦ (-1)^{|a||f|} a ⊗ f` of the
coefficient-extended Hom space. -/
def placementSign (t t' : List I) :
    (coefficientObj D Sc t ⟶ coefficientObj D Sc t') ≃ₗ[k]
      (coefficientObj D Sc t ⟶ coefficientObj D Sc t') :=
  LinearEquiv.ofInvolutive (placementSignMap D Sc t t') (placementSignMap_involutive D Sc t t')

theorem placementSign_apply (t t' : List I) (y : coefficientObj D Sc t ⟶ coefficientObj D Sc t') :
    placementSign D Sc t t' y = placementSignMap D Sc t t' y := rfl

theorem placementSign_symm (t t' : List I) :
    (placementSign D Sc t t').symm = placementSign D Sc t t' := by
  ext y
  rw [LinearEquiv.symm_apply_eq, placementSign_apply, placementSign_apply,
    placementSignMap_involutive]

/-- On a tensor basis vector the placement sign is the Koszul sign of the coefficient
parity (the size of its exterior part) against the parity of the normal form. -/
theorem placementSign_sourceCoefficientHom (t t' : List I) (a : SKM.SYM.CoefficientIndex D)
    (i : NFIdx t t') :
    placementSign D Sc t t' (sourceCoefficientHom D Sc (SKM.SYM.coefficientBasis D k a) i.nf) =
      (if ((a.2.card : ZMod 2) * i.par D) = 0 then (1 : k) else -1) •
        sourceCoefficientHom D Sc (SKM.SYM.coefficientBasis D k a) i.nf := by
  rw [← extensionBasis_apply, placementSign_apply, placementSignMap_basis]
  rfl

/-- The placement sign preserves the weight window `ExtendedAtMost d`. -/
theorem placementSign_mem_extendedAtMost {t t' : List I} {d : ℕ}
    {y : coefficientObj D Sc t ⟶ coefficientObj D Sc t'} (hy : y ∈ ExtendedAtMost D Sc t t' d) :
    placementSign D Sc t t' y ∈ ExtendedAtMost D Sc t t' d := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    rw [placementSign_apply, placementSignMap_basis]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, hx, rfl⟩)
  | zero => simp
  | add y z _ _ hy hz => simpa only [map_add] using Submodule.add_mem _ hy hz
  | smul c y _ hy => simpa only [map_smul] using Submodule.smul_mem _ c hy

/-- The placement sign also preserves the lower windows `ExtendedAtLeast s`. -/
theorem placementSign_mem_extendedAtLeast {t t' : List I} {s : ℤ}
    {y : coefficientObj D Sc t ⟶ coefficientObj D Sc t'} (hy : y ∈ ExtendedAtLeast D Sc t t' s) :
    placementSign D Sc t t' y ∈ ExtendedAtLeast D Sc t t' s := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    rw [placementSign_apply, placementSignMap_basis]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, hx, rfl⟩)
  | zero => simp
  | add y z _ _ hy hz => simpa only [map_add] using Submodule.add_mem _ hy hz
  | smul c y _ hy => simpa only [map_smul] using Submodule.smul_mem _ c hy

end OddMath.QuiverHecke
