import OddMath.Frontier.EQFunctorEmbeddingAbelian
import DG.Module.ExternalInterchange

/-!
# `J^A` and `J^H` on `(ONH_a ⊗ ONH_b)`-modules

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§4.4, the Morita equivalences (4.30)–(4.31) on the components `ONH_a ⊗ ONH_b` used in Corollary
4.21 (ranks `a = a' + 2`, `b = b' + 2`).

With `Z_a ⊠ Z_b` the external tensor product of dg bimodules, a dg
`(ONH_a ⊗ ONH_b, OΛ_a ⊗ OΛ_b)`-bimodule (dg-lean's `DG.ExternalTensor.instDGBimodule`), and
`Z_a^∨ ⊠ Z_b^∨` the corresponding `(OΛ_a ⊗ OΛ_b, ONH_a ⊗ ONH_b)`-bimodule:

* `zzTensorDualEquiv : (Z_a ⊠ Z_b) ⊗_{OΛ_a ⊗ OΛ_b} (Z_a^∨ ⊠ Z_b^∨) ≅ ONH_a ⊗ ONH_b` and
  `zzDualTensorEquiv : (Z_a^∨ ⊠ Z_b^∨) ⊗_{ONH_a ⊗ ONH_b} (Z_a ⊠ Z_b) ≅ OΛ_a ⊗ OΛ_b`, isomorphisms of
  dg bimodules (the interchange isomorphism `DG.ExternalTensor.interchangeEquiv`, the rank-`a` and
  rank-`b` isomorphisms of `EQZnMorita`, and `A ⊠ B ≅ A ⊗ B`);
* `JA2 a b : (ONH_a ⊗ ONH_b)-dmod ≌ (OΛ_a ⊗ OΛ_b)-dmod`, `M ↦ (Z_a^∨ ⊠ Z_b^∨) ⊗_{ONH_a ⊗ ONH_b} M`,
  and `JH2 a b` on homotopy categories.
-/

noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace OddMath.Frontier.EQFunctor

open OddMath.Frontier.EQSkewDifferential (osymDG Zn)
open OddMath.Frontier.EQOnhDG (ONH)
open DG MulOpposite TensorProductOver.RightAction

variable (a b : ℕ)

local notation "𝒪a" => DGAlgebra.gradingSubmodule ℤ (ONH a)
local notation "𝒪b" => DGAlgebra.gradingSubmodule ℤ (ONH b)
local notation "Λa" => DGAlgebra.gradingSubmodule ℤ (osymDG (a + 2))
local notation "Λb" => DGAlgebra.gradingSubmodule ℤ (osymDG (b + 2))

/-- `Z_a ⊠ Z_b`. -/
abbrev ZZ : Type := Zn (a + 2) ⊗[ℤ] Zn (b + 2)

/-- `Z_a^∨ ⊠ Z_b^∨`. -/
abbrev ZZDual : Type := ZnDual a ⊗[ℤ] ZnDual b

/-- `(Z_a^∨ ⊠ Z_b^∨) ⊗_{ONH_a ⊗ ONH_b} (Z_a ⊠ Z_b) ≅ OΛ_a ⊗ OΛ_b` as dg `OΛ_a ⊗ OΛ_b`-modules. -/
def zzDualTensorEquiv :
    TensorProductOver (𝒪a ᵍ⊗[ℤ] 𝒪b) (ZZDual a b) (ZZ a b) ≃ᵈᵍ[Λa ᵍ⊗[ℤ] Λb] (Λa ᵍ⊗[ℤ] Λb) :=
  ((ExternalTensor.interchangeEquiv (osymDG (a + 2)) (osymDG (b + 2)) (ONH a) (ONH b) (ZnDual a)
      (ZnDual b) (Zn (a + 2)) (Zn (b + 2))).trans
    (ExternalTensor.tensorEquiv (znDualTensorEquiv a) (znDualTensorEquiv b))).trans
    (ExternalTensor.regularEquiv (osymDG (a + 2)) (osymDG (b + 2)))

theorem zzDualTensorEquiv_op_smul (x : Λa ᵍ⊗[ℤ] Λb)
    (t : TensorProductOver (𝒪a ᵍ⊗[ℤ] 𝒪b) (ZZDual a b) (ZZ a b)) :
    zzDualTensorEquiv a b (op x • t) = op x • zzDualTensorEquiv a b t := by
  simp only [zzDualTensorEquiv, DGModuleEquiv.trans_apply]
  rw [show ExternalTensor.interchangeEquiv (osymDG (a + 2)) (osymDG (b + 2)) (ONH a) (ONH b)
      (ZnDual a) (ZnDual b) (Zn (a + 2)) (Zn (b + 2)) (op x • t) = op x •
      ExternalTensor.interchangeEquiv (osymDG (a + 2)) (osymDG (b + 2)) (ONH a) (ONH b)
        (ZnDual a) (ZnDual b) (Zn (a + 2)) (Zn (b + 2)) t from
      ExternalTensor.interchange_op_smul x t,
    ExternalTensor.tensorEquiv_op_smul _ _ (znDualTensorEquiv_op_smul a)
      (znDualTensorEquiv_op_smul b), ExternalTensor.regularEquiv_op_smul]

/-- `(Z_a ⊠ Z_b) ⊗_{OΛ_a ⊗ OΛ_b} (Z_a^∨ ⊠ Z_b^∨) ≅ ONH_a ⊗ ONH_b` as dg `ONH_a ⊗ ONH_b`-modules. -/
def zzTensorDualEquiv :
    TensorProductOver (Λa ᵍ⊗[ℤ] Λb) (ZZ a b) (ZZDual a b) ≃ᵈᵍ[𝒪a ᵍ⊗[ℤ] 𝒪b] (𝒪a ᵍ⊗[ℤ] 𝒪b) :=
  ((ExternalTensor.interchangeEquiv (ONH a) (ONH b) (osymDG (a + 2)) (osymDG (b + 2)) (Zn (a + 2))
      (Zn (b + 2)) (ZnDual a) (ZnDual b)).trans
    (ExternalTensor.tensorEquiv (znTensorDualEquiv a) (znTensorDualEquiv b))).trans
    (ExternalTensor.regularEquiv (ONH a) (ONH b))

theorem zzTensorDualEquiv_op_smul (x : 𝒪a ᵍ⊗[ℤ] 𝒪b)
    (t : TensorProductOver (Λa ᵍ⊗[ℤ] Λb) (ZZ a b) (ZZDual a b)) :
    zzTensorDualEquiv a b (op x • t) = op x • zzTensorDualEquiv a b t := by
  simp only [zzTensorDualEquiv, DGModuleEquiv.trans_apply]
  rw [show ExternalTensor.interchangeEquiv (ONH a) (ONH b) (osymDG (a + 2)) (osymDG (b + 2))
      (Zn (a + 2)) (Zn (b + 2)) (ZnDual a) (ZnDual b) (op x • t) = op x •
      ExternalTensor.interchangeEquiv (ONH a) (ONH b) (osymDG (a + 2)) (osymDG (b + 2))
        (Zn (a + 2)) (Zn (b + 2)) (ZnDual a) (ZnDual b) t from
      ExternalTensor.interchange_op_smul x t,
    ExternalTensor.tensorEquiv_op_smul _ _ (znTensorDualEquiv_op_smul a)
      (znTensorDualEquiv_op_smul b), ExternalTensor.regularEquiv_op_smul]

/-- **`J^A` on `(ONH_a ⊗ ONH_b)`-modules**: `M ↦ (Z_a^∨ ⊠ Z_b^∨) ⊗_{ONH_a ⊗ ONH_b} M` is an
equivalence `(ONH_a ⊗ ONH_b)-dmod ≌ (OΛ_a ⊗ OΛ_b)-dmod`, with quasi-inverse
`(Z_a ⊠ Z_b) ⊗_{OΛ_a ⊗ OΛ_b} (-)`. -/
def JA2 : DGModuleCat.{0} (𝒪a ᵍ⊗[ℤ] 𝒪b) ≌ DGModuleCat.{0} (Λa ᵍ⊗[ℤ] Λb) :=
  DGModuleCat.moritaEquivalence (ZZ a b) (ZZDual a b) (zzDualTensorEquiv a b)
    (zzDualTensorEquiv_op_smul a b) (zzTensorDualEquiv a b) (zzTensorDualEquiv_op_smul a b)

theorem JA2_functor :
    (JA2 a b).functor = DGModuleCat.tensorFunctor (Λa ᵍ⊗[ℤ] Λb) (ZZDual a b) := rfl

/-- `J^H` on `(ONH_a ⊗ ONH_b)`-modules. -/
def JH2 : DG.HomotopyCategory.{0} (𝒪a ᵍ⊗[ℤ] 𝒪b) ≌ DG.HomotopyCategory.{0} (Λa ᵍ⊗[ℤ] Λb) :=
  DG.HomotopyCategory.moritaEquivalence (ZZ a b) (ZZDual a b) (zzDualTensorEquiv a b)
    (zzDualTensorEquiv_op_smul a b) (zzTensorDualEquiv a b) (zzTensorDualEquiv_op_smul a b)

end OddMath.Frontier.EQFunctor
