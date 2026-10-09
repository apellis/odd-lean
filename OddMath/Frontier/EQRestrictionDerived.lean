import DG.Homotopy.RightContractible
import OddMath.Frontier.EQRestrictionFunctor

/-!
# `Res^♮ = ONH^♮ ⊗^L (-)` on derived categories

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§4.4, Definition 4.20 (`Res^♮ := ONH^♮ ⊗^L_{ONH} (-)`) and Corollary 4.21; ranks `a + 2`, `b + 2`.

The derived tensor product `M ⊗^L_B (-)` with a dg `(A, B)`-bimodule `M` (`DGBimodule.derivedTensor`) needs
`M` to be K-projective as a left dg `A`-module. For `ONH^♮_{a+b}` (`ONHNat a b`, the right ideal
`P^a ONH_{a+b}`) over `A = ONH_a ⊗ ONH_b` this holds for a simple reason:

* dg-lean (`DG.isContractible_of_d_op_smul_eq_one`): a dg `(A, B)`-bimodule `M` is contractible as a left
  dg `A`-module as soon as `B` has an element `t` of degree `-1` with `d t = 1`; the contracting
  homotopy `m ↦ (-1)^{|m|} m t` is left `A`-linear because it acts on the right;
* `ONH_{a+b}` has `d(∂_1) = 1`, so `ONH^♮_{a+b}` is contractible, hence K-projective, as a left dg
  `ONH_a ⊗ ONH_b`-module (`onhNat_isContractible`, `onhNat_isKProjective`). No resolution is needed.

With it, `ResNatD a b = ONH^♮_{a+b} ⊗^L_{ONH_{a+b}} (-) : D(ONH_{a+b}) ⥤ D(ONH_a ⊗ ONH_b)` is Definition 4.20
literally, and `resNatIsoD a b : J ∘ R ≅ Res^♮ ∘ J` is the restriction half of Corollary 4.21 on derived
categories for this functor.
-/

noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace OddMath.Frontier.EQFunctor

open OddMath.Frontier.EQSkewDifferential (osymDG)
open OddMath.Frontier.EQOnhDG (ONH)
open DG MulOpposite


/-! ### `ONH^♮` is K-projective over `ONH_a ⊗ ONH_b` -/

variable (a b : ℕ)

local notation "𝒪a" => DGAlgebra.gradingSubmodule ℤ (ONH a)
local notation "𝒪b" => DGAlgebra.gradingSubmodule ℤ (ONH b)
local notation "Λa" => DGAlgebra.gradingSubmodule ℤ (osymDG (a + 2))
local notation "Λb" => DGAlgebra.gradingSubmodule ℤ (osymDG (b + 2))

/-- `ONH^♮_{a+b}` is contractible as a left dg `ONH_a ⊗ ONH_b`-module (homotopy `m ↦ ± m ∂_1`). -/
theorem onhNat_isContractible : IsContractible (𝒪a ᵍ⊗[ℤ] 𝒪b) (ONHNat a b) :=
  isContractible_of_d_op_smul_eq_one (EQOnhDG.ONH.del_mem_grading (n := a + 2 + b) 0)
    (EQOnhDG.ONH.d_del 0)

/-- `ONH^♮_{a+b}` is K-projective as a left dg `ONH_a ⊗ ONH_b`-module. -/
theorem onhNat_isKProjective : IsKProjective.{0} (𝒪a ᵍ⊗[ℤ] 𝒪b) (ONHNat a b) :=
  (onhNat_isContractible a b).isKProjective

section Derived

universe w₁ w₂

variable
  [CatModule.HasDerivedCategory.{w₁, 0} (SingleObj (DGAlgebra.gradingSubmodule ℤ (ONH a) ᵍ⊗[ℤ]
    DGAlgebra.gradingSubmodule ℤ (ONH b)))]
  [CatModule.HasDerivedCategory.{w₁, 0} (SingleObj (ONH (a + 2 + b)))]
  [CatModule.HasDerivedCategory.{w₁, 0} (SingleObj (DGAlgebra.gradingSubmodule ℤ (osymDG (a + 2)) ᵍ⊗[ℤ]
    DGAlgebra.gradingSubmodule ℤ (osymDG (b + 2))))]
  [CatModule.HasDerivedCategory.{w₁, 0} (SingleObj (osymDG ((a + 2) + (b + 2))))]
  [DG.HasDerivedCategory.{w₂, 0} (DGAlgebra.gradingSubmodule ℤ (ONH a) ᵍ⊗[ℤ]
    DGAlgebra.gradingSubmodule ℤ (ONH b))]
  [DG.HasDerivedCategory.{w₂, 0} (ONH (a + 2 + b))]
  [DG.HasDerivedCategory.{w₂, 0} (DGAlgebra.gradingSubmodule ℤ (osymDG (a + 2)) ᵍ⊗[ℤ]
    DGAlgebra.gradingSubmodule ℤ (osymDG (b + 2)))]
  [DG.HasDerivedCategory.{w₂, 0} (osymDG ((a + 2) + (b + 2)))]

/-- **Definition 4.20**: `Res^♮ = ONH^♮_{a+b} ⊗^L_{ONH_{a+b}} (-) : D(ONH_{a+b}) ⥤ D(ONH_a ⊗ ONH_b)`. -/
abbrev ResNatD : DG.DerivedCategory.{w₂, 0} (ONH (a + 2 + b)) ⥤ DG.DerivedCategory.{w₂, 0} (𝒪a ᵍ⊗[ℤ] 𝒪b) :=
  DGBimodule.derivedTensor.{w₁, w₁, w₂, w₂} (𝒪a ᵍ⊗[ℤ] 𝒪b) (ONH (a + 2 + b)) (ONHNat a b)
    (onhNat_isKProjective a b)

/-- **Ellis–Qi, Corollary 4.21, the restriction half on derived categories**, with `Res^♮` the derived
tensor product of Definition 4.20: `R ∘ J ≅ J ∘ Res^♮`. -/
def resNatIsoD :
    (J.{w₁, w₁, w₂, w₂} (a + 2 + b) : _ ⥤ DG.DerivedCategory.{w₂, 0} (osymDG ((a + 2) + (b + 2)))) ⋙
        RD.{w₁, w₂} a b ≅
      ResNatD.{w₁, w₂} a b ⋙ J2D.{w₁, w₂} a b :=
  resIsoD a b (ResNatD a b)

end Derived

end OddMath.Frontier.EQFunctor
