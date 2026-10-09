import OddMath.Frontier.EQInductionBimodule
import OddMath.Frontier.EQZabEndRankOne
import DG.Homotopy.DualAdjunction
import OddMath.Frontier.EQFunctorEmbedding
import OddMath.Frontier.EQOnhDGAcyclic
import DG.Homotopy.ExternalTensorKProjective

/-!
# The induction half of Ellis–Qi, Corollary 4.21

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§4.4, Corollary 4.21 ("`J^A` intertwines `I` with `Ind`"), on the components `ONH_a ⊗ ONH_b`,
ranks `a + 2`, `b + 2`:

* `IndA a b : (ONH_a ⊗ ONH_b)-dmod ⥤ ONH_{a+b}-dmod`, `M ↦ ONH_{a+b} ⊗_{ONH_a ⊗ ONH_b} M` (extension of
  scalars along `ι = ONH.iota a b`, `IndA_eq_extendScalars`);
* `IA a b : (OΛ_a ⊗ OΛ_b)-dmod ⥤ OΛ_{a+b}-dmod`, `M ↦ Z_{a,b}^∨ ⊗_{OΛ_a ⊗ OΛ_b} M` with
  `Z_{a,b}^∨ = HOM_{OΛ_{a+b}}(Z_{a,b}, OΛ_{a+b})` (Definition 4.14, underived) for `Z_{a,b}` with the left
  action of `OΛ_a ⊗ OΛ_b` through `θ ∘ w₀` (`ZabTw`, see ERRATA [EQ] 23);
* **`indIsoA a b : IndA a b ⋙ (JA _).functor ≅ (JA2 a b).functor ⋙ IA a b`**: the induction half of
  Corollary 4.21 on abelian categories, from the adjunctions `Ind ⊣ Res`, `I ⊣ Z_{a,b} ⊗_{OΛ_{a+b}} (-)`
  (`RightBasis.dualAdjunction`) and the isomorphism of right adjoints
  `Res ∘ (J^A)^{-1} ≅ (J^A_2)^{-1} ∘ (Z_{a,b} ⊗ -)` given by `indEquiv`;
* `indIsoH a b`: the same on homotopy categories.
-/

noncomputable section

set_option linter.unusedSectionVars false

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

/-! ### The functors -/

/-- `Ind`: `M ↦ ONH_{a+b} ⊗_{ONH_a ⊗ ONH_b} M` along `ι`. -/
abbrev IndA : DGModuleCat.{0} (𝒪a ᵍ⊗[ℤ] 𝒪b) ⥤ DGModuleCat.{0} (ONH (a + 2 + b)) :=
  DGModuleCat.tensorFunctor (ONH (a + 2 + b)) (ONH.iota a b).Bimodule

theorem IndA_eq_extendScalars : IndA a b = DGModuleCat.extendScalars.{0} (ONH.iota a b) := rfl

/-- The right basis of `Z_{a,b}` (Corollary 4.8), for the twisted left action. -/
def zabTwRightBasis : RightBasis (osymDG ((a + 2) + (b + 2))) (ZabTw a b) (EQFix.ParIdx (a + 2) (b + 2)) :=
  zabRightBasis (a + 2) (b + 2)

/-- `Z_{a,b}^∨ = HOM_{OΛ_{a+b}}(Z_{a,b}, OΛ_{a+b})` for the twisted left action. -/
abbrev ZabTwDual : Type := RightDual (osymDG ((a + 2) + (b + 2))) (ZabTw a b)

/-- **Definition 4.14** (underived): `I(M) = Z_{a,b}^∨ ⊗_{OΛ_a ⊗ OΛ_b} M`. -/
abbrev IA : DGModuleCat.{0} (Λa ᵍ⊗[ℤ] Λb) ⥤ DGModuleCat.{0} (osymDG ((a + 2) + (b + 2))) :=
  DGModuleCat.tensorFunctor (osymDG ((a + 2) + (b + 2))) (ZabTwDual a b)

/-! ### Right adjoints -/

section ResTensor

variable (Y : Type) [AddCommGroup Y] [DGAddCommGroup Y] [Module (osymDG ((a + 2) + (b + 2))) Y]
  [DGModule (osymDG ((a + 2) + (b + 2))) Y]

/-- `ι^* (Z_{a+b} ⊗ Y)`. -/
abbrev ResT : Type := RestrictScalars (ONH.iota a b)
  (TensorProductOver (osymDG ((a + 2) + (b + 2))) (Zn ((a + 2) + (b + 2))) Y)

/-- `(ι^* Z_{a+b}) ⊗ Y`. -/
abbrev IZT : Type := TensorProductOver (osymDG ((a + 2) + (b + 2))) (IZ a b) Y

/-- The identity of underlying groups `(ι^* Z) ⊗ Y → ι^* (Z ⊗ Y)`. -/
def izt : IZT a b Y →+ ResT a b Y := AddMonoidHom.id _

theorem izt_smul (s : 𝒪a ᵍ⊗[ℤ] 𝒪b) (t : IZT a b Y) : izt a b Y (s • t) = s • izt a b Y t := by
  have h : (izt a b Y).comp (DistribSMul.toAddMonoidHom (IZT a b Y) s) =
      (DistribSMul.toAddMonoidHom (ResT a b Y) s).comp (izt a b Y) :=
    TensorProductOver.addHom_ext fun _ _ => rfl
  exact DFunLike.congr_fun h t

/-- `ι^* (Z_{a+b} ⊗ Y) = (ι^* Z_{a+b}) ⊗ Y`. -/
def resTensorEquiv : IZT a b Y ≃ᵈᵍ[𝒪a ᵍ⊗[ℤ] 𝒪b] ResT a b Y where
  toFun := izt a b Y
  invFun t := t
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' := map_add _
  map_smul' s t := izt_smul a b Y s t
  map_mem' h := h
  map_d' _ := rfl

end ResTensor

theorem indEquiv_symm_op_smul (h : osymDG ((a + 2) + (b + 2))) (t : IZ a b) :
    (indEquiv a b).symm (op h • t) = op h • (indEquiv a b).symm t := by
  apply (indEquiv a b).injective
  rw [indEquiv_op_smul, DGModuleEquiv.apply_symm_apply, DGModuleEquiv.apply_symm_apply]

/-- `ι^* (Z_{a+b} ⊗ -) ≅ (ι^* Z_{a+b}) ⊗ -`. -/
def resIso1 :
    ((JA (a + 2 + b)).inverse : DGModuleCat.{0} (osymDG ((a + 2) + (b + 2))) ⥤ _) ⋙
        DGModuleCat.restrictScalars.{0} (ONH.iota a b) ≅
      DGModuleCat.tensorFunctor (B := osymDG ((a + 2) + (b + 2))) (𝒪a ᵍ⊗[ℤ] 𝒪b) (IZ a b) :=
  NatIso.ofComponents (fun Y => (DGModuleCat.isoOfDGModuleEquiv (resTensorEquiv a b Y)).symm)
    (fun _ => DGModuleCat.hom_ext_apply fun _ => rfl)

/-- `(ι^* Z_{a+b}) ⊗ - ≅ ((Z_a ⊠ Z_b) ⊗ Z_{a,b}) ⊗ -`. -/
def resIso2 :
    DGModuleCat.tensorFunctor (B := osymDG ((a + 2) + (b + 2))) (𝒪a ᵍ⊗[ℤ] 𝒪b) (IZ a b) ≅
      DGModuleCat.tensorFunctor (B := osymDG ((a + 2) + (b + 2))) (𝒪a ᵍ⊗[ℤ] 𝒪b)
        (TensorProductOver (Λa ᵍ⊗[ℤ] Λb) (ZZ a b) (ZabTw a b)) :=
  DGModuleCat.tensorFunctorIsoOfEquiv (indEquiv a b).symm (indEquiv_symm_op_smul a b)

/-- `Res ∘ (Z_{a+b} ⊗ -) ≅ (Z_a ⊠ Z_b) ⊗ (Z_{a,b} ⊗ -)`, from `indEquiv`. -/
def rightAdjIso :
    ((JA (a + 2 + b)).inverse : DGModuleCat.{0} (osymDG ((a + 2) + (b + 2))) ⥤ _) ⋙
        DGModuleCat.restrictScalars.{0} (ONH.iota a b) ≅
      DGModuleCat.tensorFunctor (B := osymDG ((a + 2) + (b + 2))) (Λa ᵍ⊗[ℤ] Λb) (ZabTw a b) ⋙
        (JA2 a b).inverse :=
  resIso1 a b ≪≫ resIso2 a b ≪≫ (DGModuleCat.tensorFunctorCompIso (ZabTw a b) (ZZ a b)).symm

/-! ### The induction half on abelian categories -/

/-- `Ind ⊣ Res` along `ι`. -/
def adjInd : IndA a b ⊣ DGModuleCat.restrictScalars.{0} (ONH.iota a b) :=
  DGModuleCat.extendRestrictScalarsAdj.{0} (ONH.iota a b)

/-- `J^A ∘ Ind ⊣ Res ∘ (J^A)^{-1}`. -/
def adjL1 :
    IndA a b ⋙ ((JA (a + 2 + b)).functor : _ ⥤ DGModuleCat.{0} (osymDG ((a + 2) + (b + 2)))) ⊣
      ((JA (a + 2 + b)).inverse : DGModuleCat.{0} (osymDG ((a + 2) + (b + 2))) ⥤ _) ⋙
        DGModuleCat.restrictScalars.{0} (ONH.iota a b) :=
  (adjInd a b).comp (JA (a + 2 + b)).toAdjunction

/-- `I ∘ J^A_2 ⊣ (J^A_2)^{-1} ∘ (Z_{a,b} ⊗ -)`. -/
def adjL2 :
    (JA2 a b).functor ⋙ IA a b ⊣
      DGModuleCat.tensorFunctor (B := osymDG ((a + 2) + (b + 2))) (Λa ᵍ⊗[ℤ] Λb) (ZabTw a b) ⋙
        (JA2 a b).inverse :=
  (JA2 a b).toAdjunction.comp (RightBasis.dualAdjunction (E := Λa ᵍ⊗[ℤ] Λb) (zabTwRightBasis a b))

/-- **Ellis–Qi, Corollary 4.21, the induction half on abelian categories** (components
`ONH_{a+2} ⊗ ONH_{b+2}`): `J^A ∘ Ind ≅ I ∘ J^A`, with `I = Z_{a,b}^∨ ⊗ (-)` for the twisted left action
of `OΛ_a ⊗ OΛ_b` on `Z_{a,b}` (ERRATA [EQ] 23). -/
def indIsoA :
    IndA a b ⋙ ((JA (a + 2 + b)).functor : _ ⥤ DGModuleCat.{0} (osymDG ((a + 2) + (b + 2)))) ≅
      (JA2 a b).functor ⋙ IA a b :=
  (adjL1 a b).leftAdjointUniq ((adjL2 a b).ofNatIsoRight (rightAdjIso a b).symm)

/-! ### The induction half on homotopy categories -/

open HomotopyCategory in
/-- `Ind` on homotopy categories. -/
abbrev IndH : DG.HomotopyCategory.{0} (𝒪a ᵍ⊗[ℤ] 𝒪b) ⥤ DG.HomotopyCategory.{0} (ONH (a + 2 + b)) :=
  HomotopyCategory.tensorFunctor (ONH (a + 2 + b)) (ONH.iota a b).Bimodule

/-- `I` on homotopy categories. -/
abbrev IH : DG.HomotopyCategory.{0} (Λa ᵍ⊗[ℤ] Λb) ⥤ DG.HomotopyCategory.{0} (osymDG ((a + 2) + (b + 2))) :=
  HomotopyCategory.tensorFunctor (osymDG ((a + 2) + (b + 2))) (ZabTwDual a b)

/-- **Ellis–Qi, Corollary 4.21, the induction half on homotopy categories**: `J^H ∘ Ind ≅ I ∘ J^H`. -/
def indIsoH :
    IndH a b ⋙ ((JH (a + 2 + b)).functor : _ ⥤ DG.HomotopyCategory.{0} (osymDG ((a + 2) + (b + 2)))) ≅
      (JH2 a b).functor ⋙ IH a b :=
  HomotopyCategory.liftFunctorCompIso _ _ (HomotopyCategory.tensorFunctor_homotopic _ _)
      (HomotopyCategory.tensorFunctor_homotopic _ _) ≪≫
    HomotopyCategory.liftNatIso _ _ (indIsoA a b) ≪≫
    (HomotopyCategory.liftFunctorCompIso _ _ (HomotopyCategory.tensorFunctor_homotopic _ _)
      (HomotopyCategory.tensorFunctor_homotopic _ _)).symm

/-! ### Derived categories -/

section Derived

universe w₁ w₂

/-- `ONH_a ⊗ ONH_b` is acyclic: `d(∂_1 ⊗ 1) = 1`. -/
theorem onhTensor_isAcyclic_module (M : Type*) [AddCommGroup M] [DGAddCommGroup M]
    [Module (𝒪a ᵍ⊗[ℤ] 𝒪b) M] [DGModule (𝒪a ᵍ⊗[ℤ] 𝒪b) M] : IsAcyclic M := by
  refine EQOnhDG.isAcyclic_of_d_eq_one (h := ((ONH.del 0 : ONH a) ᵍ⊗ₜ[ℤ] (1 : ONH b) : 𝒪a ᵍ⊗[ℤ] 𝒪b)) ?_ ?_ M
  · have := GradedTensorProduct.tmul_mem_grading (R := ℤ)
      (EQOnhDG.ONH.del_mem_grading (n := a) 0) (DG.one_mem_grading (A := ONH b))
    rwa [add_zero] at this
  · rw [GradedTensorProduct.d_tmul (EQOnhDG.ONH.del_mem_grading (n := a) 0), EQOnhDG.ONH.d_del, d_one,
      GradedTensorProduct.tmul_zero, smul_zero, add_zero]
    rfl

theorem onhTensor_isZero_derivedCategory [DG.HasDerivedCategory.{w₂, 0} (𝒪a ᵍ⊗[ℤ] 𝒪b)]
    (X : DG.DerivedCategory.{w₂, 0} (𝒪a ᵍ⊗[ℤ] 𝒪b)) : Limits.IsZero X := by
  have := Localization.essSurj (DG.DerivedCategory.Q (A := 𝒪a ᵍ⊗[ℤ] 𝒪b))
    (DG.DGModuleCat.quasiIso (𝒪a ᵍ⊗[ℤ] 𝒪b))
  exact ((DG.DerivedCategory.isZero_Q_obj_iff _).mpr (onhTensor_isAcyclic_module a b _)).of_iso
    (DG.DerivedCategory.Q.objObjPreimageIso X).symm

/-- `Z_a^∨ ⊠ Z_b^∨` is K-projective over `OΛ_a ⊗ OΛ_b`. -/
theorem zzDual_isKProjective : IsKProjective.{0} (Λa ᵍ⊗[ℤ] Λb) (ZZDual a b) :=
  ExternalTensor.isKProjective (znDual_isKProjective (a + 2)) (znDual_isKProjective (b + 2))

/-- `Z_{a,b}^∨` is K-projective over `OΛ_{a+b}` (Corollary 4.11). -/
theorem zabTwDual_isKProjective : IsKProjective.{0} (osymDG ((a + 2) + (b + 2))) (ZabTwDual a b) :=
  zdual_isKProjective (a := a + 2) (b := b + 2)

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

/-- `J` on `(ONH_a ⊗ ONH_b)`-modules: `(Z_a^∨ ⊠ Z_b^∨) ⊗^L_{ONH_a ⊗ ONH_b} (-)`. -/
abbrev J2D : DG.DerivedCategory.{w₂, 0} (𝒪a ᵍ⊗[ℤ] 𝒪b) ⥤ DG.DerivedCategory.{w₂, 0} (Λa ᵍ⊗[ℤ] Λb) :=
  DGBimodule.derivedTensor.{w₁, w₁, w₂, w₂} (Λa ᵍ⊗[ℤ] Λb) (𝒪a ᵍ⊗[ℤ] 𝒪b) (ZZDual a b) (zzDual_isKProjective a b)

/-- **Definition 4.14**: `I = Z_{a,b}^∨ ⊗^L_{OΛ_a ⊗ OΛ_b} (-)` (twisted left action, ERRATA [EQ] 23). -/
abbrev ID : DG.DerivedCategory.{w₂, 0} (Λa ᵍ⊗[ℤ] Λb) ⥤ DG.DerivedCategory.{w₂, 0} (osymDG ((a + 2) + (b + 2))) :=
  DGBimodule.derivedTensor.{w₁, w₁, w₂, w₂} (osymDG ((a + 2) + (b + 2))) (Λa ᵍ⊗[ℤ] Λb) (ZabTwDual a b)
    (zabTwDual_isKProjective a b)

/-- **Ellis–Qi, Corollary 4.21, the induction half on derived categories**: `J ∘ Ind ≅ I ∘ J` on
`D(ONH_a ⊗ ONH_b)`, which is zero (`onhTensor_isZero_derivedCategory`). -/
def indIsoD :
    (ONH.iota a b).derivedInduction.{w₁, w₁, w₂, w₂} ⋙
        (J.{w₁, w₁, w₂, w₂} (a + 2 + b) : _ ⥤ DG.DerivedCategory.{w₂, 0} (osymDG ((a + 2) + (b + 2)))) ≅
      J2D a b ⋙ ID a b :=
  NatIso.ofComponents (fun X =>
    (((J (a + 2 + b)).map_isZero (EQOnhDG.ONH.isZero_derivedCategory _))).iso
      ((ID a b).map_isZero ((J2D a b).map_isZero (onhTensor_isZero_derivedCategory a b X))))
    (fun _ => ((ID a b).map_isZero ((J2D a b).map_isZero
      (onhTensor_isZero_derivedCategory a b _))).eq_of_tgt _ _)

end Derived

end OddMath.Frontier.EQFunctor
