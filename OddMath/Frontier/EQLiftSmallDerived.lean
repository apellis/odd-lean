import OddMath.Frontier.EQLiftSmallRank
import OddMath.Frontier.EQLiftOneOne

/-!
# Corollary 4.21 on derived categories in ranks `a + b ≤ 1`

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2, §4.4, Corollary 4.21
("the same is true of `J` on derived categories"), for `(a, b) ∈ {(0,0), (0,1), (1,0)}`.

Every bimodule involved is a ring through a morphism of dg rings, so every functor is a derived induction:

* `jDAllIsoChi`: `J = Z^∨ ⊗^L (-) ≅ χ^*` (`χ = chiE : ONH_{a+b} → OΛ_{a+b}`, `e 1_z = 1_z χ(e)`);
* `j2DAllIsoChi`: `J = (Z_a^∨ ⊠ Z_b^∨) ⊗^L (-) ≅ (χ_a ⊗ χ_b)^*`;
* `iDAllIsoPsi`: `I = Z_{a,b}^∨ ⊗^L (-) ≅ ψ^*` (`ψ(f ⊗ g) = f(x) g(y)`);
* **`indIsoDAllSmall`**: `J ∘ Ind ≅ I ∘ J`, from `χ ∘ ι = ψ ∘ (χ_a ⊗ χ_b)` (`chiE_comp_gIota`);
* `ONH^♮` is free of rank one over `ONH_a ⊗ ONH_b` (`P^A = 1`, `ι` bijective), so K-projective
  (`onhNatAll_isKProjective_small`), and `Res^♮ = ONH^♮ ⊗^L (-) ≅ (ι⁻¹)^*` (`resNatDAllSmallIso`);
* **`resNatIsoDAllSmall`**: `R ∘ J ≅ J ∘ Res^♮`, from `swap ∘ χ = (χ_a ⊗ χ_b) ∘ ι⁻¹` (`swapDGG_comp_chiE`).

With the cases `a + b ≥ 2` (`EQLiftDerived`) and `a = b = 1` (`EQLiftOneOne`): **`resNatIsoDAny`** and
**`indIsoDAny`**, both halves of Corollary 4.21 on derived categories for all `a`, `b`, with
`Res^♮ = ONH^♮ ⊗^L (-)` (`ResNatDAllAny`; `ONH^♮` is K-projective in every rank, `onhNatAll_isKProjective_all`).
-/

noncomputable section

set_option linter.unusedSectionVars false

open CategoryTheory

namespace OddMath.Frontier.EQLift

open OddMath.Frontier.EQSkewDifferential (osymDG Zn)
open OddMath.Frontier.EQK0Int (ONHAll ONHTensor)
open OddMath.Frontier.EQFunctor
open DG MulOpposite

universe w₂

variable (a b : ℕ)
  [CatModule.HasDerivedCategory.{0, 0} (SingleObj (ONHTensor a b))]
  [CatModule.HasDerivedCategory.{0, 0} (SingleObj (ONHAll (a + b)))]
  [CatModule.HasDerivedCategory.{0, 0} (SingleObj (LABg a b))]
  [CatModule.HasDerivedCategory.{0, 0} (SingleObj (osymDG (a + b)))]
  [DG.HasDerivedCategory.{w₂, 0} (ONHTensor a b)] [DG.HasDerivedCategory.{w₂, 0} (ONHAll (a + b))]
  [DG.HasDerivedCategory.{w₂, 0} (LABg a b)] [DG.HasDerivedCategory.{w₂, 0} (osymDG (a + b))]

section Small

variable (hAB : a + b ≤ 1)
include hAB

/-- `J ≅ χ^*` for `a + b ≤ 1`. -/
def jDAllIsoChi : JDAll.{0, w₂} a b ≅ (chiE hAB (ONHAll (a + b))).derivedInduction.{0, 0, w₂, w₂} :=
  DGBimodule.derivedTensorIsoInduction (chiE hAB (ONHAll (a + b))) (znDual_isKProjective (a + b)) (znDualEquiv hAB)
    (znDualEquiv_mem_iff hAB) (znDualEquiv_d hAB) (znDualEquiv_smul hAB) (znDualEquiv_op_smul_chiE hAB _)

/-- `J ≅ (χ_a ⊗ χ_b)^*` on `D(ONH_a ⊗ ONH_b)` for `a + b ≤ 1`. -/
def j2DAllIsoChi :
    J2DAll.{0, w₂} a b ≅
      (tChi (A := a) (B := b) (by omega) (by omega) (ONHAll a) (ONHAll b)).derivedInduction.{0, 0, w₂, w₂} :=
  DGBimodule.derivedTensorIsoInduction _ _ (zzDualEquivSmall (by omega) (by omega))
    (zzDualEquivSmall_mem_iff _ _) (zzDualEquivSmall_d _ _) (zzDualEquivSmall_smul _ _)
    (zzDualEquivSmall_op_smul _ _ (ONHAll a) (ONHAll b))

/-- `I ≅ ψ^*` for `a + b ≤ 1`. -/
def iDAllIsoPsi : IDAll.{0, w₂} a b ≅ (psiSmall hAB).derivedInduction.{0, 0, w₂, w₂} :=
  DGBimodule.derivedTensorIsoInduction (psiSmall hAB) _ (zabDualEquivSmall hAB) (zabDualEquivSmall_mem_iff hAB)
    (zabDualEquivSmall_d hAB) (zabDualEquivSmall_smul hAB) (zabDualEquivSmall_op_smul hAB)

theorem chiE_comp_iotaAll :
    (chiE hAB (ONHAll (a + b))).comp (iotaAll a b) =
      (psiSmall hAB).comp (tChi (A := a) (B := b) (by omega) (by omega) (ONHAll a) (ONHAll b)) :=
  chiE_comp_gIota (by omega) (by omega) hAB (fullActionAll (a + b))

/-- **Ellis–Qi, Corollary 4.21, the induction half on derived categories for `a + b ≤ 1`**: `J ∘ Ind ≅ I ∘ J` on
`D(ONH_a ⊗ ONH_b)`. -/
def indIsoDAllSmall :
    IndDAll.{0, w₂} a b ⋙ JDAll.{0, w₂} a b ≅ J2DAll.{0, w₂} a b ⋙ IDAll.{0, w₂} a b :=
  Functor.isoWhiskerLeft _ (jDAllIsoChi a b hAB) ≪≫
    (DGRingHom.derivedInductionCompIso (iotaAll a b) (chiE hAB (ONHAll (a + b)))).symm ≪≫
    eqToIso (congrArg (fun φ => DGRingHom.derivedInduction.{0, 0, w₂, w₂} φ) (chiE_comp_iotaAll a b hAB)) ≪≫
    DGRingHom.derivedInductionCompIso _ (psiSmall hAB) ≪≫
    Functor.isoWhiskerRight (j2DAllIsoChi a b hAB).symm _ ≪≫
    Functor.isoWhiskerLeft _ (iDAllIsoPsi a b hAB).symm

/-! ### The restriction half -/

/-- `ι⁻¹ : ONH_{a+b} → ONH_a ⊗ ONH_b` for `a + b ≤ 1`. -/
abbrev iotaInvAll : ONHAll (a + b) →ᵈᵍ+* ONHTensor a b :=
  gIotaInv (A := a) (B := b) (by omega) (by omega) hAB (fullActionAll a) (fullActionAll b) (fullActionAll (a + b))

/-- For `a + b ≤ 1`, `ONH^♮_{a+b}` is free of rank one, hence K-projective, as a left `ONH_a ⊗ ONH_b`-module. -/
theorem onhNatAll_isKProjective_small : IsKProjective.{0} (ONHTensor a b) (ONHNatAll a b) :=
  onhNatG_isKProjective_small (A := a) (B := b) (by omega) (by omega) hAB (fullActionAll a) (fullActionAll b)
    (fullActionAll (a + b))

/-- **Definition 4.20** for `a + b ≤ 1`: `Res^♮ = ONH^♮ ⊗^L (-)`. -/
abbrev ResNatDAllSmall :
    DG.DerivedCategory.{w₂, 0} (ONHAll (a + b)) ⥤ DG.DerivedCategory.{w₂, 0} (ONHTensor a b) :=
  DGBimodule.derivedTensor.{0, 0, w₂, w₂} (ONHTensor a b) (ONHAll (a + b)) (ONHNatAll a b)
    (onhNatAll_isKProjective_small a b hAB)

/-- `Res^♮ ≅ (ι⁻¹)^*` for `a + b ≤ 1`. -/
def resNatDAllSmallIso : ResNatDAllSmall.{w₂} a b hAB ≅ (iotaInvAll a b hAB).derivedInduction.{0, 0, w₂, w₂} :=
  DGBimodule.derivedTensorIsoInduction (iotaInvAll a b hAB) _ (natEquivSmall _ _ _ _ _ _) (natEquivSmall_mem_iff _ _ _ _ _ _)
    (natEquivSmall_d _ _ _ _ _ _) (natEquivSmall_smul _ _ _ _ _ _) (natEquivSmall_op_smul _ _ _ _ _ _)

/-- **Ellis–Qi, Corollary 4.21, the restriction half on derived categories for `a + b ≤ 1`**: `R ∘ J ≅ J ∘ Res^♮`
on `D(ONH_{a+b})`, from `swap ∘ χ = (χ_a ⊗ χ_b) ∘ ι⁻¹` (`swapDGG_comp_chiE`). -/
def resNatIsoDAllSmall :
    JDAll.{0, w₂} a b ⋙ RDAll.{0, w₂} a b ≅ ResNatDAllSmall.{w₂} a b hAB ⋙ J2DAll.{0, w₂} a b :=
  Functor.isoWhiskerRight (jDAllIsoChi a b hAB) _ ≪≫
    (DGRingHom.derivedInductionCompIso (chiE hAB (ONHAll (a + b))) (swapDGG a b)).symm ≪≫
    eqToIso (congrArg (fun φ => DGRingHom.derivedInduction.{0, 0, w₂, w₂} φ)
      (swapDGG_comp_chiE (A := a) (B := b) (by omega) (by omega) hAB (fullActionAll a) (fullActionAll b)
        (fullActionAll (a + b)))) ≪≫
    DGRingHom.derivedInductionCompIso (iotaInvAll a b hAB) _ ≪≫
    Functor.isoWhiskerRight (resNatDAllSmallIso a b hAB).symm _ ≪≫
    Functor.isoWhiskerLeft _ (j2DAllIsoChi a b hAB).symm

end Small

/-! ### All ranks -/

/-- `ONH^♮_{a+b}` is K-projective over `ONH_a ⊗ ONH_b` for all `a`, `b`: contractible for `a + b ≥ 2`, free of rank
one for `a + b ≤ 1`. -/
theorem onhNatAll_isKProjective_all : IsKProjective.{0} (ONHTensor a b) (ONHNatAll a b) := by
  by_cases h : 2 ≤ a + b
  · exact onhNatAll_isKProjective a b h
  · exact onhNatAll_isKProjective_small a b (by omega)

/-- **Definition 4.20** in all ranks: `Res^♮ = ONH^♮ ⊗^L (-) : D(ONH_{a+b}) → D(ONH_a ⊗ ONH_b)`. -/
abbrev ResNatDAllAny :
    DG.DerivedCategory.{w₂, 0} (ONHAll (a + b)) ⥤ DG.DerivedCategory.{w₂, 0} (ONHTensor a b) :=
  DGBimodule.derivedTensor.{0, 0, w₂, w₂} (ONHTensor a b) (ONHAll (a + b)) (ONHNatAll a b)
    (onhNatAll_isKProjective_all a b)

/-- **Ellis–Qi, Corollary 4.21, the restriction half on derived categories, all `a`, `b`**:
`R ∘ J ≅ J ∘ Res^♮` on `D(ONH_{a+b})`. -/
def resNatIsoDAny : JDAll.{0, w₂} a b ⋙ RDAll.{0, w₂} a b ≅ ResNatDAllAny.{w₂} a b ⋙ J2DAll.{0, w₂} a b :=
  if h : 2 ≤ a + b then resNatIsoDAll a b h else resNatIsoDAllSmall a b (by omega)

/-- **Ellis–Qi, Corollary 4.21, the induction half on derived categories, all `a`, `b`**:
`J ∘ Ind ≅ I ∘ J` on `D(ONH_a ⊗ ONH_b)`. -/
def indIsoDAny : IndDAll.{0, w₂} a b ⋙ JDAll.{0, w₂} a b ≅ J2DAll.{0, w₂} a b ⋙ IDAll.{0, w₂} a b :=
  if h : 2 ≤ a ∨ 2 ≤ b then indIsoDAll_of_two a b h
  else if h' : a + b ≤ 1 then indIsoDAllSmall a b h'
  else by
    obtain ⟨rfl, rfl⟩ : a = 1 ∧ b = 1 := by omega
    exact indIsoDOneOne

end OddMath.Frontier.EQLift
