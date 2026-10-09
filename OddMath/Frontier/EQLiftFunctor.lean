import OddMath.Frontier.EQLiftInduction
import OddMath.Frontier.EQInductionFunctor

/-!
# The induction half of Corollary 4.21 in all ranks (abelian and homotopy categories)

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§4.4, (4.30)–(4.31) and Corollary 4.21 ("`J^A` intertwines `I` with `Ind`"), for dg rings `E_A`, `E_B`,
`E_{A+B}` acting fully on `Z_A`, `Z_B`, `Z_{A+B}` (`DG.FullAction`; `E_N = ONH_N` in every rank).

* `JAg H : E-dmod ≌ OΛ_N-dmod`, `M ↦ Z_N^∨ ⊗_E M` (the Morita equivalence (4.30) of a full action), `JHg H` on
  homotopy categories; `JA2g HA HB` on `(E_A ⊗ E_B)`-modules, `M ↦ (Z_A^∨ ⊠ Z_B^∨) ⊗ M`, and `JH2g`;
* `IndAg`: extension of scalars along `ι = gIota` (`EQLiftInduction`); `IAg`: `M ↦ Z_{A,B}^∨ ⊗ M`;
* **`indIsoAg : Ind ⋙ J^A ≅ J^A ⋙ I`** and **`indIsoHg`** (homotopy categories), from `gIndEquiv`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open CategoryTheory
open scoped TensorProduct

namespace OddMath.Frontier.EQLift

open OddMath.Frontier.EQSkewDifferential (osymDG Zn)
open OddMath.Frontier.EQFunctor
open DG MulOpposite TensorProductOver.RightAction

/-! ### Morita equivalences of full actions -/

section Morita

variable {N : ℕ} {E : Type} [Ring E] [DGAddCommGroup E] [DGRing E] [Module E (Zn N)]
  [DGBimodule E (osymDG N) (Zn N)] (H : FullAction E (osymDG N) (Zn N))

/-- **(4.30)** for a full action: `J^A : E-dmod ≌ OΛ_N-dmod`, `M ↦ Z_N^∨ ⊗_E M`, quasi-inverse `Z_N ⊗_{OΛ_N} -`. -/
def JAg : DGModuleCat.{0} E ≌ DGModuleCat.{0} (osymDG N) :=
  DGModuleCat.moritaEquivalence (Zn N) (RightDual (osymDG N) (Zn N)) (H.evEquiv (znRightBasis N))
    (fun c t => H.evEquiv_op_smul _ c t) (H.mulEquiv (znRightBasis N)) (fun p t => H.mulEquiv_op_smul _ p t)

theorem JAg_functor : (JAg H).functor = DGModuleCat.tensorFunctor (osymDG N) (RightDual (osymDG N) (Zn N)) :=
  rfl

theorem JAg_inverse : (JAg H).inverse = DGModuleCat.tensorFunctor E (Zn N) := rfl

/-- `J^H : H(E) ≌ H(OΛ_N)`. -/
def JHg : DG.HomotopyCategory.{0} E ≌ DG.HomotopyCategory.{0} (osymDG N) :=
  DG.HomotopyCategory.moritaEquivalence (Zn N) (RightDual (osymDG N) (Zn N)) (H.evEquiv (znRightBasis N))
    (fun c t => H.evEquiv_op_smul _ c t) (H.mulEquiv (znRightBasis N)) (fun p t => H.mulEquiv_op_smul _ p t)

end Morita

section Morita2

variable {A B : ℕ} {EA EB : Type} [Ring EA] [DGAddCommGroup EA] [DGRing EA] [Module EA (Zn A)]
  [DGBimodule EA (osymDG A) (Zn A)] [Ring EB] [DGAddCommGroup EB] [DGRing EB] [Module EB (Zn B)]
  [DGBimodule EB (osymDG B) (Zn B)] (HA : FullAction EA (osymDG A) (Zn A))
  (HB : FullAction EB (osymDG B) (Zn B))

variable (A B) in
/-- `OΛ_A ⊗ OΛ_B`. -/
abbrev LABg : Type := DGAlgebra.gradingSubmodule ℤ (osymDG A) ᵍ⊗[ℤ] DGAlgebra.gradingSubmodule ℤ (osymDG B)

variable (A B) in
/-- `Z_A^∨ ⊠ Z_B^∨`. -/
abbrev ZZDualg : Type := RightDual (osymDG A) (Zn A) ⊗[ℤ] RightDual (osymDG B) (Zn B)

/-- `(Z_A^∨ ⊠ Z_B^∨) ⊗_{E_A ⊗ E_B} (Z_A ⊠ Z_B) ≅ OΛ_A ⊗ OΛ_B`. -/
def zzDualTensorEquivg : TensorProductOver (EAB EA EB) (ZZDualg A B) (ZZg A B) ≃ᵈᵍ[LABg A B] LABg A B :=
  ((ExternalTensor.interchangeEquiv (osymDG A) (osymDG B) EA EB (RightDual (osymDG A) (Zn A))
      (RightDual (osymDG B) (Zn B)) (Zn A) (Zn B)).trans
    (ExternalTensor.tensorEquiv (HA.evEquiv (znRightBasis A)) (HB.evEquiv (znRightBasis B)))).trans
    (ExternalTensor.regularEquiv (osymDG A) (osymDG B))

theorem zzDualTensorEquivg_op_smul (x : LABg A B) (t : TensorProductOver (EAB EA EB) (ZZDualg A B) (ZZg A B)) :
    zzDualTensorEquivg HA HB (op x • t) = op x • zzDualTensorEquivg HA HB t := by
  simp only [zzDualTensorEquivg, DGModuleEquiv.trans_apply]
  rw [show ExternalTensor.interchangeEquiv (osymDG A) (osymDG B) EA EB (RightDual (osymDG A) (Zn A))
      (RightDual (osymDG B) (Zn B)) (Zn A) (Zn B) (op x • t) = op x •
      ExternalTensor.interchangeEquiv (osymDG A) (osymDG B) EA EB (RightDual (osymDG A) (Zn A))
        (RightDual (osymDG B) (Zn B)) (Zn A) (Zn B) t from ExternalTensor.interchange_op_smul x t,
    ExternalTensor.tensorEquiv_op_smul _ _ (fun c t => HA.evEquiv_op_smul _ c t)
      (fun c t => HB.evEquiv_op_smul _ c t), ExternalTensor.regularEquiv_op_smul]

/-- `(Z_A ⊠ Z_B) ⊗_{OΛ_A ⊗ OΛ_B} (Z_A^∨ ⊠ Z_B^∨) ≅ E_A ⊗ E_B`. -/
def zzTensorDualEquivg : TensorProductOver (LABg A B) (ZZg A B) (ZZDualg A B) ≃ᵈᵍ[EAB EA EB] EAB EA EB :=
  ((ExternalTensor.interchangeEquiv EA EB (osymDG A) (osymDG B) (Zn A) (Zn B) (RightDual (osymDG A) (Zn A))
      (RightDual (osymDG B) (Zn B))).trans
    (ExternalTensor.tensorEquiv (HA.mulEquiv (znRightBasis A)) (HB.mulEquiv (znRightBasis B)))).trans
    (ExternalTensor.regularEquiv EA EB)

theorem zzTensorDualEquivg_op_smul (x : EAB EA EB) (t : TensorProductOver (LABg A B) (ZZg A B) (ZZDualg A B)) :
    zzTensorDualEquivg HA HB (op x • t) = op x • zzTensorDualEquivg HA HB t := by
  simp only [zzTensorDualEquivg, DGModuleEquiv.trans_apply]
  rw [show ExternalTensor.interchangeEquiv EA EB (osymDG A) (osymDG B) (Zn A) (Zn B)
      (RightDual (osymDG A) (Zn A)) (RightDual (osymDG B) (Zn B)) (op x • t) = op x •
      ExternalTensor.interchangeEquiv EA EB (osymDG A) (osymDG B) (Zn A) (Zn B)
        (RightDual (osymDG A) (Zn A)) (RightDual (osymDG B) (Zn B)) t from
      ExternalTensor.interchange_op_smul x t,
    ExternalTensor.tensorEquiv_op_smul _ _ (fun p t => HA.mulEquiv_op_smul _ p t)
      (fun p t => HB.mulEquiv_op_smul _ p t), ExternalTensor.regularEquiv_op_smul]

/-- `J^A` on `(E_A ⊗ E_B)`-modules: `M ↦ (Z_A^∨ ⊠ Z_B^∨) ⊗ M`. -/
def JA2g : DGModuleCat.{0} (EAB EA EB) ≌ DGModuleCat.{0} (LABg A B) :=
  DGModuleCat.moritaEquivalence (ZZg A B) (ZZDualg A B) (zzDualTensorEquivg HA HB)
    (zzDualTensorEquivg_op_smul HA HB) (zzTensorDualEquivg HA HB) (zzTensorDualEquivg_op_smul HA HB)

theorem JA2g_inverse : (JA2g HA HB).inverse = DGModuleCat.tensorFunctor (EAB EA EB) (ZZg A B) := rfl

/-- `J^H` on `(E_A ⊗ E_B)`-modules. -/
def JH2g : DG.HomotopyCategory.{0} (EAB EA EB) ≌ DG.HomotopyCategory.{0} (LABg A B) :=
  DG.HomotopyCategory.moritaEquivalence (ZZg A B) (ZZDualg A B) (zzDualTensorEquivg HA HB)
    (zzDualTensorEquivg_op_smul HA HB) (zzTensorDualEquivg HA HB) (zzTensorDualEquivg_op_smul HA HB)

end Morita2

/-! ### The induction half -/

section Induction

variable {A B : ℕ} {EA EB EN : Type} [Ring EA] [DGAddCommGroup EA] [DGRing EA] [Module EA (Zn A)]
  [DGBimodule EA (osymDG A) (Zn A)] [Ring EB] [DGAddCommGroup EB] [DGRing EB] [Module EB (Zn B)]
  [DGBimodule EB (osymDG B) (Zn B)] [Ring EN] [DGAddCommGroup EN] [DGRing EN] [Module EN (Zn (A + B))]
  [DGBimodule EN (osymDG (A + B)) (Zn (A + B))]
  (HA : FullAction EA (osymDG A) (Zn A)) (HB : FullAction EB (osymDG B) (Zn B))
  (HN : FullAction EN (osymDG (A + B)) (Zn (A + B)))

variable (EA EB) in
/-- `Ind : (E_A ⊗ E_B)-dmod ⥤ E_{A+B}-dmod`, extension of scalars along `ι`. -/
abbrev IndAg : DGModuleCat.{0} (EAB EA EB) ⥤ DGModuleCat.{0} EN :=
  DGModuleCat.tensorFunctor EN (gIota EA EB HN).Bimodule

variable (A B) in
/-- `Z_{A,B}^∨`. -/
abbrev ZabDualG : Type := RightDual (osymDG (A + B)) (ZabTwG A B)

variable (A B) in
/-- **Definition 4.14** (underived): `I(M) = Z_{A,B}^∨ ⊗_{OΛ_A ⊗ OΛ_B} M`. -/
abbrev IAg : DGModuleCat.{0} (LABg A B) ⥤ DGModuleCat.{0} (osymDG (A + B)) :=
  DGModuleCat.tensorFunctor (osymDG (A + B)) (ZabDualG A B)

variable (A B) in
/-- The right basis of `Z_{A,B}` (Corollary 4.8). -/
def zabRightBasisG : RightBasis (osymDG (A + B)) (ZabTwG A B) (EQFix.ParIdx A B) := zabRightBasis A B

section ResTensor

variable (Y : Type) [AddCommGroup Y] [DGAddCommGroup Y] [Module (osymDG (A + B)) Y]
  [DGModule (osymDG (A + B)) Y]

variable (EA EB) in
/-- `ι^* (Z_{A+B} ⊗ Y)`. -/
abbrev ResTg : Type := RestrictScalars (gIota EA EB HN) (TensorProductOver (osymDG (A + B)) (Zn (A + B)) Y)

variable (EA EB) in
/-- `(ι^* Z_{A+B}) ⊗ Y`. -/
abbrev IZTg : Type := TensorProductOver (osymDG (A + B)) (IZG A B EA EB HN) Y

theorem iztg_smul (s : EAB EA EB) (t : IZTg EA EB HN Y) :
    (AddMonoidHom.id (IZTg EA EB HN Y) : IZTg EA EB HN Y →+ ResTg EA EB HN Y) (s • t) =
      s • (AddMonoidHom.id (IZTg EA EB HN Y) : IZTg EA EB HN Y →+ ResTg EA EB HN Y) t := by
  have h : (AddMonoidHom.id (IZTg EA EB HN Y) : IZTg EA EB HN Y →+ ResTg EA EB HN Y).comp
      (DistribSMul.toAddMonoidHom (IZTg EA EB HN Y) s) =
      (DistribSMul.toAddMonoidHom (ResTg EA EB HN Y) s).comp (AddMonoidHom.id (IZTg EA EB HN Y)) :=
    TensorProductOver.addHom_ext fun _ _ => rfl
  exact DFunLike.congr_fun h t

variable (EA EB) in
/-- `ι^* (Z_{A+B} ⊗ Y) = (ι^* Z_{A+B}) ⊗ Y`. -/
def resTensorEquivg : IZTg EA EB HN Y ≃ᵈᵍ[EAB EA EB] ResTg EA EB HN Y where
  toFun t := t
  invFun t := t
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' s t := iztg_smul HN Y s t
  map_mem' h := h
  map_d' _ := rfl

end ResTensor

theorem gIndEquiv_symm_op_smul (h : osymDG (A + B)) (t : IZG A B EA EB HN) :
    (gIndEquiv EA EB HN).symm (op h • t) = op h • (gIndEquiv EA EB HN).symm t := by
  apply (gIndEquiv EA EB HN).injective
  rw [gIndEquiv_op_smul, DGModuleEquiv.apply_symm_apply, DGModuleEquiv.apply_symm_apply]

/-- `Res ∘ (J^A)^{-1} ≅ (J^A_2)^{-1} ∘ (Z_{A,B} ⊗ -)`, from `gIndEquiv`. -/
def rightAdjIsog :
    ((JAg HN).inverse : DGModuleCat.{0} (osymDG (A + B)) ⥤ _) ⋙
        DGModuleCat.restrictScalars.{0} (gIota EA EB HN) ≅
      DGModuleCat.tensorFunctor (B := osymDG (A + B)) (LABg A B) (ZabTwG A B) ⋙ (JA2g HA HB).inverse :=
  NatIso.ofComponents (fun Y => (DGModuleCat.isoOfDGModuleEquiv (resTensorEquivg EA EB HN Y)).symm)
      (fun _ => DGModuleCat.hom_ext_apply fun _ => rfl) ≪≫
    DGModuleCat.tensorFunctorIsoOfEquiv (gIndEquiv EA EB HN).symm (gIndEquiv_symm_op_smul HN) ≪≫
    (DGModuleCat.tensorFunctorCompIso (ZabTwG A B) (ZZg A B)).symm

/-- **Ellis–Qi, Corollary 4.21, the induction half on abelian categories, in all ranks**:
`J^A ∘ Ind ≅ I ∘ J^A`. -/
def indIsoAg :
    IndAg EA EB HN ⋙ ((JAg HN).functor : _ ⥤ DGModuleCat.{0} (osymDG (A + B))) ≅
      (JA2g HA HB).functor ⋙ IAg A B :=
  ((DGModuleCat.extendRestrictScalarsAdj.{0} (gIota EA EB HN)).comp (JAg HN).toAdjunction).leftAdjointUniq
    (((JA2g HA HB).toAdjunction.comp (RightBasis.dualAdjunction (E := LABg A B) (zabRightBasisG A B))).ofNatIsoRight
      (rightAdjIsog HA HB HN).symm)

/-- `Ind` on homotopy categories. -/
abbrev IndHg : DG.HomotopyCategory.{0} (EAB EA EB) ⥤ DG.HomotopyCategory.{0} EN :=
  HomotopyCategory.tensorFunctor EN (gIota EA EB HN).Bimodule

/-- `I` on homotopy categories. -/
abbrev IHg : DG.HomotopyCategory.{0} (LABg A B) ⥤ DG.HomotopyCategory.{0} (osymDG (A + B)) :=
  HomotopyCategory.tensorFunctor (osymDG (A + B)) (ZabDualG A B)

/-- **Ellis–Qi, Corollary 4.21, the induction half on homotopy categories, in all ranks**:
`J^H ∘ Ind ≅ I ∘ J^H`. -/
def indIsoHg :
    IndHg HN ⋙ ((JHg HN).functor : _ ⥤ DG.HomotopyCategory.{0} (osymDG (A + B))) ≅
      (JH2g HA HB).functor ⋙ IHg (A := A) (B := B) :=
  HomotopyCategory.liftFunctorCompIso _ _ (HomotopyCategory.tensorFunctor_homotopic _ _)
      (HomotopyCategory.tensorFunctor_homotopic _ _) ≪≫
    HomotopyCategory.liftNatIso _ _ (indIsoAg HA HB HN) ≪≫
    (HomotopyCategory.liftFunctorCompIso _ _ (HomotopyCategory.tensorFunctor_homotopic _ _)
      (HomotopyCategory.tensorFunctor_homotopic _ _)).symm

end Induction

end OddMath.Frontier.EQLift
