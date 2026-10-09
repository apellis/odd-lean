import OddMath.Frontier.EQLiftDerived
import DG.Category.Derived.DGBimoduleVanish

/-!
# The induction half of Corollary 4.21 on derived categories for `a = b = 1`

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§4.4, Corollary 4.21 on derived categories, ranks `a = b = 1`.

Here `D(ONH_1 ⊗ ONH_1) = D(OPol_1 ⊗ OPol_1)` is not zero, but `D(ONH_2) = 0`, so the induction half says that
`I_{1,1} ∘ J = Z_{1,1}^∨ ⊗^L (-) ∘ J` vanishes. It does, because `Z_{1,1}^∨` is acyclic:

* `zabOneOneEquiv`: `Z_{1,1} ≅ Z_2` as right dg `OΛ_2`-modules (`F ↦ (θ_1 ⊗ θ_1)(F) 1_z`; `OΛ_{1,1} = OPol_2`,
  `osymAB_one_one_eq_top`);
* `DG.RightDual.precompDGAddEquiv` (dg-lean): an isomorphism of right dg modules induces one of graded duals;
* `Z_2^∨` is a dg `(OΛ_2, ONH_2)`-bimodule, hence contractible, hence acyclic, as a left `OΛ_2`-module
  (`∂_1` acts on the right with `d ∂_1 = 1`, `isContractible_of_d_op_smul_eq_one`), and so is `Z_{1,1}^∨`
  (`zabDualOneOne_isAcyclic`);
* `Z_{1,1}^∨ ⊗^L (-) = 0` (`DGBimodule.derivedTensor_isZero_obj`), and **`indIsoDOneOne`**: `J ∘ Ind ≅ I ∘ J` on
  `D(ONH_1 ⊗ ONH_1)`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open CategoryTheory Limits
open scoped TensorProduct

namespace OddMath.Frontier.EQLift

open OddMath.SkewPolynomial (SkewPolynomial generator)
open OddMath.Frontier.EQSkewDifferential
open OddMath.Frontier.EQZab (inclX inclY osymAB)
open OddMath.Frontier.EQOnhDG (ONH)
open OddMath.Frontier.EQK0Int (ONHAll ONHTensor)
open OddMath.Frontier.EQFunctor
open DG MulOpposite


/-! ### `Z_{1,1} ≅ Z_2` -/

theorem osymAB_one_one_eq_top (f : SkewPolynomial (1 + 1)) : f ∈ osymAB 1 1 := by
  induction f using EQBorel.skew_induction with
  | hgen j =>
    have hx : inclX 1 1 (elementary 1 1) = generator 0 := by
      rw [elementary, EQZab.strictSum_one, Fin.sum_univ_one, EQZab.inclX_generator]; rfl
    have hy : inclY 1 1 (elementary 1 1) = generator 1 := by
      rw [elementary, EQZab.strictSum_one, Fin.sum_univ_one, EQZab.inclY_generator]; rfl
    fin_cases j
    · rw [show (⟨0, by norm_num⟩ : Fin (1 + 1)) = 0 from rfl, ← hx]
      exact EQZab.inclX_mem (EQZab.elementary_mem 1 1)
    · rw [show (⟨1, by norm_num⟩ : Fin (1 + 1)) = 1 from rfl, ← hy]
      exact EQZab.inclY_mem (EQZab.elementary_mem 1 1)
  | hint z => exact intCast_mem _ z
  | hadd f g hf hg => exact add_mem hf hg
  | hmul f g hf hg => exact mul_mem hf hg

/-- `1_z ⊠ 1_z ∈ Z_A ⊠ Z_B`. -/
def yOneG (A B : ℕ) : ZZg A B := zE A 1 ⊗ₜ[ℤ] zE B 1

theorem gPolyHom_yOneG (A B : ℕ) : gPolyHom (yOneG A B) = 1 := by
  rw [yOneG, gPolyHom_tmul, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply, map_one, map_one,
    sp_mul_one']

theorem d_zE_one_le_one {N : ℕ} (hN : N ≤ 1) : DG.d (zE N 1) = 0 := d_bz hN

theorem yOneG_mem (A B : ℕ) : yOneG A B ∈ DG.grading (0 : ℤ) := by
  have := DG.tmul_mem_grading (M := Zn A) (N := Zn B)
    (OPolAlpha.mem_grading_iff.mpr (by rw [AddEquiv.symm_apply_apply]; exact one_mem_grading'))
    (OPolAlpha.mem_grading_iff.mpr (by rw [AddEquiv.symm_apply_apply]; exact one_mem_grading'))
  rwa [add_zero] at this

theorem d_yOneG_one_one : DG.d (yOneG 1 1) = 0 := by
  rw [yOneG, DG.d_tmul, d_zE_one_le_one le_rfl, TensorProduct.zero_tmul,
    TensorProduct.tmul_zero, add_zero]

/-- `F ↦ (θ_1 ⊗ θ_1)(F) 1_z`, `Z_{1,1} → Z_2`. -/
def zabOneOneHom : ZabTwG 1 1 →+ Zn (1 + 1) := gIndFun (yOneG 1 1)

theorem zabOneOneHom_apply (F : ZabTwG 1 1) :
    zabOneOneHom F = zE (1 + 1) (EQZab.tauAB 1 1 (gTwVal F)) := by
  rw [zabOneOneHom, gIndFun_apply, gPolyHom_yOneG, sp_one_mul']

/-- **`Z_{1,1} ≅ Z_2`** as dg abelian groups (right `OΛ_2`-linear, `zabOneOneEquiv_op_smul`). -/
def zabOneOneEquiv : DGAddEquiv (ZabTwG 1 1) (Zn (1 + 1)) where
  toFun := zabOneOneHom
  invFun z := show EQFix.Zab 1 1 from
    EQFix.Zab.mk (EQZab.tauAB 1 1 ((zE (1 + 1)).symm z)) (osymAB_one_one_eq_top _)
  left_inv F := by
    apply EQFix.Zab.ext
    change EQZab.tauAB 1 1 ((zE (1 + 1)).symm (zabOneOneHom F)) = gTwVal F
    rw [zabOneOneHom_apply, AddEquiv.symm_apply_apply, EQZab.tauAB_tauAB]
  right_inv z := by
    rw [zabOneOneHom_apply]
    change zE (1 + 1) (EQZab.tauAB 1 1 (EQZab.tauAB 1 1 ((zE (1 + 1)).symm z))) = z
    rw [EQZab.tauAB_tauAB, AddEquiv.apply_symm_apply]
  map_add' := map_add _
  map_mem' {k F} hF := by
    have := gIndHom_mem (A := 1) (B := 1) (TensorProductOver.tmul_mem_grading
      (A := LABg 1 1) (yOneG_mem 1 1) hF)
    rwa [zero_add] at this
  map_d' F := by
    have h := gIndFun_d (yOneG_mem 1 1) F
    rw [d_yOneG_one_one, map_zero, AddMonoidHom.zero_apply, zero_add, koszulSign_zero, one_smul] at h
    exact h.symm

theorem zabOneOneEquiv_op_smul (h : osymDG (1 + 1)) (F : ZabTwG 1 1) :
    zabOneOneEquiv (op h • F) = op h • zabOneOneEquiv F :=
  gIndHom_op_smul h (TensorProductOver.tmul _ (yOneG 1 1) F)

/-! ### `Z_{1,1}^∨` is acyclic -/

theorem znDual_two_isAcyclic : DG.IsAcyclic (ZnDual 0) :=
  IsContractible.isAcyclic (isContractible_of_d_op_smul_eq_one (A := osymDG (0 + 2))
    (EQOnhDG.ONH.del_mem_grading (n := 0) 0) (EQOnhDG.ONH.d_del 0))

theorem zabDualOneOne_isAcyclic : DG.IsAcyclic (ZabDualG 1 1) :=
  IsAcyclic.of_dgAddEquiv (RightDual.precompDGAddEquiv (A := osymDG (1 + 1)) zabOneOneEquiv.symm fun a z => by
      apply zabOneOneEquiv.injective
      rw [DGAddEquiv.apply_symm_apply, zabOneOneEquiv_op_smul, DGAddEquiv.apply_symm_apply])
    znDual_two_isAcyclic

/-! ### The induction half for `a = b = 1` -/

universe w₂

variable
  [CatModule.HasDerivedCategory.{0, 0} (SingleObj (ONHTensor 1 1))]
  [CatModule.HasDerivedCategory.{0, 0} (SingleObj (ONHAll (1 + 1)))]
  [CatModule.HasDerivedCategory.{0, 0} (SingleObj (LABg 1 1))]
  [CatModule.HasDerivedCategory.{0, 0} (SingleObj (osymDG (1 + 1)))]
  [DG.HasDerivedCategory.{w₂, 0} (ONHTensor 1 1)] [DG.HasDerivedCategory.{w₂, 0} (ONHAll (1 + 1))]
  [DG.HasDerivedCategory.{w₂, 0} (LABg 1 1)] [DG.HasDerivedCategory.{w₂, 0} (osymDG (1 + 1))]

/-- `I_{1,1} = Z_{1,1}^∨ ⊗^L (-)` vanishes. -/
theorem IDAll_one_one_isZero (Y : DG.DerivedCategory.{w₂, 0} (LABg 1 1)) :
    IsZero ((IDAll.{0, w₂} 1 1).obj Y) :=
  DGBimodule.derivedTensor_isZero_obj _ _ zabDualOneOne_isAcyclic Y

/-- **Ellis–Qi, Corollary 4.21, the induction half on derived categories for `a = b = 1`**:
`J ∘ Ind ≅ I ∘ J` on `D(ONH_1 ⊗ ONH_1)`; both sides vanish (`D(ONH_2) = 0`, `I_{1,1} = 0`). -/
def indIsoDOneOne :
    IndDAll.{0, w₂} 1 1 ⋙ JDAll.{0, w₂} 1 1 ≅ J2DAll.{0, w₂} 1 1 ⋙ IDAll.{0, w₂} 1 1 :=
  NatIso.ofComponents (fun _ =>
    ((JDAll 1 1).map_isZero (isZero_derived_ONHAll (1 + 1) le_rfl _)).iso (IDAll_one_one_isZero _))
    (fun {_ _} _ => (IDAll_one_one_isZero _).eq_of_tgt _ _)

end OddMath.Frontier.EQLift
