import OddMath.Frontier.EQZnMorita
import DG.Homotopy.BimoduleTensor

/-!
# The abelian and homotopy Morita equivalences `J^A`, `J^H` (Ellis–Qi (4.30)–(4.31))

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§4.4, Definition 4.18 (`J^A`, `J^H`), the equivalences (4.30)–(4.31) and the paragraph after them
(printed numbering); every rank `N` (`N = n + 2` and, with `ONH_N = OPol_N`, `N ≤ 1`).

* `JA n : ONH_N-dmod ≌ OΛ_N-dmod`, the underived tensor product `M ↦ Z_N^∨ ⊗_{ONH_N} M`
  (`JA_functor_obj`), an equivalence of the categories of dg modules (with morphisms the
  closed degree-`0` maps), with quasi-inverse `M ↦ Z_N ⊗_{OΛ_N} M` (`JA_inverse_obj`, (4.31));
* `JH n : H(ONH_N) ≌ H(OΛ_N)`, the same functors on homotopy categories;
* `JASmall`, `JHSmall`: the same for `N ≤ 1`, where `ONH_N = OPol_N`
  (`EQFunctor.znTensorDualEquivSmall`, `EQFunctor.znDualTensorEquivSmall`).

Both are dg-lean's Morita equivalences from invertible bimodules
(`DG.DGModuleCat.moritaEquivalence`, `DG.HomotopyCategory.moritaEquivalence`) applied to the
bimodule isomorphisms `Z_N ⊗_{OΛ_N} Z_N^∨ ≅ ONH_N` and `Z_N^∨ ⊗_{ONH_N} Z_N ≅ OΛ_N`
(`EQFunctor.znTensorDualEquiv`, `EQFunctor.znDualTensorEquiv`). In contrast with the derived
functor `J` of Corollary 4.19, which is zero on `D(ONH_N) = 0`, `J^A` and `J^H` are equivalences
of nonzero categories.
-/

noncomputable section

open CategoryTheory

namespace OddMath.Frontier.EQFunctor

open OddMath.Frontier.EQSkewDifferential (osymDG Zn)
open OddMath.Frontier.EQOnhDG (ONH)
open DG TensorProductOver.RightAction

variable (n : ℕ)

/-- **Ellis–Qi (4.30)**: `J^A_N : ONH_N-dmod ≌ OΛ_N-dmod`, `M ↦ Z_N^∨ ⊗_{ONH_N} M` (`N = n + 2`),
with quasi-inverse `M ↦ Z_N ⊗_{OΛ_N} M` ((4.31)). -/
def JA : DGModuleCat.{0} (ONH n) ≌ DGModuleCat.{0} (osymDG (n + 2)) :=
  DGModuleCat.moritaEquivalence (Zn (n + 2)) (ZnDual n) (znDualTensorEquiv n)
    (znDualTensorEquiv_op_smul n) (znTensorDualEquiv n) (znTensorDualEquiv_op_smul n)

theorem JA_functor : (JA n).functor = DGModuleCat.tensorFunctor (osymDG (n + 2)) (ZnDual n) :=
  rfl

theorem JA_inverse : (JA n).inverse = DGModuleCat.tensorFunctor (ONH n) (Zn (n + 2)) := rfl

theorem JA_functor_obj (M : DGModuleCat.{0} (ONH n)) :
    ((JA n).functor.obj M : Type) = TensorProductOver (ONH n) (ZnDual n) M := rfl

theorem JA_inverse_obj (M : DGModuleCat.{0} (osymDG (n + 2))) :
    ((JA n).inverse.obj M : Type) = TensorProductOver (osymDG (n + 2)) (Zn (n + 2)) M := rfl

/-- **Ellis–Qi, after (4.31)**: `J^H_N : H(ONH_N) ≌ H(OΛ_N)` on homotopy categories, induced by
`Z_N^∨ ⊗_{ONH_N} (-)` (`N = n + 2`). -/
def JH : DG.HomotopyCategory.{0} (ONH n) ≌ DG.HomotopyCategory.{0} (osymDG (n + 2)) :=
  DG.HomotopyCategory.moritaEquivalence (Zn (n + 2)) (ZnDual n) (znDualTensorEquiv n)
    (znDualTensorEquiv_op_smul n) (znTensorDualEquiv n) (znTensorDualEquiv_op_smul n)

theorem JH_functor :
    (JH n).functor = DG.HomotopyCategory.tensorFunctor (osymDG (n + 2)) (ZnDual n) := rfl

/-- `J^H` is `J^A` followed by the quotient functor. -/
def JHQuotientIso :
    DG.HomotopyCategory.quotient (ONH n) ⋙ (JH n).functor ≅
      (JA n).functor ⋙ DG.HomotopyCategory.quotient (osymDG (n + 2)) :=
  DG.HomotopyCategory.tensorFunctorQuotientIso _ _

/-! ### Ranks `N ≤ 1` (`ONH_N = OPol_N`) -/

section Small

open OddMath.Frontier.EQSkewDifferential (OPol)

variable {N : ℕ} (hN : N ≤ 1)

/-- `J^A_N : ONH_N-dmod ≌ OΛ_N-dmod` for `N ≤ 1` (`ONH_N = OPol_N`), `M ↦ Z_N^∨ ⊗_{OPol_N} M`. -/
def JASmall : DGModuleCat.{0} (OPol N) ≌ DGModuleCat.{0} (osymDG N) :=
  DGModuleCat.moritaEquivalence (Zn N) (RightDual (osymDG N) (Zn N)) (znDualTensorEquivSmall hN)
    (znDualTensorEquivSmall_op_smul hN) (znTensorDualEquivSmall hN)
    (znTensorDualEquivSmall_op_smul hN)

theorem JASmall_functor :
    (JASmall hN).functor = DGModuleCat.tensorFunctor (osymDG N) (RightDual (osymDG N) (Zn N)) :=
  rfl

/-- `J^H_N : H(ONH_N) ≌ H(OΛ_N)` for `N ≤ 1`. -/
def JHSmall : DG.HomotopyCategory.{0} (OPol N) ≌ DG.HomotopyCategory.{0} (osymDG N) :=
  DG.HomotopyCategory.moritaEquivalence (Zn N) (RightDual (osymDG N) (Zn N))
    (znDualTensorEquivSmall hN) (znDualTensorEquivSmall_op_smul hN) (znTensorDualEquivSmall hN)
    (znTensorDualEquivSmall_op_smul hN)

theorem JHSmall_functor : (JHSmall hN).functor =
    DG.HomotopyCategory.tensorFunctor (osymDG N) (RightDual (osymDG N) (Zn N)) := rfl

end Small

end OddMath.Frontier.EQFunctor
