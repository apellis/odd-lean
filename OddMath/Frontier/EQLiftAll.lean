import OddMath.Frontier.EQLiftFunctor
import OddMath.Frontier.EQKunnethIntAll

/-!
# `ONH_N` acting on `Z_N` in every rank; the induction half of Corollary 4.21 for all `a`, `b`

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§3.6 (3.39), §4.4 (4.30)–(4.31) and Corollary 4.21, for all ranks `a`, `b` (including `0` and `1`, where
`ONH_0 = OPol_0`, `ONH_1 = OPol_1`).

`EQK0Int.ONHAll N` is `ONH_N` for every `N`. It acts on `Z_N` (`instModuleONHAllZn`,
`instDGBimoduleONHAllZn`), fully (`fullActionAll`: Corollary 3.9 for `N ≥ 2`, `EQFunctor.fullActionSmall`
for `N ≤ 1`). With it:

* `iotaAll a b : ONH_a ⊗ ONH_b → ONH_{a+b}`, a morphism of dg rings; it acts on `Z_{a+b} = Z_a ⊠ Z_b` through
  the actions on the factors (`iotaAll_smul_polyHom`), and for `a, b ≥ 2` it is the inclusion `ONH.iota` of
  (3.39) (`iotaAll_eq_iota`);
* **`indIsoAll a b : J^A ∘ Ind ≅ I ∘ J^A`** and **`indIsoHAll a b`** (homotopy categories): the induction half
  of Corollary 4.21 for all `a`, `b`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open CategoryTheory
open scoped TensorProduct

namespace OddMath.Frontier.EQLift

open OddMath.Frontier.EQSkewDifferential (osymDG Zn OPol)
open OddMath.Frontier.EQOnhDG (ONH)
open OddMath.Frontier.EQK0Int (ONHAll ONHTensor)
open OddMath.Frontier.EQFunctor
open DG MulOpposite TensorProductOver.RightAction

/-! ### `ONH_N` acts fully on `Z_N` -/

instance instModuleONHAllZn (N : ℕ) : Module (ONHAll N) (Zn N) :=
  match N with
  | 0 => inferInstanceAs (Module (OPol 0) (Zn 0))
  | 1 => inferInstanceAs (Module (OPol 1) (Zn 1))
  | n + 2 => inferInstanceAs (Module (ONH n) (Zn (n + 2)))

instance instDGBimoduleONHAllZn (N : ℕ) : DGBimodule (ONHAll N) (osymDG N) (Zn N) :=
  match N with
  | 0 => inferInstanceAs (DGBimodule (OPol 0) (osymDG 0) (Zn 0))
  | 1 => inferInstanceAs (DGBimodule (OPol 1) (osymDG 1) (Zn 1))
  | n + 2 => inferInstanceAs (DGBimodule (ONH n) (osymDG (n + 2)) (Zn (n + 2)))

/-- `ONH_N` acts fully on `Z_N` for every `N` (Corollary 3.9 for `N ≥ 2`). -/
theorem fullActionAll (N : ℕ) : FullAction (ONHAll N) (osymDG N) (Zn N) :=
  match N with
  | 0 => fullActionSmall (by norm_num)
  | 1 => fullActionSmall le_rfl
  | n + 2 => EQOnhDG.ONH.fullAction n

/-! ### `ι` in every rank -/

variable (a b : ℕ)

/-- **`ι_{a,b} : ONH_a ⊗ ONH_b → ONH_{a+b}`** for all `a`, `b`. -/
def iotaAll : ONHTensor a b →ᵈᵍ+* ONHAll (a + b) :=
  gIota (ONHAll a) (ONHAll b) (fullActionAll (a + b))

variable {a b}

/-- `ι(s)` acts on `Z_{a+b} = Z_a ⊠ Z_b` through the actions of `ONH_a` and `ONH_b` on the factors. -/
theorem iotaAll_smul_polyHom (s : ONHTensor a b) (y : ZZg a b) :
    iotaAll a b s • zE (a + b) (gPolyHom y) = zE (a + b) (gPolyHom (s • y)) := by
  have h1 : gIndInv (zE (a + b) (gPolyHom y)) = TensorProductOver.tmul _ y (gZabOne a b) := by
    change TensorProductOver.tmul _ (gPolyEquiv.symm ((zE _).symm (zE _ (gPolyHom y)))) _ = _
    rw [AddEquiv.symm_apply_apply, ← gPolyEquiv_apply, AddEquiv.symm_apply_apply]
  rw [iotaAll, gIota_smul, conjMap_apply, h1]
  change zE _ (gPolyHom (s • y) * EQZab.tauAB a b (gTwVal (gZabOne a b))) = _
  rw [gTwVal_one, map_one, sp_mul_one']

/-- For `a, b ≥ 2`, `ι` is the inclusion `ONH.iota` of (3.39) (diagrams placed side by side). -/
theorem iotaAll_eq_iota (a b : ℕ) (s : ONHTensor (a + 2) (b + 2)) :
    iotaAll (a + 2) (b + 2) s = ONH.iota a b s := by
  refine (fullActionAll ((a + 2) + (b + 2))).ext fun z => ?_
  obtain ⟨y, rfl⟩ : ∃ y : ZZg (a + 2) (b + 2), zE _ (gPolyHom y) = z :=
    ⟨gPolyEquiv.symm ((zE _).symm z), by
      rw [← gPolyEquiv_apply, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]⟩
  rw [iotaAll_smul_polyHom]
  exact zE_polyHom_smul s y

/-! ### The induction half for all ranks -/

variable (a b)

/-- **Ellis–Qi, Corollary 4.21, the induction half on abelian categories, for all `a`, `b`**:
`J^A ∘ Ind ≅ I ∘ J^A` with `Ind` extension of scalars along `ι_{a,b}`. -/
def indIsoAll :
    IndAg (ONHAll a) (ONHAll b) (fullActionAll (a + b)) ⋙
        ((JAg (fullActionAll (a + b))).functor : _ ⥤ DGModuleCat.{0} (osymDG (a + b))) ≅
      (JA2g (fullActionAll a) (fullActionAll b)).functor ⋙ IAg a b :=
  indIsoAg (fullActionAll a) (fullActionAll b) (fullActionAll (a + b))

/-- **Ellis–Qi, Corollary 4.21, the induction half on homotopy categories, for all `a`, `b`**. -/
def indIsoHAll :
    IndHg (EA := ONHAll a) (EB := ONHAll b) (fullActionAll (a + b)) ⋙
        ((JHg (fullActionAll (a + b))).functor : _ ⥤ DG.HomotopyCategory.{0} (osymDG (a + b))) ≅
      (JH2g (fullActionAll a) (fullActionAll b)).functor ⋙ IHg (A := a) (B := b) :=
  indIsoHg (fullActionAll a) (fullActionAll b) (fullActionAll (a + b))

end OddMath.Frontier.EQLift
