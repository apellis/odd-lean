import OddMath.Frontier.EQLiftRestriction
import OddMath.Frontier.EQRestrictionDerived

/-!
# The restriction half of Corollary 4.21 in all ranks (abelian and homotopy categories)

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§4.4, Definition 4.15, (4.32), Definition 4.20 and Corollary 4.21 ("`J^A` intertwines `R` with `Res^♮`"),
for all ranks `a`, `b`.

* generic, for full actions: `ResNatAg` (`M ↦ ONH^♮ ⊗ M`), `RAg` (`M ↦ Z^♮ ⊗ M`, extension of scalars along the
  block swap), **`resIsoAg : J^A ∘ R ≅ Res^♮ ∘ J^A`**, `resIsoHg` (homotopy categories), from `gEquivG`;
* for `ONH`: **`resIsoAll a b`** and **`resIsoHAll a b`** for all `a`, `b`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open CategoryTheory
open scoped TensorProduct

namespace OddMath.Frontier.EQLift

open OddMath.Frontier.EQSkewDifferential (osymDG Zn)
open OddMath.Frontier.EQK0Int (ONHAll ONHTensor)
open OddMath.Frontier.EQFunctor
open DG MulOpposite TensorProductOver.RightAction

section Restriction

variable {A B : ℕ} {EA EB EN : Type} [Ring EA] [DGAddCommGroup EA] [DGRing EA] [Module EA (Zn A)]
  [DGBimodule EA (osymDG A) (Zn A)] [Ring EB] [DGAddCommGroup EB] [DGRing EB] [Module EB (Zn B)]
  [DGBimodule EB (osymDG B) (Zn B)] [Ring EN] [DGAddCommGroup EN] [DGRing EN] [Module EN (Zn (A + B))]
  [DGBimodule EN (osymDG (A + B)) (Zn (A + B))]
  (HA : FullAction EA (osymDG A) (Zn A)) (HB : FullAction EB (osymDG B) (Zn B))
  (HN : FullAction EN (osymDG (A + B)) (Zn (A + B)))

variable (A B EA EB) in
/-- **Definition 4.20** (underived): `Res^♮(M) = ONH^♮ ⊗_{E_{A+B}} M`. -/
abbrev ResNatAg : DGModuleCat.{0} EN ⥤ DGModuleCat.{0} (EAB EA EB) :=
  DGModuleCat.tensorFunctor (B := EN) (EAB EA EB) (ONHNatG A B EA EB HN)

variable (A B) in
/-- **Definition 4.15**: `R(M) = Z^♮_{A,B} ⊗_{OΛ_{A+B}} M`, extension of scalars along the block swap. -/
abbrev RAg : DGModuleCat.{0} (osymDG (A + B)) ⥤ DGModuleCat.{0} (LABg A B) :=
  DGModuleCat.tensorFunctor (B := osymDG (A + B)) (LABg A B) (ZNatG A B)

theorem gEquivG_symm_op_smul (g : EN) (m : ONHNatG A B EA EB HN) :
    (gEquivG EA EB HN).symm (op g • m) = op g • (gEquivG EA EB HN).symm m := by
  apply (gEquivG EA EB HN).injective
  rw [gEquiv_op_smulG, DGModuleEquiv.apply_symm_apply, DGModuleEquiv.apply_symm_apply]

/-- `Res^♮ ≅ (J^A_2)^{-1} ∘ R ∘ J^A`. -/
def resNatIsog :
    ResNatAg A B EA EB HN ≅ ((JAg HN).functor : _ ⥤ DGModuleCat.{0} (osymDG (A + B))) ⋙
      RAg A B ⋙ (JA2g HA HB).inverse :=
  DGModuleCat.tensorFunctorIsoOfEquiv (gEquivG EA EB HN).symm (gEquivG_symm_op_smul HN) ≪≫
    (DGModuleCat.tensorFunctorCompIso (ZDG A B) (TTG A B)).symm ≪≫
    Functor.isoWhiskerLeft _ (DGModuleCat.tensorFunctorCompIso (ZNatG A B) (ZZg A B)).symm

/-- **Ellis–Qi, Corollary 4.21, the restriction half on abelian categories, for full actions**:
`R ∘ J^A ≅ J^A ∘ Res^♮`. -/
def resIsoAg :
    ((JAg HN).functor : _ ⥤ DGModuleCat.{0} (osymDG (A + B))) ⋙ RAg A B ≅
      ResNatAg A B EA EB HN ⋙ (JA2g HA HB).functor :=
  (Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ (JA2g HA HB).counitIso.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (resNatIsog HA HB HN).symm (JA2g HA HB).functor

variable (A B EA EB) in
/-- `Res^♮` on homotopy categories. -/
abbrev ResNatHg : DG.HomotopyCategory.{0} EN ⥤ DG.HomotopyCategory.{0} (EAB EA EB) :=
  HomotopyCategory.tensorFunctor (EAB EA EB) (ONHNatG A B EA EB HN)

variable (A B) in
/-- `R` on homotopy categories. -/
abbrev RHg : DG.HomotopyCategory.{0} (osymDG (A + B)) ⥤ DG.HomotopyCategory.{0} (LABg A B) :=
  HomotopyCategory.tensorFunctor (LABg A B) (ZNatG A B)

/-- **Ellis–Qi, Corollary 4.21, the restriction half on homotopy categories, for full actions**. -/
def resIsoHg :
    ((JHg HN).functor : _ ⥤ DG.HomotopyCategory.{0} (osymDG (A + B))) ⋙ RHg A B ≅
      ResNatHg A B EA EB HN ⋙ (JH2g HA HB).functor :=
  HomotopyCategory.liftFunctorCompIso _ _ (HomotopyCategory.tensorFunctor_homotopic _ _)
      (HomotopyCategory.tensorFunctor_homotopic _ _) ≪≫
    HomotopyCategory.liftNatIso _ _ (resIsoAg HA HB HN) ≪≫
    (HomotopyCategory.liftFunctorCompIso _ _ (HomotopyCategory.tensorFunctor_homotopic _ _)
      (HomotopyCategory.tensorFunctor_homotopic _ _)).symm

end Restriction

/-! ### All ranks -/

variable (a b : ℕ)

/-- **Ellis–Qi, Corollary 4.21, the restriction half on abelian categories, for all `a`, `b`**:
`R ∘ J^A ≅ J^A ∘ Res^♮`, with `ONH^♮_{a+b}` the right ideal `P^a ONH_{a+b}` (`ONHNatG`). -/
def resIsoAll :
    ((JAg (fullActionAll (a + b))).functor : _ ⥤ DGModuleCat.{0} (osymDG (a + b))) ⋙ RAg a b ≅
      ResNatAg a b (ONHAll a) (ONHAll b) (fullActionAll (a + b)) ⋙
        (JA2g (fullActionAll a) (fullActionAll b)).functor :=
  resIsoAg (fullActionAll a) (fullActionAll b) (fullActionAll (a + b))

/-- **Ellis–Qi, Corollary 4.21, the restriction half on homotopy categories, for all `a`, `b`**. -/
def resIsoHAll :
    ((JHg (fullActionAll (a + b))).functor : _ ⥤ DG.HomotopyCategory.{0} (osymDG (a + b))) ⋙ RHg a b ≅
      ResNatHg a b (ONHAll a) (ONHAll b) (fullActionAll (a + b)) ⋙
        (JH2g (fullActionAll a) (fullActionAll b)).functor :=
  resIsoHg (fullActionAll a) (fullActionAll b) (fullActionAll (a + b))

/-! ### Comparison with ranks `a + 2`, `b + 2` -/

/-- For `a, b ≥ 2`, `P^a ∈ ONH_{a+b}` of the all-rank construction is `EQFunctor.Pw`. -/
theorem PwG_eq_Pw (a b : ℕ) :
    PwG (a + 2) (b + 2) (fullActionAll ((a + 2) + (b + 2))) = (Pw a b : OddMath.Frontier.EQOnhDG.ONH (a + 2 + b)) :=
  (fullActionAll ((a + 2) + (b + 2))).ext fun z => by
    apply (zE ((a + 2) + (b + 2))).symm.injective
    rw [zE_symm_PwG_smul]
    exact (zE_symm_Pw_smul z).symm

end OddMath.Frontier.EQLift
