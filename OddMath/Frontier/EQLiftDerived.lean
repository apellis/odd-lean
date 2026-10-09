import OddMath.Frontier.EQLiftResFunctor

/-!
# Corollary 4.21 on derived categories in all ranks: the functors, and the ranks where a category vanishes

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§4.4, Definitions 4.14, 4.15, 4.18, 4.20 and Corollary 4.21 ("the same is true of `J` on derived categories").

For all `a`, `b` (with `ONH_N = EQK0Int.ONHAll N`):

* `JDAll N = Z_N^∨ ⊗^L_{ONH_N} (-)` (Definition 4.18), `J2DAll a b = (Z_a^∨ ⊠ Z_b^∨) ⊗^L (-)` on `D(ONH_a ⊗ ONH_b)`,
  `IndDAll a b` (derived induction along `ι_{a,b}`, (3.40)), `IDAll a b = Z_{a,b}^∨ ⊗^L (-)` (Definition 4.14),
  `RDAll a b` (derived induction along the block swap, Definition 4.15);
* `ONH^♮_{a+b}` is contractible, hence K-projective, as a left `ONH_a ⊗ ONH_b`-module when `a + b ≥ 2`
  (`onhNatAll_isKProjective`), and `ResNatDAll a b = ONH^♮ ⊗^L (-)` (Definition 4.20);
* `D(ONH_N) = 0` for `N ≥ 2` and `D(ONH_a ⊗ ONH_b) = 0` for `a ≥ 2` or `b ≥ 2`
  (`isZero_derived_ONHAll`, `isZero_derived_ONHTensor`); hence the restriction half on derived categories for
  `a + b ≥ 2` (`resIsoDAll_of_two`) and the induction half for `a ≥ 2` or `b ≥ 2` (`indIsoDAll_of_two`).
-/

noncomputable section

set_option linter.unusedSectionVars false

open CategoryTheory
open scoped TensorProduct

namespace OddMath.Frontier.EQLift

open OddMath.Frontier.EQSkewDifferential (osymDG Zn)
open OddMath.Frontier.EQOnhDG (ONH)
open OddMath.Frontier.EQK0Int (ONHAll ONHTensor delAll d_delAll d_del_tmul_one d_one_tmul_del)
open OddMath.Frontier.EQFunctor
open DG MulOpposite TensorProductOver.RightAction

/-! ### Elements with `d = 1` -/

theorem exists_d_eq_one_ONHAll : ∀ N : ℕ, 2 ≤ N →
    ∃ t : ONHAll N, t ∈ DG.grading (-1 : ℤ) ∧ DG.d t = 1
  | n + 2, _ => ⟨delAll n, EQOnhDG.ONH.del_mem_grading (n := n) 0, d_delAll n⟩

theorem exists_d_eq_one_ONHTensor (a b : ℕ) (h : 2 ≤ a ∨ 2 ≤ b) :
    ∃ t : ONHTensor a b, t ∈ DG.grading (-1 : ℤ) ∧ DG.d t = 1 := by
  rcases h with h | h
  · obtain ⟨m, rfl⟩ : ∃ m, a = m + 2 := ⟨a - 2, by omega⟩
    refine ⟨delAll m ᵍ⊗ₜ[ℤ] (1 : ONHAll b), ?_, d_del_tmul_one m b⟩
    have := GradedTensorProduct.tmul_mem_grading (R := ℤ)
      (EQOnhDG.ONH.del_mem_grading (n := m) 0) (DG.one_mem_grading (A := ONHAll b))
    rwa [add_zero] at this
  · obtain ⟨m, rfl⟩ : ∃ m, b = m + 2 := ⟨b - 2, by omega⟩
    refine ⟨(1 : ONHAll a) ᵍ⊗ₜ[ℤ] delAll m, ?_, d_one_tmul_del a m⟩
    have := GradedTensorProduct.tmul_mem_grading (R := ℤ)
      (DG.one_mem_grading (A := ONHAll a)) (EQOnhDG.ONH.del_mem_grading (n := m) 0)
    rwa [zero_add] at this

universe w₁ w₂

theorem isZero_derived_of_d_eq_one {E : Type} [Ring E] [DGAddCommGroup E] [DGRing E]
    [DG.HasDerivedCategory.{w₂, 0} E] {t : E} (ht : t ∈ DG.grading (-1 : ℤ)) (hd : DG.d t = 1)
    (X : DG.DerivedCategory.{w₂, 0} E) : Limits.IsZero X := by
  have := Localization.essSurj (DG.DerivedCategory.Q (A := E)) (DG.DGModuleCat.quasiIso E)
  exact ((DG.DerivedCategory.isZero_Q_obj_iff _).mpr (EQOnhDG.isAcyclic_of_d_eq_one ht hd _)).of_iso
    (DG.DerivedCategory.Q.objObjPreimageIso X).symm

theorem isZero_derived_ONHAll (N : ℕ) (h : 2 ≤ N) [DG.HasDerivedCategory.{w₂, 0} (ONHAll N)]
    (X : DG.DerivedCategory.{w₂, 0} (ONHAll N)) : Limits.IsZero X := by
  obtain ⟨t, ht, hd⟩ := exists_d_eq_one_ONHAll N h
  exact isZero_derived_of_d_eq_one ht hd X

theorem isZero_derived_ONHTensor (a b : ℕ) (h : 2 ≤ a ∨ 2 ≤ b) [DG.HasDerivedCategory.{w₂, 0} (ONHTensor a b)]
    (X : DG.DerivedCategory.{w₂, 0} (ONHTensor a b)) : Limits.IsZero X := by
  obtain ⟨t, ht, hd⟩ := exists_d_eq_one_ONHTensor a b h
  exact isZero_derived_of_d_eq_one ht hd X

/-! ### `ONH^♮` is K-projective for `a + b ≥ 2` -/

variable (a b : ℕ)

/-- `ONH^♮_{a+b}` for `ONH`. -/
abbrev ONHNatAll : Type := ONHNatG a b (ONHAll a) (ONHAll b) (fullActionAll (a + b))

/-- For `a + b ≥ 2`, `ONH^♮_{a+b}` is contractible as a left `ONH_a ⊗ ONH_b`-module (`m ↦ ± m ∂_1`), hence
K-projective. -/
theorem onhNatAll_isKProjective (h : 2 ≤ a + b) : IsKProjective.{0} (ONHTensor a b) (ONHNatAll a b) := by
  obtain ⟨t, ht, hd⟩ := exists_d_eq_one_ONHAll (a + b) h
  exact (isContractible_of_d_op_smul_eq_one ht hd).isKProjective

/-! ### The derived functors -/

section Derived

variable
  [CatModule.HasDerivedCategory.{w₁, 0} (SingleObj (ONHTensor a b))]
  [CatModule.HasDerivedCategory.{w₁, 0} (SingleObj (ONHAll (a + b)))]
  [CatModule.HasDerivedCategory.{w₁, 0} (SingleObj (LABg a b))]
  [CatModule.HasDerivedCategory.{w₁, 0} (SingleObj (osymDG (a + b)))]
  [DG.HasDerivedCategory.{w₂, 0} (ONHTensor a b)] [DG.HasDerivedCategory.{w₂, 0} (ONHAll (a + b))]
  [DG.HasDerivedCategory.{w₂, 0} (LABg a b)] [DG.HasDerivedCategory.{w₂, 0} (osymDG (a + b))]

/-- **Definition 4.18** in rank `a + b`: `J = Z^∨ ⊗^L_{ONH} (-)`. -/
abbrev JDAll : DG.DerivedCategory.{w₂, 0} (ONHAll (a + b)) ⥤ DG.DerivedCategory.{w₂, 0} (osymDG (a + b)) :=
  bimoduleDerivedTensor.{w₁, w₁, w₂, w₂} (osymDG (a + b)) (ONHAll (a + b)) (RightDual (osymDG (a + b)) (Zn (a + b)))
    (znDual_isKProjective (a + b))

/-- `J` on `D(ONH_a ⊗ ONH_b)`: `(Z_a^∨ ⊠ Z_b^∨) ⊗^L (-)`. -/
abbrev J2DAll : DG.DerivedCategory.{w₂, 0} (ONHTensor a b) ⥤ DG.DerivedCategory.{w₂, 0} (LABg a b) :=
  bimoduleDerivedTensor.{w₁, w₁, w₂, w₂} (LABg a b) (ONHTensor a b) (ZZDualg a b)
    (ExternalTensor.isKProjective (znDual_isKProjective a) (znDual_isKProjective b))

/-- `Ind`: derived induction along `ι_{a,b}` ((3.40)). -/
abbrev IndDAll : DG.DerivedCategory.{w₂, 0} (ONHTensor a b) ⥤ DG.DerivedCategory.{w₂, 0} (ONHAll (a + b)) :=
  (iotaAll a b).derivedInduction.{w₁, w₁, w₂, w₂}

/-- **Definition 4.14**: `I = Z_{a,b}^∨ ⊗^L_{OΛ_a ⊗ OΛ_b} (-)`. -/
abbrev IDAll : DG.DerivedCategory.{w₂, 0} (LABg a b) ⥤ DG.DerivedCategory.{w₂, 0} (osymDG (a + b)) :=
  bimoduleDerivedTensor.{w₁, w₁, w₂, w₂} (osymDG (a + b)) (LABg a b) (ZabDualG a b) (zdual_isKProjective (a := a) (b := b))

/-- **Definition 4.15**: `R = Z^♮_{a,b} ⊗^L (-)`, derived induction along the block swap. -/
abbrev RDAll : DG.DerivedCategory.{w₂, 0} (osymDG (a + b)) ⥤ DG.DerivedCategory.{w₂, 0} (LABg a b) :=
  (swapDGG a b).derivedInduction.{w₁, w₁, w₂, w₂}

/-- **Definition 4.20** for `a + b ≥ 2`: `Res^♮ = ONH^♮ ⊗^L (-)`. -/
abbrev ResNatDAll (h : 2 ≤ a + b) :
    DG.DerivedCategory.{w₂, 0} (ONHAll (a + b)) ⥤ DG.DerivedCategory.{w₂, 0} (ONHTensor a b) :=
  bimoduleDerivedTensor.{w₁, w₁, w₂, w₂} (ONHTensor a b) (ONHAll (a + b)) (ONHNatAll a b)
    (onhNatAll_isKProjective a b h)

/-- **Corollary 4.21, the restriction half on derived categories, `a + b ≥ 2`**: `R ∘ J ≅ J ∘ Res^♮` for every
functor `Res^♮` (in particular `ResNatDAll`), since `D(ONH_{a+b}) = 0`. -/
def resIsoDAll_of_two (h : 2 ≤ a + b)
    (F : DG.DerivedCategory.{w₂, 0} (ONHAll (a + b)) ⥤ DG.DerivedCategory.{w₂, 0} (ONHTensor a b))
    [F.PreservesZeroMorphisms] :
    JDAll.{w₁, w₂} a b ⋙ RDAll.{w₁, w₂} a b ≅ F ⋙ J2DAll.{w₁, w₂} a b :=
  NatIso.ofComponents (fun X =>
    ((RDAll a b).map_isZero ((JDAll a b).map_isZero (isZero_derived_ONHAll (a + b) h X))).iso
      ((J2DAll a b).map_isZero (F.map_isZero (isZero_derived_ONHAll (a + b) h X))))
    (fun {_ Y} _ => ((J2DAll a b).map_isZero (F.map_isZero (isZero_derived_ONHAll (a + b) h Y))).eq_of_tgt _ _)

/-- **Corollary 4.21, the restriction half on derived categories, `a + b ≥ 2`**, with `Res^♮ = ONH^♮ ⊗^L (-)`. -/
def resNatIsoDAll (h : 2 ≤ a + b) :
    JDAll.{w₁, w₂} a b ⋙ RDAll.{w₁, w₂} a b ≅ ResNatDAll.{w₁, w₂} a b h ⋙ J2DAll.{w₁, w₂} a b :=
  resIsoDAll_of_two a b h _

/-- **Corollary 4.21, the induction half on derived categories, `a ≥ 2` or `b ≥ 2`**: `J ∘ Ind ≅ I ∘ J`, since
`D(ONH_a ⊗ ONH_b) = 0`. -/
def indIsoDAll_of_two (h : 2 ≤ a ∨ 2 ≤ b) :
    IndDAll.{w₁, w₂} a b ⋙ JDAll.{w₁, w₂} a b ≅ J2DAll.{w₁, w₂} a b ⋙ IDAll.{w₁, w₂} a b :=
  NatIso.ofComponents (fun X =>
    ((JDAll a b).map_isZero ((IndDAll a b).map_isZero (isZero_derived_ONHTensor a b h X))).iso
      ((IDAll a b).map_isZero ((J2DAll a b).map_isZero (isZero_derived_ONHTensor a b h X))))
    (fun {_ Y} _ => ((IDAll a b).map_isZero ((J2DAll a b).map_isZero
      (isZero_derived_ONHTensor a b h Y))).eq_of_tgt _ _)

end Derived

end OddMath.Frontier.EQLift
