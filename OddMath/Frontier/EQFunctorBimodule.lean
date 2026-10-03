import OddMath.Frontier.EQFixFiniteCell
import DG.Category.Derived.TensorInduction
import DG.K0.DGRing

/-!
# The derived tensor product with a dg bimodule over dg rings

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§2.2.3 ((2.13)–(2.16): the derived tensor product `M ⊗^L_B -` with a dg `(A, B)`-bimodule `M`,
derived induction and restriction).

This file is generic. Let `A`, `B` be dg rings and `M` a dg `(A, B)`-bimodule (`DG.DGBimodule`)
which is K-projective as a left dg `A`-module (for instance finite-cell). The `DG` library
constructs the derived tensor product for bimodules over dg categories
(`DG.CatModule.DerivedCategory.derivedTensor`); here it is transported to dg rings.

* `catBimodule A B M`: `M` as a dg bimodule over the one-object dg categories
  (`DG.CatBimodule (SingleObj A) (SingleObj B)`), with the same two actions;
* `isKProjective_toCatModuleObj`: a K-projective dg `A`-module is K-projective as a dg module over
  `SingleObj A`;
* `bimoduleDerivedTensor A B M hM : D(B) ⥤ D(A)`, the functor `M ⊗^L_B -`, a triangulated
  functor (`bimoduleDerivedTensor_commShift`, `bimoduleDerivedTensor_isTriangulated`);
* `bimoduleDerivedTensorSelfIso`: `M ⊗^L_B B ≅ M` in `D(A)`;
* `DGRingHom.derivedInduction` is triangulated (`derivedInduction_commShift`,
  `derivedInduction_isTriangulated`) and `derivedInductionSelfIso φ : φ^*(B) ≅ A` in `D(A)` for a
  morphism of dg rings `φ : B → A` (with `D(SingleObj B)` having morphisms in the universe of the
  dg modules);
* `isCompact_obj_of_isCompact_self`: a triangulated functor out of `D(B)` taking `B` to a compact
  object preserves compact objects;
* `K0_leftCorner_one`, `TriangularBasis.K0_mk`, `FreeBasis.K0_mk_toTriangular`: in `K₀(A)`, the class
  of a dg module with a finite triangular basis `(b_j)` is `Σ_j (-1)^{|b_j|} [A]`.
-/

open CategoryTheory

universe w₁ w₂ w₃ w₄ w' v

namespace OddMath.Frontier.EQFunctor

open DG MulOpposite

noncomputable section

/-! ## Bimodules over dg rings as bimodules over one-object dg categories -/

section CatBimodule

variable (A B : Type v) [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B] [DGAddCommGroup B]
  [DGRing B] (M : Type v) [AddCommGroup M] [DGAddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M]
  [DGBimodule A B M]

/-- A dg `(A, B)`-bimodule as a dg bimodule over the one-object dg categories `SingleObj A` and
`SingleObj B`, with the same left and right actions. -/
def catBimodule : CatBimodule.{v} (SingleObj A) (SingleObj B) where
  obj _ _ := M
  lact := smulAddHom A M
  ract := (smulAddHom Bᵐᵒᵖ M).comp (opAddEquiv : B ≃+ Bᵐᵒᵖ).toAddMonoidHom
  lact_mem' hf hx := smul_mem_grading (A := A) hf hx
  lact_id' _ _ x := one_smul A x
  lact_comp' f f' x := mul_smul (f' : A) (f : A) x
  d_lact' hf x := d_smul (A := A) hf x
  ract_mem' hg hx := op_smul_mem_grading (A := B) hg hx
  ract_id' _ _ x := one_smul Bᵐᵒᵖ x
  ract_comp' g g' x := mul_smul (op (g : B)) (op (g' : B)) x
  d_ract' hx g := d_op_smul (A := B) hx g
  lact_ract' f g x := smul_comm (f : A) (op (g : B)) x

omit [DGRing A] [DGRing B] in
theorem catBimodule_lact {X X' : SingleObj A} {Y : SingleObj B} (f : X ⟶ X') (x : M) :
    (catBimodule A B M).lact (Y := Y) f x = (f : A) • x := rfl

omit [DGRing A] [DGRing B] in
theorem catBimodule_ract {X : SingleObj A} {Y Y' : SingleObj B} (g : Y ⟶ Y') (x : M) :
    (catBimodule A B M).ract (X := X) g x = op (g : B) • x := rfl

omit [DGRing A] [DGRing B] in
/-- The left dg module `M(-, Y)` over `SingleObj A` is the dg `A`-module `M`. -/
theorem catBimodule_left (Y : SingleObj B) :
    (catBimodule A B M).left Y = DGModuleCat.toCatModuleObj (DGModuleCat.of A M) := rfl

end CatBimodule

section KProjective

variable {A : Type v} [Ring A] [DGAddCommGroup A] [DGRing A]

omit [DGRing A] in
/-- A K-projective dg `A`-module is K-projective as a dg module over the one-object dg category
`SingleObj A`. -/
theorem isKProjective_toCatModuleObj (P : DGModuleCat.{v} A) (hP : DG.IsKProjective.{v} A P) :
    CatModule.IsKProjective (DGModuleCat.toCatModuleObj P) := by
  intro N hN f
  rw [CatModule.homotopic_iff_toDGModuleCat]
  have h0 : ((CatModule.toDGModuleCat A).map (0 : DGModuleCat.toCatModuleObj P ⟶ N)).hom = 0 :=
    rfl
  rw [h0]
  exact hP.homotopic_zero (N := (CatModule.toDGModuleCatObj N : Type v))
    (hN (SingleObj.star A)) ((CatModule.toDGModuleCat A).map f).hom

end KProjective

/-! ## The derived tensor product -/

section DerivedTensor

variable (A B : Type v) [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B] [DGAddCommGroup B]
  [DGRing B] (M : Type v) [AddCommGroup M] [DGAddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M]
  [DGBimodule A B M] (hM : DG.IsKProjective.{v} A M)

omit [DGRing A] [DGRing B] in
include hM in
theorem catBimodule_left_isKProjective (Y : SingleObj B) :
    CatModule.IsKProjective ((catBimodule A B M).left Y) :=
  isKProjective_toCatModuleObj (DGModuleCat.of A M) hM

variable [CatModule.HasDerivedCategory.{w₁, v} (SingleObj B)]
  [CatModule.HasDerivedCategory.{w₂, v} (SingleObj A)]
  [DG.HasDerivedCategory.{w₃, v} B] [DG.HasDerivedCategory.{w₄, v} A]

/-- **The derived tensor product** `M ⊗^L_B - : D(B) ⥤ D(A)` with a dg `(A, B)`-bimodule `M` which
is K-projective as a left dg `A`-module (Ellis–Qi (2.13)): the derived tensor product with the
bimodule `catBimodule A B M` over the one-object dg categories, transported along the
equivalences `D(SingleObj B) ≌ D(B)` and `D(SingleObj A) ≌ D(A)`. -/
def bimoduleDerivedTensor : DG.DerivedCategory B ⥤ DG.DerivedCategory A :=
  (CatModule.DerivedCategory.singleObjEquivalence B).inverse ⋙
    CatModule.DerivedCategory.derivedTensor.{w₁, w₂, v} (catBimodule A B M)
      (catBimodule_left_isKProjective A B M hM) ⋙
      (CatModule.DerivedCategory.singleObjEquivalence A).functor

/-- `M ⊗^L_B -` commutes with the shifts. -/
instance bimoduleDerivedTensor_commShift :
    (bimoduleDerivedTensor.{w₁, w₂, w₃, w₄} A B M hM).CommShift ℤ :=
  letI := (CatModule.DerivedCategory.singleObjEquivalence B).commShiftInverse ℤ
  inferInstanceAs (((CatModule.DerivedCategory.singleObjEquivalence B).inverse ⋙
    CatModule.DerivedCategory.derivedTensor.{w₁, w₂, v} (catBimodule A B M)
      (catBimodule_left_isKProjective A B M hM) ⋙
      (CatModule.DerivedCategory.singleObjEquivalence A).functor).CommShift ℤ)

/-- `M ⊗^L_B -` is a triangulated functor. -/
instance bimoduleDerivedTensor_isTriangulated :
    (bimoduleDerivedTensor.{w₁, w₂, w₃, w₄} A B M hM).IsTriangulated := by
  let := (CatModule.DerivedCategory.singleObjEquivalence B).commShiftInverse ℤ
  have := (CatModule.DerivedCategory.singleObjEquivalence B).commShift_of_functor ℤ
  have : (CatModule.DerivedCategory.singleObjEquivalence B).IsTriangulated :=
    Equivalence.IsTriangulated.mk' _ inferInstance
  exact inferInstanceAs (((CatModule.DerivedCategory.singleObjEquivalence B).inverse ⋙
    CatModule.DerivedCategory.derivedTensor.{w₁, w₂, v} (catBimodule A B M)
      (catBimodule_left_isKProjective A B M hM) ⋙
      (CatModule.DerivedCategory.singleObjEquivalence A).functor).IsTriangulated)

/-- `M ⊗_B B ≅ M`, as dg modules over `SingleObj A`: the tensor product of the bimodule with the
representable module is the bimodule (the co-Yoneda isomorphism `m ⊗ b ↦ m b`). -/
def catBimoduleTensorRepresentableIso :
    (catBimodule A B M).tensorObj (CatModule.representable (SingleObj.star B)) ≅
      DGModuleCat.toCatModuleObj (DGModuleCat.of A M) :=
  CatModule.isoMk
    (fun X => (CatTensorProduct.rid ((catBimodule A B M).right X) (SingleObj.star B)).toAddEquiv)
    (fun {X k w} => ⟨fun h => by
      have h1 := (CatTensorProduct.rid ((catBimodule A B M).right X)
        (SingleObj.star B)).symm.map_mem h
      have h2 : (CatTensorProduct.rid ((catBimodule A B M).right X) (SingleObj.star B)).symm
          (CatTensorProduct.rid ((catBimodule A B M).right X) (SingleObj.star B) w) = w :=
        (CatTensorProduct.rid ((catBimodule A B M).right X) (SingleObj.star B)).symm_apply_apply w
      exact h2 ▸ h1,
      fun h => (CatTensorProduct.rid ((catBimodule A B M).right X) (SingleObj.star B)).map_mem h⟩)
    (fun {X} w =>
      (CatTensorProduct.rid ((catBimodule A B M).right X) (SingleObj.star B)).map_d w)
    (fun {X Y} f w => by
      change CatTensorProduct.rid ((catBimodule A B M).right Y) (SingleObj.star B)
          ((catBimodule A B M).tensorAct _ f w) =
        (f : A) • (show M from
          CatTensorProduct.rid ((catBimodule A B M).right X) (SingleObj.star B) w)
      induction w using CatTensorProduct.induction_on with
      | zero => rw [map_zero, map_zero, map_zero, smul_zero]
      | tmul Y' n h =>
        rw [CatBimodule.tensorAct_tmul, CatTensorProduct.rid_tmul, CatTensorProduct.rid_tmul,
          CatBimodule.right_ract, CatBimodule.right_ract]
        exact (smul_comm (M := A) (N := Bᵐᵒᵖ) (α := M) f (op h) n).symm
      | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, smul_add])

/-- **`M ⊗^L_B B ≅ M`** in `D(A)`. -/
def bimoduleDerivedTensorSelfIso :
    (bimoduleDerivedTensor.{w₁, w₂, w₃, w₄} A B M hM).obj
        (DG.DerivedCategory.Q.obj (DGModuleCat.of B B)) ≅
      DG.DerivedCategory.Q.obj (DGModuleCat.of A M) :=
  (CatModule.DerivedCategory.singleObjEquivalence A).functor.mapIso
    ((CatModule.DerivedCategory.derivedTensor.{w₁, w₂, v} (catBimodule A B M)
        (catBimodule_left_isKProjective A B M hM)).mapIso
      ((CatModule.DerivedCategory.singleObjEquivalence B).inverse.mapIso
          (DG.DerivedCategory.singleObjEquivalenceObjIso (DGModuleCat.of B B)).symm ≪≫
        ((CatModule.DerivedCategory.singleObjEquivalence B).unitIso.app _).symm ≪≫
        CatModule.DerivedCategory.Q.mapIso (CatModule.IsCornerGenerator.isoOfGen
          CatModule.isCornerGenerator_toCatModuleObj_self
          (CatModule.isCornerGenerator_representable (SingleObj.star B)))) ≪≫
      (CatModule.DerivedCategory.derivedTensorObjIso (catBimodule A B M)
        (catBimodule_left_isKProjective A B M hM)
        (CatModule.isKProjective_representable (SingleObj.star B))).symm ≪≫
      CatModule.DerivedCategory.Q.mapIso (catBimoduleTensorRepresentableIso A B M)) ≪≫
    DG.DerivedCategory.singleObjEquivalenceObjIso (DGModuleCat.of A M)

end DerivedTensor

/-! ## Derived induction along a morphism of dg rings -/

section Induction

variable {A B : Type v} [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B] [DGAddCommGroup B]
  [DGRing B] (φ : B →ᵈᵍ+* A)
  [CatModule.HasDerivedCategory.{w₁, v} (SingleObj B)]
  [CatModule.HasDerivedCategory.{w₂, v} (SingleObj A)]
  [DG.HasDerivedCategory.{w₃, v} B] [DG.HasDerivedCategory.{w₄, v} A]

/-- Derived induction along a morphism of dg rings commutes with the shifts. -/
instance derivedInduction_commShift : (φ.derivedInduction.{w₁, w₂, w₃, w₄}).CommShift ℤ :=
  letI := (CatModule.DerivedCategory.singleObjEquivalence B).commShiftInverse ℤ
  inferInstanceAs (((CatModule.DerivedCategory.singleObjEquivalence B).inverse ⋙
    CatModule.DerivedCategory.induction.{w₁, w₂, v} φ.singleObjFunctor ⋙
      (CatModule.DerivedCategory.singleObjEquivalence A).functor).CommShift ℤ)

/-- Derived induction along a morphism of dg rings is a triangulated functor. -/
instance derivedInduction_isTriangulated :
    (φ.derivedInduction.{w₁, w₂, w₃, w₄}).IsTriangulated := by
  let := (CatModule.DerivedCategory.singleObjEquivalence B).commShiftInverse ℤ
  have := (CatModule.DerivedCategory.singleObjEquivalence B).commShift_of_functor ℤ
  have : (CatModule.DerivedCategory.singleObjEquivalence B).IsTriangulated :=
    Equivalence.IsTriangulated.mk' _ inferInstance
  exact inferInstanceAs (((CatModule.DerivedCategory.singleObjEquivalence B).inverse ⋙
    CatModule.DerivedCategory.induction.{w₁, w₂, v} φ.singleObjFunctor ⋙
      (CatModule.DerivedCategory.singleObjEquivalence A).functor).IsTriangulated)

end Induction

section SelfIso

variable {A B : Type v} [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B] [DGAddCommGroup B]
  [DGRing B] (φ : B →ᵈᵍ+* A)
  [CatModule.HasDerivedCategory.{v, v} (SingleObj B)]
  [CatModule.HasDerivedCategory.{w₂, v} (SingleObj A)]
  [DG.HasDerivedCategory.{w₃, v} B] [DG.HasDerivedCategory.{w₄, v} A]

/-- **`φ^*(B) ≅ A`** in `D(A)`: derived induction along a morphism of dg rings `φ : B → A` takes
the free module of rank one to the free module of rank one. -/
def derivedInductionSelfIso :
    (φ.derivedInduction.{v, w₂, w₃, w₄}).obj (DG.DerivedCategory.Q.obj (DGModuleCat.of B B)) ≅
      DG.DerivedCategory.Q.obj (DGModuleCat.of A A) :=
  (CatModule.DerivedCategory.singleObjEquivalence A).functor.mapIso
    ((CatModule.DerivedCategory.induction.{v, w₂, v} φ.singleObjFunctor).mapIso
      ((CatModule.DerivedCategory.singleObjEquivalence B).inverse.mapIso
          (DG.DerivedCategory.singleObjEquivalenceObjIso (DGModuleCat.of B B)).symm ≪≫
        ((CatModule.DerivedCategory.singleObjEquivalence B).unitIso.app _).symm ≪≫
        CatModule.DerivedCategory.Q.mapIso (CatModule.IsCornerGenerator.isoOfGen
          CatModule.isCornerGenerator_toCatModuleObj_self
          (CatModule.isCornerGenerator_representable (SingleObj.star B)).ulift)) ≪≫
      CatModule.DerivedCategory.inductionRepresentableIso φ.singleObjFunctor (SingleObj.star B) ≪≫
      CatModule.DerivedCategory.Q.mapIso
        (CatModule.IsCornerGenerator.isoOfGen
          (CatModule.isCornerGenerator_representable (SingleObj.star A)).ulift
          CatModule.isCornerGenerator_toCatModuleObj_self)) ≪≫
    DG.DerivedCategory.singleObjEquivalenceObjIso (DGModuleCat.of A A)

end SelfIso

/-! ## Preservation of compact objects -/

section Compact

open Limits Pretriangulated

variable {B : Type v} [Ring B] [DGAddCommGroup B] [DGRing B] [DG.HasDerivedCategory.{v, v} B]
  {T : Type*} [Category T] [HasZeroObject T] [HasShift T ℤ] [Preadditive T]
  [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T] [HasCoproducts.{v} T]

/-- A triangulated functor out of `D(B)` which takes `B` to a compact object preserves compact
objects: the compact objects of `D(B)` form the thick subcategory generated by `B`
(`DG.DerivedCategory.thickClosure_self_eq_isCompact`), and the objects with compact image form a
thick subcategory. -/
theorem isCompact_obj_of_isCompact_self (F : DG.DerivedCategory.{v, v} B ⥤ T) [F.CommShift ℤ]
    [F.IsTriangulated]
    (hF : IsCompact.{v} (F.obj (DG.DerivedCategory.Q.obj (DGModuleCat.of B B))))
    {X : DG.DerivedCategory.{v, v} B} (hX : IsCompact.{v} X) : IsCompact.{v} (F.obj X) := by
  rw [← DG.DerivedCategory.thickClosure_self_eq_isCompact] at hX
  have hP : IsThick (fun Y : DG.DerivedCategory.{v, v} B => IsCompact.{v} (F.obj Y)) :=
    { zero := IsCompact.of_isZero (F.map_isZero (isZero_zero _))
      shift := fun Y n hY => (hY.shift n).of_iso ((F.commShiftIso n).app Y)
      ext₂ := fun R hR h₁ h₃ => IsCompact.ext₂ _ (F.map_distinguished R hR) h₁ h₃
      retract := fun e hY => hY.of_retract (e.map F) }
  refine thickClosure_le hP ?_ X hX
  rintro _ ⟨-, rfl⟩
  exact hF

end Compact

/-! ## Classes in `K₀` -/

section K0

variable {A : Type v} [Ring A] [DGAddCommGroup A] [DGRing A]

/-- `A · 1 ≅ A` as dg `A`-modules. -/
def oneLeftCornerIso :
    DGModuleCat.of A (EQFix.oneIdempotent A).LeftCorner ≅ DGModuleCat.of A A where
  hom := DGModuleCat.ofHom (EQFix.oneIdempotent A).leftCornerInclusion
  inv := DGModuleCat.ofHom (EQFix.oneIdempotent A).leftCornerProjection
  hom_inv_id := DGModuleCat.hom_ext_apply fun x => Subtype.ext x.2
  inv_hom_id := DGModuleCat.hom_ext_apply fun _ => mul_one _

variable [DG.HasDerivedCategory.{w', v} A]

/-- The class of the corner module `A · 1` is `[A]`. -/
theorem K0_leftCorner_one :
    DGRing.K0.leftCorner (EQFix.oneIdempotent A) = DGRing.K0.self.{w'} A :=
  DG.K0.mk_eq_of_iso_obj (DG.DerivedCategory.Q.mapIso oneLeftCornerIso)

/-- **The class of a dg module with a finite triangular basis** `(b_j)`:
`[P] = Σ_j (-1)^{|b_j|} [A]` in `K₀(A)`. -/
theorem _root_.OddMath.Frontier.EQFix.TriangularBasis.K0_mk {P : Type v} [AddCommGroup P]
    [DGAddCommGroup P] [Module A P] [DGModule A P] (T : EQFix.TriangularBasis A P) :
    DG.K0.mk (⟨DG.DerivedCategory.Q.obj (DGModuleCat.of A P),
        T.finiteCellFiltration.isCompact_Q_obj⟩ : PerfectDerivedCategory.{w', v} A) =
      ∑ j, (T.deg j).negOnePow • DGRing.K0.self.{w'} A := by
  rw [DGRing.K0.mk_finiteCell T.finiteCellFiltration]
  change ∑ j : Fin T.length,
    (-T.deg j).negOnePow • DGRing.K0.leftCorner (EQFix.oneIdempotent A) = _
  simp only [K0_leftCorner_one, Int.negOnePow_neg]

/-- **The class of a dg module with a finite free basis** `(b_i)` ordered by a key decreased by
the differential: `[P] = Σ_i (-1)^{|b_i|} [A]` in `K₀(A)`. -/
theorem _root_.OddMath.Frontier.EQFix.FreeBasis.K0_mk_toTriangular {P : Type v} [AddCommGroup P]
    [DGAddCommGroup P] [Module A P] [DGModule A P] {ι : Type*} [Fintype ι]
    (Bs : EQFix.FreeBasis A P ι) (key : ι → ℤ)
    (hkey : ∀ i l, Bs.coeff (d (Bs.b i)) l ≠ 0 → key l < key i) :
    DG.K0.mk (⟨DG.DerivedCategory.Q.obj (DGModuleCat.of A P),
        (Bs.toTriangular key hkey).finiteCellFiltration.isCompact_Q_obj⟩ :
          PerfectDerivedCategory.{w', v} A) =
      ∑ i, (Bs.deg i).negOnePow • DGRing.K0.self.{w'} A := by
  rw [EQFix.TriangularBasis.K0_mk (Bs.toTriangular key hkey)]
  exact (EQFix.FreeBasis.order key).sum_comp fun i => (Bs.deg i).negOnePow • DGRing.K0.self A

end K0

end

end OddMath.Frontier.EQFunctor
