import DG.Derived.TriangularBasis
import DG.K0.TriangularBasis
import DG.Category.Derived.DGBimodule
import DG.Derived.ExternalTensorOver
import DG.Category.Derived.TensorInduction
import DG.K0.DGRing

/-!
# Derived induction of the free module of rank one

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§2.2.3 ((2.13)–(2.16): the derived tensor product `M ⊗^L_B -` with a dg `(A, B)`-bimodule `M`,
derived induction and restriction).

The derived tensor product with a dg bimodule over dg rings is `DG.DGBimodule.derivedTensor`
(dg-lean), derived induction along a morphism of dg rings is triangulated
(`DG.DGRingHom.derivedInduction_isTriangulated`), compact objects are preserved by triangulated
functors taking the regular module to a compact object
(`DG.DerivedCategory.isCompact_obj_of_isCompact_self`), and the classes in `K₀` of modules with a
finite triangular basis are `DG.TriangularBasis.K0_mk`, `DG.FreeBasis.K0_mk_toTriangular`.

* `derivedInductionSelfIso φ : φ^*(B) ≅ A` in `D(A)` for a morphism of dg rings `φ : B → A`, with
  `D(SingleObj B)` having morphisms in the universe of the dg modules and `D(SingleObj A)` in any
  universe.
-/

open CategoryTheory

universe w₁ w₂ w₃ w₄ w' v

namespace OddMath.Frontier.EQFunctor

open DG

noncomputable section

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

end

end OddMath.Frontier.EQFunctor
