/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightDot
import OddMath.QuiverHecke.SwappedAssembly.ProductDenominatorUnits

/-! # Actual full-ELV denominator inverses from contentwise dot bounds

An arbitrary source superfunctor is followed by the actual weight induction.
The reservoir dot is the whiskering of the chosen normalized full-ELV dot.
Denominator inverses use fixed-content nilpotence, assembled as even natural
transformations. Neither the source objects nor target blocks are assumed
finite, and no global reservoir-dot exponent is used.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.SwappedAssembly
universe u v w
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)
  (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)
  {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C] [Supercategory k C]
  (F : Superfunctor k C (ELVWeightProduct D Sc cutoff bound Λ x))

abbrev elvPostInduction := F.comp (elvE D Sc cutoff bound i Λ h)
abbrev elvPostDot : End (elvPostInduction D Sc cutoff bound i Λ h F) :=
  Superfunctor.whiskerLeft F (elvActionDot D Sc cutoff bound i Λ h)

/-- A typed endomorphism component of the actual postinduction functor. -/
abbrev elvPostEndComponent
    (g : End (elvPostInduction D Sc cutoff bound i Λ h F)) (p : ZMod 2)
    (M : C) (δ : WeightBlocks D Λ y) :
    End (((elvPostInduction D Sc cutoff bound i Λ h F).obj M) δ) := g.app p M δ

theorem elvPostDot_mem :
    elvPostDot D Sc cutoff bound i Λ h F ∈ parity (R := k) _ _ (D.parity i) :=
  Superfunctor.whiskerLeft_mem F (elvActionDot_mem D Sc cutoff bound i Λ h)

include sy hc in
theorem elvPostDot_component_isNilpotent [Finite I] (M : C) (δ : WeightBlocks D Λ y) :
    IsNilpotent (elvPostEndComponent D Sc cutoff bound i Λ h F (elvPostDot D Sc cutoff bound i Λ h F) (D.parity i) M δ) :=
  elvWeightDotComponent_isNilpotent D Sc cutoff bound i Λ h sy hc (F.obj M) δ

include sy hc in
theorem elvPostDot_difference_isUnit [Finite I] (hi : D.parity i = 0)
    (X : End (elvPostInduction D Sc cutoff bound i Λ h F))
    (hx : X ∈ parity (R := k) _ _ 0)
    (hu : IsUnit X)
    (hcomm : ∀ M δ, Commute
      (elvPostEndComponent D Sc cutoff bound i Λ h F (elvPostDot D Sc cutoff bound i Λ h F) 0 M δ) (elvPostEndComponent D Sc cutoff bound i Λ h F X 0 M δ)) :
    IsUnit (elvPostDot D Sc cutoff bound i Λ h F - X) := by
  apply superfunctorEnd_isUnit
  · exact Submodule.sub_mem _
      (hi ▸ elvPostDot_mem D Sc cutoff bound i Λ h F) hx
  · intro M
    change IsUnit (show End ((elvPostInduction D Sc cutoff bound i Λ h F).obj M) from
      (elvPostDot D Sc cutoff bound i Λ h F).app 0 M - X.app 0 M)
    apply product_difference_isUnit
      (fun δ : WeightBlocks D Λ y => ContentModules D Sc cutoff bound δ.1)
    · exact fun δ => superfunctorProductEnd_component_isUnit _ _ X hu 0 hx M δ
    · intro δ
      simpa only [hi] using
        elvPostDot_component_isNilpotent D Sc cutoff bound sy hc i Λ h F M δ
    · exact hcomm M

include sy hc in
theorem elvPostDot_square_difference_isUnit [Finite I] (hi : D.parity i = 1)
    (X : End (elvPostInduction D Sc cutoff bound i Λ h F))
    (hx : X ∈ parity (R := k) _ _ 1)
    (hu : IsUnit X)
    (hanti : ∀ M δ,
      elvPostEndComponent D Sc cutoff bound i Λ h F (elvPostDot D Sc cutoff bound i Λ h F) 1 M δ * elvPostEndComponent D Sc cutoff bound i Λ h F X 1 M δ =
        -(elvPostEndComponent D Sc cutoff bound i Λ h F X 1 M δ * elvPostEndComponent D Sc cutoff bound i Λ h F (elvPostDot D Sc cutoff bound i Λ h F) 1 M δ)) :
    IsUnit (X ^ 2 - elvPostDot D Sc cutoff bound i Λ h F ^ 2) := by
  have hy : elvPostDot D Sc cutoff bound i Λ h F ∈ parity (R := k) _ _ 1 :=
    hi ▸ elvPostDot_mem D Sc cutoff bound i Λ h F
  apply superfunctorEnd_isUnit
  · simpa only [pow_two, End.mul_def, SuperNatTrans.zmod2_one_add_one] using
      Submodule.sub_mem _ (comp_mem hx hx) (comp_mem hy hy)
  · intro M
    change IsUnit (
      (show End ((elvPostInduction D Sc cutoff bound i Λ h F).obj M) from (X ^ 2).app 0 M) -
      (show End ((elvPostInduction D Sc cutoff bound i Λ h F).obj M) from
        (elvPostDot D Sc cutoff bound i Λ h F ^ 2).app 0 M))
    rw [superfunctor_odd_square_app_zero _ X hx M,
      superfunctor_odd_square_app_zero _ (elvPostDot D Sc cutoff bound i Λ h F) hy M]
    exact product_square_difference_isUnit
      (fun δ : WeightBlocks D Λ y => ContentModules D Sc cutoff bound δ.1)
      ((elvPostInduction D Sc cutoff bound i Λ h F).obj M)
      (show End ((elvPostInduction D Sc cutoff bound i Λ h F).obj M) from X.app 1 M)
      (show End ((elvPostInduction D Sc cutoff bound i Λ h F).obj M) from
        (elvPostDot D Sc cutoff bound i Λ h F).app 1 M)
      (fun δ => superfunctorProductEnd_component_isUnit _ _ X hu 1 hx M δ)
      (fun δ => by
        simpa only [hi] using
          elvPostDot_component_isNilpotent D Sc cutoff bound sy hc i Λ h F M δ)
      (hanti M)

end OddMath.QuiverHecke.ELVOld
