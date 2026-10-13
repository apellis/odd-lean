/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.SKM.ChevalleyGradedHom
import OddMath.SKM.ChevalleyHomDensity

/-!
# The original homwise graded Chevalley equivalence

`chevHomGradedEquivalence` is a graded superequivalence for every actual `UGr`
hom category, with original `omega` as forward map and even degree-zero unit
and counit. The explicit morphism preimage proves fullness; the packaged inverse
is choice-based, not definitionally that explicit preimage.

The coefficient ring is commutative, with the original `Scalars` and
`Scalars.Homogeneous` constraints; no field hypothesis is needed. This completes
the homwise graded equivalence prerequisite for Brundan–Ellis,
*Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §9, Proposition 9.3.
Global horizontal coherence and the shifted-envelope extension remain open.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation Supercategory GradedSupercategory
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D}
  {hc : Sc.Homogeneous}

private theorem cancel_boundary {C : Type*} [Category C] {A B U V : C}
    (p : A = B) (q : B = A) (r : U = V) (s : V = U) (f : A ⟶ U) :
    (eqToHom p ≫ eqToHom q ≫ f ≫ eqToHom r) ≫ eqToHom s = f := by
  simp [Category.assoc]

/-- The explicit preimage of an original omega morphism, using only square-boundary transport. -/
def chevHomPreimage {a b : UGr D Sc sy hc} {f g : a ⟶ b}
    (y : (chevHom a b).obj f ⟶ (chevHom a b).obj g) : f ⟶ g := by
  change (pres D Sc).obj f.obj ⟶ (pres D Sc).obj g.obj
  exact eqToHom (congrArg (pres D Sc).obj (chevObj_square f.obj)).symm ≫
    SOp.unsop (C := (pres D Sc).Presented)
      ((omega Sc).map (SOp.unsop (C := (negWeight a ⟶ negWeight b)) y)) ≫
      eqToHom (congrArg (pres D Sc).obj (chevObj_square g.obj))

theorem chevHom_map_preimage {a b : UGr D Sc sy hc} {f g : a ⟶ b}
    (y : (chevHom a b).obj f ⟶ (chevHom a b).obj g) :
    (chevHom a b).map (chevHomPreimage y) = y := by
  change (pres D Sc).Bicat at a b
  apply SOp.hom_ext
  change SOp.unsop ((omega Sc).map (chevHomPreimage y)) =
    (show (pres D Sc).obj ((chevMap D).obj g.obj) ⟶
      (pres D Sc).obj ((chevMap D).obj f.obj) from SOp.unsop (C := (negWeight a ⟶ negWeight b)) y)
  unfold chevHomPreimage
  erw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map,
    SOpMap.unsop_eqToHom_comp, SOpMap.unsop_comp_eqToHom]
  have h := chevHom_square (f := chevHomObj g) (g := chevHomObj f)
    (SOp.unsop (C := (negWeight a ⟶ negWeight b)) y)
  erw [h]
  exact cancel_boundary (C := (pres D Sc).Presented) _ _ _ _
    (SOp.unsop (C := (negWeight a ⟶ negWeight b)) y)

instance chevHom_full (a b : UGr D Sc sy hc) : (chevHom a b).Full where
  map_surjective y := ⟨chevHomPreimage y, chevHom_map_preimage y⟩

/-- Original homwise Chevalley graded equivalence, with even degree-zero unit and counit. -/
def chevHomGradedEquivalence (a b : UGr D Sc sy hc) :
    GradedSuperequivalence k (chevHom a b) :=
  GradedSuperequivalence.ofFullyFaithful (chevHom a b) (chevHom_gradedEvenlyDense a b)

end OddMath.SKM
