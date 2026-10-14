/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQHom
import OddMath.SKM.ChevalleyHomEquivalence

/-!
# The Chevalley involution on `Q`-shifted hom categories is an equivalence

[BE2] J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Proposition
3.5 and §9: each hom functor `chevQHom a b` is fully faithful and surjective on objects, hence a
graded superequivalence (`chevQHomGradedEquivalence`).
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Supercategory GradedSupercategory
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D}
  {hc : Sc.Homogeneous}

instance chevQHom_faithful (a b : UGr D Sc sy hc) : (chevQHom a b).Faithful where
  map_injective {f g} {η θ} h := by
    apply (chevHom a b).map_injective
    apply SOp.hom_ext
    exact congrArg (fun x => QEnvelope.toHom (SOp.unsop x)) h

instance chevQHom_full (a b : UGr D Sc sy hc) : (chevQHom a b).Full where
  map_surjective {f g} η := by
    let y : (chevHom a b).obj f.obj ⟶ (chevHom a b).obj g.obj :=
      SOp.mk' (QEnvelope.toHom (SOp.unsop η))
    refine ⟨QEnvelope.ofHom (chevHomPreimage y), ?_⟩
    apply SOp.hom_ext
    exact congrArg (SOp.unsop (C := (negWeight a ⟶ negWeight b))) (chevHom_map_preimage y)

/-- Surjectivity on objects, using double negation of the shift. -/
theorem chevQHom_obj_surjective (a b : UGr D Sc sy hc) :
    Function.Surjective (chevQHom a b).obj := by
  intro Y
  refine ⟨⟨-Y.unop.shift, chevHomObjectPreimage (SOp.mk Y.unop.obj)⟩, ?_⟩
  apply SOp.ext
  apply QEnvelope.ext
  · exact neg_neg Y.unop.shift
  · exact congrArg SOp.unop (chevHom_obj_preimage (SOp.mk Y.unop.obj))

/-- Each shifted target admits an even degree-zero equality isomorphism from an image. -/
theorem chevQHom_gradedEvenlyDense (a b : UGr D Sc sy hc) :
    GradedEvenlyDense k (chevQHom a b) := by
  intro Y
  obtain ⟨f, hf⟩ := chevQHom_obj_surjective a b Y
  subst Y
  exact ⟨f, Iso.refl _, id_mem _, id_mem_degree _⟩

/-- Each `Q`-shifted hom functor of `ω` is a graded superequivalence. -/
def chevQHomGradedEquivalence (a b : UGr D Sc sy hc) :
    GradedSuperequivalence k (chevQHom a b) :=
  GradedSuperequivalence.ofFullyFaithful (chevQHom a b) (chevQHom_gradedEvenlyDense a b)
end OddMath.SKM
