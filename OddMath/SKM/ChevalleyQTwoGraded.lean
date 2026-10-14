/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQTwo
import OddMath.SKM.ChevalleyQEquivalence
import StringDiagrams.Super.TwoHom

/-!
# Grading of the Chevalley involution on the `Q`-envelope

[BE2] J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §9:
`chevalleyQTwo` is graded (`chevalleyQTwo_isGraded`), surjective on objects and a local
2-superequivalence (`chevalleyQTwo_isLocalTwoSuperequivalence`).
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Supercategory GradedSupercategory TwoSupercategory
universe u v w

private theorem q_eqToHom_degree {R : Type*} [CommRing R] {C : Type*} [Category C]
    [Preadditive C] [Linear R C] [Supercategory R C] [GradedSupercategory R C]
    {A B : C} (h : A = B) : eqToHom h ∈ degree (R := R) A B 0 := by
  subst B
  exact id_mem_degree A

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D}
  {hc : Sc.Homogeneous}
local notation "F" => chevalleyQTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)

/-- The global Q-shifted action preserves total degree and has degree-zero comparisons. -/
theorem chevalleyQTwo_isGraded : (F).IsGraded where
  map₂_mem_degree {a b f g n η} h := (chevQHom_graded a.as b.as).map_mem_degree h
  mapComp_hom_mem_degree f g := by
    change eqToHom (congrArg SOp.mk (chevQObj_comp f g)).symm ∈ _
    exact q_eqToHom_degree _
  mapId_hom_mem_degree a := by
    change eqToHom (congrArg SOp.mk (chevQObj_id a)).symm ∈ _
    exact q_eqToHom_degree _

/-- The hom functors of `chevalleyQTwo` are `chevQHom`. -/
theorem chevalleyQTwo_mapFunctor (a b : QTwoEnvelope k (UGr D Sc sy hc)) :
    (F).mapFunctor a b = chevQHom a.as b.as := rfl

/-- `chevalleyQTwo` is surjective on objects. -/
theorem chevalleyQTwo_obj_surjective : Function.Surjective (F).obj := by
  intro c
  refine ⟨⟨negWeight c.unop.as⟩, ?_⟩
  apply congrArg TwoSOp.mk
  apply QTwoEnvelope.ext
  apply Presentation.Bicat.ext
  exact neg_neg (show X from c.unop.as.region)

/-- Every hom functor of `chevalleyQTwo` is a graded superequivalence. -/
def chevalleyQTwo_homGradedEquivalence (a b : QTwoEnvelope k (UGr D Sc sy hc)) :
    GradedSuperequivalence k ((F).mapFunctor a b) :=
  chevQHomGradedEquivalence a.as b.as

/-- `chevalleyQTwo` is a local 2-superequivalence. -/
theorem chevalleyQTwo_isLocalTwoSuperequivalence : (F).IsLocalTwoSuperequivalence where
  hom a b := ⟨(chevalleyQTwo_homGradedEquivalence a b).toSuperequivalence⟩
  essSurj c := by
    obtain ⟨a, ha⟩ := chevalleyQTwo_obj_surjective c
    exact ⟨a, ha.symm ▸ Superequivalent.refl c⟩
end OddMath.SKM
