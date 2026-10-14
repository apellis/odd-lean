/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQReverseComparisonAssociator

/-!
# The inverse 2-superfunctor of `ω_q`

`chevalleyQReverseTwo : 𝔘_q(𝔤)^{sop} → 𝔘_q(𝔤)`, a graded 2-superfunctor with `λ ↦ -λ` on objects. It is the inverse 2-superfunctor in the adjoint biequivalence of `ω_q`.

Part of the adjoint biequivalence reading of [BE2] J. Brundan, A. P. Ellis,
*Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Proposition 9.3.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Supercategory GradedSupercategory
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D}
  {hc : Sc.Homogeneous}

/-- The reverse Q action, with all horizontal coherence fields proved. -/
def chevalleyQReverseTwo :
    TwoSuperfunctor k (TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc)))
      (QTwoEnvelope k (UGr D Sc sy hc)) where
  obj := chevalleyQReverseObj
  map {a b} := (chevalleyQReverseHom a b).obj
  map₂ {a b} := (chevalleyQReverseHom a b).map
  map₂_id {a b} := (chevalleyQReverseHom a b).map_id
  map₂_comp {a b} := (chevalleyQReverseHom a b).map_comp
  map₂_add η θ := by rw [Functor.map_add]
  map₂_smul s η := by rw [Functor.map_smul]
  map₂_mem h := chevalleyQReverseHom_mem_parity h
  mapComp := chevalleyQReverseMapComp
  mapId := chevalleyQReverseMapId
  mapComp_hom_mem := chevalleyQReverseMapComp_even
  mapId_hom_mem := chevalleyQReverseMapId_even
  mapComp_naturality_left := chevalleyQReverseMapComp_naturality_left
  mapComp_naturality_right := chevalleyQReverseMapComp_naturality_right
  map₂_associator := chevalleyQReverse_associator
  map₂_leftUnitor := chevalleyQReverse_leftUnitor
  map₂_rightUnitor := chevalleyQReverse_rightUnitor

/-- The reverse bundle preserves arbitrary degree and has degree-zero comparisons. -/
theorem chevalleyQReverseTwo_isGraded :
    (chevalleyQReverseTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc) (k := k)).IsGraded where
  map₂_mem_degree h := chevalleyQReverseHom_mem_degree h
  mapComp_hom_mem_degree := chevalleyQReverseMapComp_degree
  mapId_hom_mem_degree := chevalleyQReverseMapId_degree
end OddMath.SKM
