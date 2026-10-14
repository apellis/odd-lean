/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQPiForwardTriangle
import OddMath.SKM.ChevalleyQPiReverseTriangle

/-!
# The Chevalley involution `ω̃` is an adjoint biequivalence

[BE2] J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Proposition
9.3: the graded 2-superfunctor `ω̃ : 𝔘_{q,π}(𝔤) → 𝔘_{q,π}(𝔤)^{sop}` (`chevalleyQPiTwo`) is an
isomorphism.

The paper calls `ω̃` an isomorphism. This file proves the adjoint biequivalence reading of that
word (`chevalleyQPiTwo_isAdjointBiequivalence`). The data are:
* the inverse graded 2-superfunctor `G̃ = chevalleyQPiReverseTwo`;
* the unit `J̃ : 1 ⟹ ω̃ ⋙ G̃` (`chevalleyQPiGlobalUnit`) and the counit `Ẽ : G̃ ⋙ ω̃ ⟹ 1`
  (`chevalleyQPiGlobalCounit`). Both are strong graded 2-natural transformations with strong
  graded inverses, up to invertible modifications that are even of degree zero;
* both triangle identities, up to invertible modifications that are even of degree zero
  (`chevalleyQPiForwardTriangleIso`, `chevalleyQPiReverseTriangleIso`).

A strict inverse, with `ω̃ ⋙ G̃` and `G̃ ⋙ ω̃` equal to identity 2-superfunctors, is not
constructed. `ω̃` is not strict: its composition comparison carries the sign `(-1)^{ab}`
(`chevalleyQPiTwo_mapComp`).
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

/-- [BE2] Proposition 9.3, adjoint biequivalence reading: `ω̃` with inverse `G̃`, unit `J̃`
and counit `Ẽ` is an adjoint biequivalence of graded 2-supercategories. -/
theorem chevalleyQPiTwo_isAdjointBiequivalence :
    TwoSuperfunctor.IsAdjointBiequivalence
      (chevalleyQPiTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)) chevalleyQPiReverseTwo
      chevalleyQPiGlobalUnit chevalleyQPiGlobalCounit where
  left_isGraded := chevalleyQPiTwo_isGraded
  right_isGraded := chevalleyQPiReverseTwo_isGraded
  unit_isStrong := chevalleyQPiGlobalUnit_isStrong
  unit_isGraded := chevalleyQPiGlobalUnit_isGraded
  counit_isStrong := chevalleyQPiGlobalCounit_isStrong
  counit_isGraded := chevalleyQPiGlobalCounit_isGraded
  unit_invertible := ⟨chevalleyQPiGlobalUnitInv, chevalleyQPiGlobalUnitInv_isStrong,
    chevalleyQPiGlobalUnitInv_isGraded, ⟨qPiUnitCancel⟩, ⟨qPiUnitInvCancel⟩⟩
  counit_invertible := ⟨chevalleyQPiGlobalCounitInv, chevalleyQPiGlobalCounitInv_isStrong,
    chevalleyQPiGlobalCounitInv_isGraded, ⟨qPiCounitCancel⟩, ⟨qPiCounitInvCancel⟩⟩
  left_triangle := ⟨qPiForwardTriangle⟩
  right_triangle := ⟨qPiReverseTriangle⟩
end OddMath.SKM
