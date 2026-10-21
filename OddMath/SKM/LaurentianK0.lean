/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.LaurentianHoms
import OddMath.SKM.Envelope
import StringDiagrams.Super.GSKarLaurent

/-!
# Laurent bases in the completed super Kac–Moody category

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
§11, the corrected first preliminary fact used in Theorem 11.7.
Theorem 8.1 supplies degreewise finite-dimensional, bounded-below Homs.
The generic Laurentian-envelope theorem then gives an integral basis and
an `R = ℤ[q,q⁻¹]`-basis on grading-shift orbits of indecomposables.

The local-finiteness condition on symmetrizer degrees is retained from
`hom_laurentian`; it holds for finite colour sets. No Nondegeneracy
Conjecture, type-M assumption, or covering-ring freeness is asserted.
The comparison with graded left `H_n`-projectives needed in Theorem 11.3
remains separate from this completed-category result.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams GradedSupercategory
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [Field k] {Sc : Scalars D k} (sy : Symmetrizer D)
  (cs : CScalars Sc) (hc : Sc.Homogeneous) (hf : sy.DegreeLocallyFinite)

/-- Well-formed categorical words have the standard presentation at their target weight. -/
theorem UGr.homObj_normal {a b : UGr D Sc sy hc} (f : a ⟶ b) :
    f.obj = ob D b.region (f.obj.word.map Col.l) := by
  obtain ⟨hw, hs⟩ := word_eq_wd (D := D) f.obj.start f.obj.word f.wf
  change f.obj.word = wd D f.obj.endR _ at hw
  change f.obj.start = wt D f.obj.endR _ at hs
  rw [f.endR_eq] at hw hs
  exact Obj.ext hs hw

include cs hf in
/-- Theorem 8.1 supplies the exact degreewise Hom-finiteness hypothesis of
Krull–Schmidt for the completed hom categories. -/
theorem UGr.degreeHomFinite (a b : UGr D Sc sy hc) :
    GSKar.DegreeHomFinite (k := k) (C := a ⟶ b) where
  finiteDimensional f g n := by
    change FiniteDimensional k ((pres D Sc).homDeg (gdeg D sy) f.obj g.obj n)
    rw [UGr.homObj_normal sy hc f, UGr.homObj_normal sy hc g]
    exact (hom_laurentian sy Sc cs hc hf b.region _ _).1 n

include cs hf in
/-- The same spanning theorem supplies a uniform lower degree bound on each Hom-space. -/
theorem UGr.homBoundedBelow (a b : UGr D Sc sy hc) :
    GSKar.HomBoundedBelow (k := k) (C := a ⟶ b) := by
  intro f g
  change ∃ N, ∀ n < N, (pres D Sc).homDeg (gdeg D sy) f.obj g.obj n = ⊥
  rw [UGr.homObj_normal sy hc f, UGr.homObj_normal sy hc g]
  exact (hom_laurentian sy Sc cs hc hf b.region _ _).2

/-- The completed hom categories inherit the existing grading and parity shifts. -/
instance UDot.homQPiCategory (a b : UGr D Sc sy hc) :
    QPiCategory k (GSKAR.mkObj k (UGr D Sc sy hc) a ⟶ GSKAR.mkObj k (UGr D Sc sy hc) b) :=
  inferInstanceAs (QPiCategory k (GSKar k (a ⟶ b)))

include cs hf in
/-- The corrected Laurent freeness input for BE2 Theorem 11.7, on the existing
idempotent completion of the SKM 2-category. This is not freeness over ℒ. -/
theorem UDot.k0_free_laurentInt (a b : UGr D Sc sy hc) :
    letI := K₀.moduleLaurentInt k
      (GSKAR.mkObj k (UGr D Sc sy hc) a ⟶ GSKAR.mkObj k (UGr D Sc sy hc) b)
    Module.Free (LaurentPolynomial ℤ)
      (K₀ (GSKAR.mkObj k (UGr D Sc sy hc) a ⟶ GSKAR.mkObj k (UGr D Sc sy hc) b)) := by
  let := UGr.degreeHomFinite sy cs hc hf a b
  exact GSKar.k0_free_laurentInt (UGr.homBoundedBelow sy cs hc hf a b)

/-- The chosen Laurent basis consists of integer-shift orbits of indecomposables. -/
def UDot.laurentBasis (a b : UGr D Sc sy hc) :=
  letI := UGr.degreeHomFinite sy cs hc hf a b
  KrullSchmidt.laurentBasis k
    (GSKar.shiftHomBoundedBelow (UGr.homBoundedBelow sy cs hc hf a b))

#print axioms UDot.k0_free_laurentInt
#print axioms UDot.laurentBasis

end OddMath.SKM
