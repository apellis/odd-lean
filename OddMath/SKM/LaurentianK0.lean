/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.LaurentianHoms
import OddMath.SKM.LaurentianNil
import OddMath.SKM.Envelope
import StringDiagrams.Super.GSKarLaurent

/-!
# Laurent bases in the completed super Kac–Moody category

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
§11, the corrected first preliminary fact used in Theorem 11.7.
The bubble filtration (`UGr.nilFiltration`) makes each completed hom category
`NilFinite`, and Theorem 8.1 supplies bounded-below Homs; the Laurentian-envelope
theorem modulo nil ideals then gives an integral basis and an `R = ℤ[q,q⁻¹]`-basis
on grading-shift orbits of indecomposables, for every colour set.

Degreewise finite-dimensionality of the Homs (`UGr.degreeHomFinite`) is a stronger
statement; it needs the local-finiteness condition on symmetrizer degrees of
`hom_laurentian`, which holds for finite colour sets, and is not used for the bases.
No Nondegeneracy Conjecture, type-M assumption, or covering-ring freeness is asserted.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams GradedSupercategory
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [Field k] {Sc : Scalars D k} (sy : Symmetrizer D)
  (cs : CScalars Sc) (hc : Sc.Homogeneous) (hf : sy.DegreeLocallyFinite)

include cs hf in
/-- Theorem 8.1 supplies the exact degreewise Hom-finiteness hypothesis of
Krull–Schmidt for the completed hom categories. -/
theorem UGr.degreeHomFinite (a b : UGr D Sc sy hc) :
    GSKar.DegreeHomFinite (k := k) (C := a ⟶ b) where
  finiteDimensional f g n := by
    change FiniteDimensional k ((pres D Sc).homDeg (gdeg D sy) f.obj g.obj n)
    rw [UGr.homObj_normal sy hc f, UGr.homObj_normal sy hc g]
    exact (hom_laurentian sy Sc cs hc hf b.region _ _).1 n

include cs in
/-- The spanning theorem supplies a uniform lower degree bound on each Hom-space, for every
colour set. -/
theorem UGr.homBoundedBelow (a b : UGr D Sc sy hc) :
    GSKar.HomBoundedBelow (k := k) (C := a ⟶ b) := by
  intro f g
  change ∃ N, ∀ n < N, (pres D Sc).homDeg (gdeg D sy) f.obj g.obj n = ⊥
  rw [UGr.homObj_normal sy hc f, UGr.homObj_normal sy hc g]
  exact hom_boundedBelow sy cs hc b.region _ _

include cs in
/-- The bubble filtration makes the completed hom categories `NilFinite`: the Krull–Schmidt
input of BE2 §11, for every colour set. -/
theorem UGr.nilFinite (a b : UGr D Sc sy hc) :
    KrullSchmidtNil.NilFinite k (GSKar k (a ⟶ b)) :=
  KrullSchmidtNil.GSKar.nilFinite (UGr.nilFiltration sy cs a b).toShiftBase

/-- The completed hom categories inherit the existing grading and parity shifts. -/
instance UDot.homQPiCategory (a b : UGr D Sc sy hc) :
    QPiCategory k (GSKAR.mkObj k (UGr D Sc sy hc) a ⟶ GSKAR.mkObj k (UGr D Sc sy hc) b) :=
  inferInstanceAs (QPiCategory k (GSKar k (a ⟶ b)))

include cs in
/-- The corrected Laurent freeness input for BE2 Theorem 11.7, on the existing
idempotent completion of the SKM 2-category. This is not freeness over ℒ. -/
theorem UDot.k0_free_laurentInt (a b : UGr D Sc sy hc) :
    letI := K₀.moduleLaurentInt k
      (GSKAR.mkObj k (UGr D Sc sy hc) a ⟶ GSKAR.mkObj k (UGr D Sc sy hc) b)
    Module.Free (LaurentPolynomial ℤ)
      (K₀ (GSKAR.mkObj k (UGr D Sc sy hc) a ⟶ GSKAR.mkObj k (UGr D Sc sy hc) b)) := by
  exact KrullSchmidtNil.GSKar.k0_free_laurentInt_of_graded k (UGr.nilFiltration sy cs a b)
    (UGr.homBoundedBelow sy cs hc a b)

/-- The chosen Laurent basis consists of integer-shift orbits of indecomposables. -/
def UDot.laurentBasis (a b : UGr D Sc sy hc) :=
  letI := UGr.nilFinite sy cs hc a b
  KrullSchmidtNil.laurentBasis k
    (KrullSchmidtNil.GSKar.shiftHomBoundedBelow (UGr.homBoundedBelow sy cs hc a b))

#print axioms UDot.k0_free_laurentInt
#print axioms UDot.laurentBasis

end OddMath.SKM
