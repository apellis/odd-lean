/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.LaurentianK0
import OddMath.SKM.CliffordKrullSchmidt
import StringDiagrams.Super.GSKarLaurentParity

/-!
# The corrected mixed Laurent decomposition in BE2 §11

Apply the generic M/Q decomposition to the completed SKM hom categories used
by Theorem 11.7, retaining the same explicit Laurentian Hom hypotheses.
The degree-zero Clifford envelope is a nonzero all-type-Q consumer: parity
fixes every grading-shift orbit, and the fixed orbit set is nonempty.
The separate equivalence with graded left projectives for Theorem 11.3 is
not asserted by this envelope result.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [Field k] {Sc : Scalars D k} (sy : Symmetrizer D)
  (cs : CScalars Sc) (hc : Sc.Homogeneous) (hf : sy.DegreeLocallyFinite)

/-- The corrected ℒ-module decomposition for each completed SKM hom category. -/
def UDot.laurentDecomposition (a b : UGr D Sc sy hc) :=
  letI := UGr.degreeHomFinite sy cs hc hf a b
  GSKar.laurentDecomposition (UGr.homBoundedBelow sy cs hc hf a b)

namespace CliffordK0
variable (K : Type) [Field K]

instance degreeHomFinite : GSKar.DegreeHomFinite (k := K) (C := Cat K) where
  finiteDimensional _ _ n := (laurentian K).1 n

/-- The Clifford example satisfies the actual lower-bound hypothesis. -/
theorem homBoundedBelow : GSKar.HomBoundedBelow (k := K) (C := Cat K) :=
  fun _ _ => ⟨0, (laurentian K).2⟩

/-- The mixed decomposition on the existing Clifford projective envelope. -/
def laurentDecomposition := GSKar.laurentDecomposition (homBoundedBelow K)

/-- The regular class has nonzero coordinates in the decomposition. -/
theorem laurent_coordinates_ne_zero :
    (laurentDecomposition K).symm (K₀.mk (gradedRegular K)) ≠ 0 := by
  intro h
  have hh := congrArg (laurentDecomposition K) h
  exact gradedRegular_class_ne_zero K
    (by simpa only [LinearEquiv.apply_symm_apply, map_zero] using hh)

/-- Every grading-shift orbit of Clifford indecomposables is type Q. -/
theorem laurentParity_eq_self
    (o : KrullSchmidt.ShiftOrbit K (C := GradedProjectives K)) :
    KrullSchmidt.laurentParity K o = o := by
  induction o using Quotient.inductionOn with
  | h i =>
    apply (KrullSchmidt.laurentParity_fixed_iff K
      (GSKar.shiftHomBoundedBelow (homBoundedBelow K)) i).2
    exact ⟨(gradedProjectiveParityNatIso K).app i.rep⟩

/-- Type-Q orbit summands occur in a concrete nonzero projective category. -/
theorem typeQ_orbits_nonempty :
    Nonempty (CoveringLaurent.FixedRep (KrullSchmidt.laurentParity K (C := GradedProjectives K))) := by
  obtain ⟨i⟩ := (indecBasis K).index_nonempty
  exact ⟨⟨Quotient.mk _ i, laurentParity_eq_self K _⟩⟩

#print axioms laurentDecomposition
#print axioms laurent_coordinates_ne_zero
#print axioms typeQ_orbits_nonempty
end CliffordK0

#print axioms UDot.laurentDecomposition
end OddMath.SKM
