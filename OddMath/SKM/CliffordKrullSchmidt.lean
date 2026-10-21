import OddMath.SKM.CliffordK0
import StringDiagrams.Super.KrullSchmidtParity

/-!
# Krull–Schmidt and the Clifford parity obstruction

Consumers of the corrected parity-ring part of BE2, arXiv:1701.04133v2,
§11 opening (ERRATA [BE2] 10). The integral indecomposable basis is derived
for the same graded Clifford projective envelope as `CliffordK0`; it is not
an extra premise. This supplies a second obstruction to covering-ring
freeness, via a nonzero parity-fixed class modulo norms.

The general Laurentian orbit theorem remains separate: these results do not
construct a basis modulo integer grading shifts.
-/

noncomputable section
namespace OddMath.SKM.CliffordK0
open CategoryTheory StringDiagrams

variable (K : Type) [Field K]

instance homFinite : KrullSchmidt.HomFinite K (GradedProjectives K) where
  finiteDimensional _ _ := inferInstance

/-- The indecomposable integral basis on the existing graded Clifford split K₀. -/
def indecBasis : Module.Basis (KrullSchmidt.IndecClass (GradedProjectives K)) ℤ
    (K₀ (GradedProjectives K)) := KrullSchmidt.indecBasis K

@[simp] theorem indecBasis_apply (i : KrullSchmidt.IndecClass (GradedProjectives K)) :
    indecBasis K i = K₀.mk i.rep := KrullSchmidt.indecBasis_apply K i

/-- The concrete nonzero regular class forces an indecomposable summand. -/
theorem exists_indecomposable :
    ∃ P : GradedProjectives K, KrullSchmidt.IsIndec P := by
  obtain ⟨i⟩ := (indecBasis K).index_nonempty
  exact ⟨i.rep, i.isIndec_rep⟩

/-- The corrected parity-ring criterion detects the Clifford counterexample. -/
theorem gradedK0_not_free_zpi :
    letI := K₀.moduleZπ K (GradedProjectives K)
    ¬ Module.Free Zπ (K₀ (GradedProjectives K)) := by
  obtain ⟨P, hP⟩ := exists_indecomposable K
  exact KrullSchmidt.not_free_of_parity_iso K hP
    ((gradedProjectiveParityNatIso K).app P)

/-- Some indecomposable class is fixed by parity but is not a norm. In contrast,
every parity-fixed element of a free parity-ring module is a norm. -/
theorem exists_indecomposable_not_norm :
    letI := K₀.moduleZπ K (GradedProjectives K)
    ∃ P : GradedProjectives K, KrullSchmidt.IsIndec P ∧
      ¬ ∃ y : K₀ (GradedProjectives K), y + Zπ.π • y = K₀.mk P := by
  obtain ⟨P, hP⟩ := exists_indecomposable K
  exact ⟨P, hP, KrullSchmidt.indec_not_norm K hP
    ((gradedProjectiveParityNatIso K).app P)⟩

end OddMath.SKM.CliffordK0
