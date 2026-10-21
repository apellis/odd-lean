import OddMath
import OddMath.SKM.CliffordKrullSchmidt

noncomputable section
open StringDiagrams OddMath.SKM.CliffordK0

example : Module.Basis (KrullSchmidt.IndecClass (GradedProjectives ℚ)) ℤ
    (K₀ (GradedProjectives ℚ)) := indecBasis ℚ

example : ∃ P : GradedProjectives ℚ, KrullSchmidt.IsIndec P :=
  exists_indecomposable ℚ

example :
    letI := K₀.moduleZπ ℚ (GradedProjectives ℚ)
    ¬ Module.Free Zπ (K₀ (GradedProjectives ℚ)) := gradedK0_not_free_zpi ℚ

example :
    letI := K₀.moduleZπ ℚ (GradedProjectives ℚ)
    ∃ P : GradedProjectives ℚ, KrullSchmidt.IsIndec P ∧
      ¬ ∃ y : K₀ (GradedProjectives ℚ), y + Zπ.π • y = K₀.mk P :=
  exists_indecomposable_not_norm ℚ

#print axioms indecBasis
#print axioms exists_indecomposable
#print axioms gradedK0_not_free_zpi
#print axioms exists_indecomposable_not_norm
