import OddMath.SKM.BubbleExterior

noncomputable section
open OddMath.SKM
variable {I X k : Type} [AddCommGroup X] [CommRing k] (D : Datum I X)

/-- Retraction preserves products of distinct generators as exterior words. -/
example (i j : {i : I // D.parity i = 1}) :
    SYM.exteriorProjection D k (SYM.delta D k i * SYM.delta D k j) =
      ExteriorAlgebra.ι k (Finsupp.single i 1 : SYM.OddModule D k) *
      ExteriorAlgebra.ι k (Finsupp.single j 1 : SYM.OddModule D k) := by
  simp

/-- Injectivity is on the entire exterior algebra, not merely its generating space. -/
example (x y : ExteriorAlgebra k (SYM.OddModule D k))
    (h : SYM.exteriorInclude D k x = SYM.exteriorInclude D k y) : x = y :=
  SYM.exteriorInclude_injective D k h

#print axioms SYM.oddLinear_sq_zero
#print axioms SYM.exteriorProjection_comp_include
#print axioms SYM.exteriorInclude_injective
