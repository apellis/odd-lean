import OddMath.QuiverHecke.CoefficientExtension
import OddMath.QuiverHecke.Positional

noncomputable section
open CategoryTheory StringDiagrams OddMath.QuiverHecke
open scoped Classical TensorProduct
variable {I X k : Type} [AddCommGroup X] [CommRing k]
  (D : OddMath.SKM.Datum I X) (Sc : OddMath.SKM.Scalars D k)

private def oneDot (i : I) := cl D Sc [i] [i] [.dot 0] (sChain_pl _ _)

private theorem oneDot_odd (i : I) (hi : D.parity i = 1) :
    oneDot D Sc i ∈ Supercategory.parity (R := k) _ _ 1 := by
  apply Presentation.diag_mem_homDeg'
  rw [degree_parity_mkD]
  simp [pl, PG.ld, Shape.parity, hi]

/-- The actual odd upward dot picks up the Koszul sign across an independent odd coefficient. -/
example (i j : {i : I // D.parity i = 1}) :
    sourceCoefficientHom D Sc (OddMath.SKM.SYM.delta D k i) (𝟙 ((pres D Sc).obj (ob D [j.1]))) ≫
      sourceCoefficientHom D Sc 1 (oneDot D Sc j.1) =
      -sourceCoefficientHom D Sc (OddMath.SKM.SYM.delta D k i) (oneDot D Sc j.1) := by
  simpa using odd_coefficient_comp_odd D Sc i (𝟙 _) (oneDot_odd D Sc j.1 j.2)

#print axioms OddMath.SKM.SYM.polynomialExteriorGradedAlgebra
#print axioms coefficientHom_comp
#print axioms odd_coefficient_comp_odd
#print axioms sourceTensorEquiv
