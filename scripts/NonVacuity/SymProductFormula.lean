import OddMath

/-! Consumers of `OddMath/SKM/SymProductFormula.lean` and of the composed (dum) headline in
`OddMath/QuiverHecke/HomBases.lean`, on the two-odd-colour datum over `ℚ` with constant
parameters, for both signs `σ = ±1`. -/
noncomputable section
namespace SymProductFormulaConsumer
open CategoryTheory OddMath OddMath.SKM OddMath.CoveringQuantum
open OddMath.SKM.DimensionFormulaExamples
open OddMath.SKM.Theorem103Examples
open OddMath.CoveringQuantum.UDot.ContextualExchangeExamples
open OddMath.CoveringQuantum.UDot.GenericTensor
open OddMath.CoveringQuantum.UDot.GenericVerma.MixedGram
open scoped PowerSeries.WithPiTopology

/-- A generic product: degree-one even factors and a degree-two odd factor. -/
example : HasProd (Sum.elim (fun _ : Unit => MonomialSeries.geomSeries (R := ℚ) 1)
    (fun _ : Unit => 1 + PowerSeries.C (-1 : ℚ) * PowerSeries.X ^ 2))
    (MonomialSeries.monomialSeries (fun _ : Unit => 1) (fun _ : Unit => 2) (-1 : ℚ)) :=
  MonomialSeries.hasProd_monomialSeries _ _ (fun _ => one_pos) (fun _ => two_pos)
    (fun _ => Set.toFinite _) (-1) (by norm_num)

example : HasProd (symFactor twoOddDatum.skmSymmetrizer (-1))
    (symPowerSeries twoOddDatum.skmSymmetrizer ℚ (-1)) :=
  hasProd_symFactor twoOddDatum.skmSymmetrizer ℚ locallyFinite (-1) (by norm_num)

example : symDimension twoOddDatum.skmSymmetrizer ℚ 1 =
    ((∏' g, symFactor twoOddDatum.skmSymmetrizer 1 g : PowerSeries ℚ) : LaurentSeries ℚ) :=
  symDimension_eq_tprod twoOddDatum.skmSymmetrizer ℚ locallyFinite 1 (by norm_num)

example (μ : Bool → ℤ) :
    homDimension twoOddDatum.skmSymmetrizer cScalars homogeneous locallyFinite
      μ (boundary true) (boundary true) (-1) =
      signLaurent (-1) (by norm_num) (sesquilinearForm twoOddDatum
        (algebraWord twoOddDatum μ (boundary true)) (algebraWord twoOddDatum μ (boundary true))) *
      ((∏' g, symFactor twoOddDatum.skmSymmetrizer (-1) g : PowerSeries ℚ) :
        LaurentSeries ℚ) :=
  QuiverHecke.homDimension_eq_form_mul_tprod_symFactor twoOddDatum (by norm_num) homogeneous
    cScalars locallyFinite μ (boundary true) (boundary true) rfl (-1) (by norm_num)

#print axioms OddMath.SKM.MonomialSeries.hasProd_monomialSeries
#print axioms OddMath.SKM.hasProd_symFactor
#print axioms OddMath.SKM.symDimension_eq_tprod
#print axioms OddMath.QuiverHecke.homDimension_eq_form_mul_tprod_symFactor

end SymProductFormulaConsumer
