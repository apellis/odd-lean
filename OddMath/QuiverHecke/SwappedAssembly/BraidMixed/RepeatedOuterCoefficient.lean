/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentReverseCoefficient
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.SignedCoefficientTransport

/-! # A single probe crossing in the repeated-outer braid

For the path `Rᵢ Pⱼ Pᵢ`, the equal-pair coefficient is transported from
`Pⱼ Rᵢ Pᵢ` by the mixed comparison. Its normalization includes the Koszul
sign. The single unequal probe crossing carries this coefficient with that
sign. This is a consequence of the proved dot slides and inverse denominator
identities, not a braid hypothesis. Neither this crossing nor Q is inverted.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory
universe u
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
namespace ProbeReservoir
variable (P : ProbeReservoir k B D Sc) (c : P.CrossCoeff Sc)
  (i j : I) (s : Sector I) (hR : StepValid (true, i) false s)
  (hs : nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)) =
    nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s)))
  (Z : P.H (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))))

/-- The normalized coefficient on the separated equal strands `Rᵢ Pⱼ Pᵢ`. -/
def repeatedOuterProbeCoeff :=
  zsign k (D.parity i * D.parity j) •
    ((P.mixedJ j i s hR ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z))).inv ≫
      (P.step (true, j) true s trivial).map
        (c.a i (nextSector (true, j) true s) hR ((P.castH hs).obj Z)) ≫
      (P.mixedJ j i s hR ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z))).hom)

/-- The actual single unequal probe crossing transports the separated
coefficient with its Koszul sign. The underlying two dot signs and denominator
cancellation are supplied by `adjacentReverseMove_coeff`. -/
theorem repeatedOuterProbeCross_coeff (hc : c.IsInverse) (h : P.CrossCoeffInputs)
    (hij : i ≠ j) :
    (P.step (true, i) false s hR).map
        (P.preCrossNe j i (nextSector (true, i) false s) hs Z) ≫
      c.a i s hR ((P.step (true, j) true _ trivial).obj Z) =
    zsign k (D.parity i * D.parity j) •
      (P.repeatedOuterProbeCoeff c i j s hR hs Z ≫
        (P.step (true, i) false s hR).map
          (P.preCrossNe j i (nextSector (true, i) false s) hs Z)) := by
  let J := P.mixedJ j i s hR
    ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z))
  have he := P.adjacentReverseMove_coeff c hc h i j s hR hs Z hij
  have he' := congrArg (fun f => J.inv ≫ f) he
  dsimp only [adjacentReverseMove, J] at he'
  simp only [Category.assoc, Iso.inv_hom_id_assoc] at he'
  simpa only [repeatedOuterProbeCoeff, Linear.smul_comp, smul_smul,
    zsign_mul_self', one_smul, Category.assoc] using he'.symm

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
