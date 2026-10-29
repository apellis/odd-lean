/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Action
import OddMath.QuiverHecke.SwappedAssembly.Supernatural.CrossCoeff
import OddMath.QuiverHecke.SwappedAssembly.Supernatural.Leftward

/-! # The super interchange law of the swapped generators from the inverse relations

The field `SwappedRelationData.supernatural` (the super interchange law for the swapped
generator images, `GeneratorsSupernatural`) follows from the other fields of
`SwappedRelationData`: the distinct-colour sideways crossings have permutation matrices with
invertible entries (`sigma`), the equal-colour leftward data invert the augmented maps
(`leftward`), and the coefficient `a` of the equal-colour mixed block is supernatural. The
last holds when `a` satisfies its characterizing identities `CrossCoeff.IsInverse` and the
denominators are invertible (`CrossCoeffInputs`), in particular for `crossCoeffOfInputs`.

## Main results

* `ProbeReservoir.swappedGens_supernatural_of_isInverse`.
* `ProbeReservoir.SwappedRelationData.ofIsInverse`: `SwappedRelationData` without the
  interchange-law field.
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams Supercategory OddMath.SKM BicategoryStruct

universe u

variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

namespace ProbeReservoir

variable {P : ProbeReservoir k B D Sc}

/-- **The swapped generator images are supernatural** when the sideways crossings for
distinct colours have permutation matrices with invertible entries, the leftward data invert
the augmented maps, and the mixed-block coefficient satisfies its characterizing identities
with invertible denominators. -/
theorem swappedGens_supernatural_of_isInverse (c : P.CrossCoeff) (L : P.LeftwardData)
    (hin : P.CrossCoeffInputs) (hc : c.IsInverse)
    (hσ : ∀ i j : I, i ≠ j → ∀ ν : X, P.SigmaPermutation c i j ν) (hL : L.IsInverse c) :
    GeneratorsSupernatural (P.swappedGens c L) :=
  have hcs := CrossCoeff.isSupernatural_of_isInverse P c hc hin
  P.swappedGens_supernatural c L hcs hσ (L.isSupernatural_of_isInverse c hcs hL)

/-- **`SwappedRelationData` without the interchange-law field**: the super interchange law
`GeneratorsSupernatural` is a consequence of `sigma`, `leftward` and the characterizing
identities of the mixed-block coefficient with invertible denominators. -/
theorem SwappedRelationData.ofIsInverse {c : P.CrossCoeff} {L : P.LeftwardData}
    (hin : P.CrossCoeffInputs) (hc : c.IsInverse)
    (quad : CrossQuad (P.swappedGens c L)) (slide : CrossSlide (P.swappedGens c L))
    (braid : CrossBraid (P.swappedGens c L)) (zigzag : CupCapZigzag (P.swappedGens c L))
    (sigma : ∀ i j ν, i ≠ j → P.SigmaPermutation c i j ν) (leftward : L.IsInverse c)
    (windowZero : DcupDcapWindowZero (P.swappedGens c L)) : P.SwappedRelationData c L where
  quad := quad
  slide := slide
  braid := braid
  zigzag := zigzag
  sigma := sigma
  leftward := leftward
  windowZero := windowZero
  supernatural := swappedGens_supernatural_of_isInverse c L hin hc
    (fun i j hij ν => sigma i j ν hij) leftward

/-- The coefficient built from `CrossCoeffInputs` needs no further hypothesis. -/
theorem SwappedRelationData.ofCrossCoeffInputs (hin : P.CrossCoeffInputs) {L : P.LeftwardData}
    (quad : CrossQuad (P.swappedGens (P.crossCoeffOfInputs hin) L))
    (slide : CrossSlide (P.swappedGens (P.crossCoeffOfInputs hin) L))
    (braid : CrossBraid (P.swappedGens (P.crossCoeffOfInputs hin) L))
    (zigzag : CupCapZigzag (P.swappedGens (P.crossCoeffOfInputs hin) L))
    (sigma : ∀ i j ν, i ≠ j → P.SigmaPermutation (P.crossCoeffOfInputs hin) i j ν)
    (leftward : L.IsInverse (P.crossCoeffOfInputs hin))
    (windowZero : DcupDcapWindowZero (P.swappedGens (P.crossCoeffOfInputs hin) L)) :
    P.SwappedRelationData (P.crossCoeffOfInputs hin) L :=
  .ofIsInverse hin (P.crossCoeffOfInputs_isInverse hin) quad slide braid zigzag sigma leftward
    windowZero

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
