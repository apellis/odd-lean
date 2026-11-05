import OddMath.QuiverHecke.CyclotomicAction.ELVProbeEvaluatedDistinctMate
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendToAdjunction
import OddMath.QuiverHecke.CyclotomicAction.ELVPiSCatRectangularMate
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightCrossMate

/-! # The positive distinct crossing and its evaluated OLD mate

Brundan–Ellis Definition 1.5, (1.12): the chosen positive rectangular
crossing restricts to scalar-evaluated OLD modules. Bending it by the
specified lower and upper right adjunctions gives the already constructed
evaluated OLD mate. The append flattenings and both bending maps are kept.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (ν : List I) (i j : I)
local notation "cut" => probeCutoff D m
local notation "J" => oldContentAppend D Sc cut ν j
local notation "K" => oldContentAppend D Sc cut ν i
local notation "L" => oldContentAppend D Sc cut (j :: ν) i
local notation "M" => oldContentDistinctUpperAppend D Sc cut ν i j
local notation "hCross" => oldContentDistinctCross_supernatural D Sc cut ν i j
local notation "P" => ProbeEvaluatesCoefficients D m Sc ν
local notation "Q" => ProbeEvaluatesCoefficients D m Sc (i :: j :: ν)
local notation "Ei" => probeEvaluatedE D Sc m ν i
local notation "Ej" => probeEvaluatedE D Sc m ν j
local notation "V" => probeEvaluatedE D Sc m (j :: ν) i
local notation "U" => probeAppendToE D Sc m (i :: ν) j (i :: j :: ν) (List.Perm.swap i j ν)
local notation "A" => probeEvaluatedRightAdjunction D Sc m ν j
local notation "B" => probeAppendToRightAdjunction D Sc m (i :: ν) j (i :: j :: ν)
  (List.Perm.swap i j ν)

end OddMath.QuiverHecke
