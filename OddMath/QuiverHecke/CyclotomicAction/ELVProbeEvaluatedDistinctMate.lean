import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCanonicalContent
import OddMath.QuiverHecke.CyclotomicAction.ELVContentDistinctIso

/-! # Distinct mates on the scalar-evaluated OLD probe

Brundan–Ellis Definition 1.5, (1.12): restrict the prescribed OLD
cup-crossing-cap and its constructed PBW inverse through the full evaluated
module subcategories. The upper append uses its given common target list.
Both inverse identities and all input-map parity signs are retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction
open CyclotomicAction
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
local notation "S" => probeEvaluatedRestriction D Sc m ν j ⋙ probeEvaluatedInduction D Sc m ν i
local notation "T" => probeEvaluatedInduction D Sc m (j :: ν) i ⋙
  probeEvaluatedRestrictTo D Sc m (i :: ν) j (i :: j :: ν) (List.Perm.swap i j ν)
local notation "P" => ProbeEvaluatesCoefficients D m Sc (j :: ν)
local notation "Q" => ProbeEvaluatesCoefficients D m Sc (i :: ν)

end OddMath.QuiverHecke
