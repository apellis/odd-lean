/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentDistinctMate
import OddMath.QuiverHecke.CyclotomicAction.ELVRectangularMateIso

/-! # The distinct mate isomorphism on untruncated old-content modules

Brundan–Ellis (1.12): apply the proved chosen-chart comparison and old
PBW inverse to the prescribed content cup-crossing-cap. The resulting
module inverse and input-natural inverse have crossing parity p(i)p(j).
No additional pointwise invertibility hypothesis is imposed here.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i j : I)
local notation "J" => oldContentAppend D Sc cutoff ν j
local notation "K" => oldContentAppend D Sc cutoff ν i
local notation "L" => oldContentAppend D Sc cutoff (j :: ν) i
local notation "M" => oldContentDistinctUpperAppend D Sc cutoff ν i j

end OddMath.QuiverHecke.ELVOld
