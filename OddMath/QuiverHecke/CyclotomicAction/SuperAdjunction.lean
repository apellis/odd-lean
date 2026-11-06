/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.SuperAdjunctionCounit

/-!
# The cyclotomic super adjunction

Ports the induction-restriction adjunction of
`Categorification/TwoRep/CyclotomicRouqAdjunction.lean` to the actual
cyclotomic supermodule categories. The unit and counit are even and their
naturality includes odd morphisms.
-/

noncomputable section
open CategoryTheory StringDiagrams
open SuperBimodule
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i : I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)
local notation "φ" => cyclotomicAppend D Sc i a n
local notation "P" => inductionCorner D Sc i a ha n
local notation "Q" => restrictionCorner D Sc i a ha n
local notation "F" => cyclotomicSuperInduction D Sc i a ha n
local notation "E" => cyclotomicSuperRestriction D Sc i a ha n

end OddMath.QuiverHecke
