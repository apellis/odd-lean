/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.CornerPairing

/-!
# The unit of cyclotomic super induction and restriction

Ports the unit construction of
`Categorification/TwoRep/CyclotomicRouqAdjunction.lean` using genuine balanced
super tensor products. Both inserted colour idempotents are even.
-/

noncomputable section
open CategoryTheory StringDiagrams
open SuperBimodule
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i : I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)

local notation "A" => CyclotomicAlgebra D Sc a n
local notation "B" => CyclotomicAlgebra D Sc a (n + 1)
local notation "φ" => cyclotomicAppend D Sc i a n
local notation "P" => inductionCorner D Sc i a ha n
local notation "Q" => restrictionCorner D Sc i a ha n
local notation "ep" => inductionCornerIdempotent D Sc i a ha n
local notation "eq" => restrictionCornerOf D Sc i a ha n 1

end OddMath.QuiverHecke
