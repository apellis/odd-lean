/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.InductionFunctorComparison
import OddMath.QuiverHecke.CyclotomicAction.SuperCrossing
import StringDiagrams.Super.Functor

/-!
# The crossing on composed cyclotomic superinduction

Ports the crossing of `Categorification/KLR/CyclotomicAction/Induction.lean`
through the even comparison of `CyclotomicAction/Comparison.lean`.
The transformation below is obtained from `compositionSuperCrossing`, not from
an assumed crossing operator. Only its parity and supernatural naturality are
asserted; no square, braid, inversion or KKO relations are asserted.
-/

noncomputable section
open CategoryTheory StringDiagrams SuperBimodule Supercategory
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i j : I) (a : I → _root_.Polynomial k)
  (ha : CyclotomicPolynomialParity D a) (n : ℕ)
local notation "P" => compositionCorner D Sc i j a ha n
local notation "Q" => compositionCorner D Sc j i a ha n
local notation "F" => cyclotomicSuperInduction D Sc j a ha n ⋙
  cyclotomicSuperInduction D Sc i a ha (n + 1)
local notation "G" => cyclotomicSuperInduction D Sc i a ha n ⋙
  cyclotomicSuperInduction D Sc j a ha (n + 1)
local notation "d" => D.parity i * D.parity j
local notation "e" => inductionFunctorComparison D Sc i j a ha n
local notation "e'" => inductionFunctorComparison D Sc j i a ha n

end OddMath.QuiverHecke
