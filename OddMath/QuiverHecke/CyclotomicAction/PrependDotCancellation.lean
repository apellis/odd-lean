/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.PrependCoefficientCoordinates
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerContentDot

/-!
# Moving-dot square cancellation in prepend coordinates

The degree-two raising and cancellation step of `PrependCoordinates.md`,
used in the repeated-colour QP argument. The square of the existing right
dot is conjugated through the additive balanced coordinates; the finite
support proof permits every right cyclotomic coefficient. No flatness,
monicity, even polynomial support, or coefficient-domain hypothesis is used.
This does not identify an odd linear difference with its square or prove QP.
-/

noncomputable section
open Categorification
namespace OddMath.QuiverHecke

/-- Raising the polynomial exponent by two, with all shuffle indices retained. -/
def prependRaiseTwo {J M : Type*} [AddCommGroup M] :
    (J × ℕ →₀ M) →+ (J × ℕ →₀ M) :=
  Finsupp.embDomain.addMonoidHom
    ⟨fun q => (q.1, q.2 + 2), by intro x y h; cases x; cases y; simp_all⟩

@[simp] theorem prependRaiseTwo_single {J M : Type*} [AddCommGroup M]
    (q : J × ℕ) (y : M) :
    prependRaiseTwo (Finsupp.single q y) = Finsupp.single (q.1, q.2 + 2) y :=
  Finsupp.embDomain_single _ _ _

@[simp] theorem prependRaiseTwo_apply {J M : Type*} [AddCommGroup M]
    (f : J × ℕ →₀ M) (j : J) (m : ℕ) :
    prependRaiseTwo f (j, m + 2) = f (j, m) :=
  Finsupp.embDomain_apply_self _ _ (j, m)

universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

variable (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
  (ha : CyclotomicPolynomialParity D a) (r : ℕ)
local notation "M" => (StringDiagrams.SuperBimodule.toSVec (qCoefficient D Sc i β a ha r))
local notation "T" => InductionAlong.Ind M (prependAlgebra D Sc i (r+1) :
  Hn D Sc (r+1) →ₙ+* Hn D Sc (r+1+1))

end OddMath.QuiverHecke
