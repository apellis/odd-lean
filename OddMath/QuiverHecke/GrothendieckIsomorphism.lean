/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.Surjectivity
import OddMath.QuiverHecke.Injectivity
import OddMath.SKM.GroundRingNondegeneracy

/-!
# `K₀` of the Karoubi envelope is the integral covering `U̇`

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Theorem 11.7 and
Theorem 12.1: the homomorphism `γ : U̇_{q,π}(𝔤)_ℒ → K₀(𝔘̇(𝔤))` of Theorem 11.7 is surjective
(Theorem 11.7) and, if the Nondegeneracy Conjecture holds, injective (Theorem 12.1). Together
they make `γ` an isomorphism of `ℒ`-algebras, `ℒ = ℤπ[q, q⁻¹]`, between the integral form of
the covering modified quantum group and the split Grothendieck ring of the graded Karoubi
envelope `𝔘̇(𝔤)`. By (11.2) that envelope is equivalent to the category of finitely
generated graded projective right supermodules over the Hom-matrix algebra
(`FiniteHomMatrix.gsKarFunctor_essImage_iff`); the ring here is the split Grothendieck ring of
the envelope itself (`SKM.K0Relations.Grothendieck`).

## Main results

* `SerreComplex.gammaInt_bijective`: `γ` is bijective, given the Nondegeneracy Conjecture.
* `SerreComplex.gammaIntEquiv`: the resulting ring isomorphism, `ℒ`-linear by
  `gammaIntEquiv_smul`.
* `SerreComplex.gammaInt_bijective_of_charZeroField`: the same with the conjecture replaced by
  its field case `SKM.CharZeroFieldNondegeneracy` (for every field of characteristic zero),
  over every ground field of characteristic not `2`, through the ground-ring descent
  `SKM.nondegeneracyConjecture_of_charZeroField`.

## Hypotheses

The hypotheses are those of `theorem_11_7_surjective` and `theorem_12_1`: a ground field, the
scalar hypotheses of §9 (`Homogeneous`), the route hypothesis `DegreeLocallyFinite` of
Theorem 11.7, and, for nondegeneracy of the form of Theorem 10.1, finitely many colours, a
finitely generated free weight lattice and linearly independent roots and coroots. The
Nondegeneracy Conjecture (or its characteristic-zero field case) is a hypothesis; it is not
proved here.
-/

noncomputable section

namespace OddMath.QuiverHecke.SerreComplex

open CoveringQuantum CoveringQuantum.UDot LaurentPolynomial

variable {I X : Type*} [AddCommGroup X] {k : Type*} [Field k]
variable (Q : CoveringQuantum.RootDatum I X) {S : SKM.Scalars Q.toSKM k} (hS : S.Homogeneous)
  (cs : SKM.CScalars S) (hf : Q.skmSymmetrizer.DegreeLocallyFinite)
variable [Finite I] [Module.Free ℤ X] [Module.Finite ℤ X]

/-- **BE2 Theorems 11.7 and 12.1**: given the Nondegeneracy Conjecture, `γ` is bijective. -/
theorem gammaInt_bijective (hN : SKM.NondegeneracyConjecture cs)
    (hα : LinearIndependent ℤ Q.α) (hh : LinearIndependent ℤ Q.cd.coroot) :
    Function.Bijective (gammaInt Q hS cs hf) :=
  ⟨theorem_12_1 Q hS cs hf hN hα hh, theorem_11_7_surjective Q hS cs hf⟩

/-- **`K₀(𝔘̇(𝔤)) ≅ U̇_{q,π}(𝔤)_ℒ`** (BE2 Theorems 11.7 and 12.1), as a ring isomorphism,
given the Nondegeneracy Conjecture. It is `ℒ`-linear (`gammaIntEquiv_smul`). -/
def gammaIntEquiv (hN : SKM.NondegeneracyConjecture cs)
    (hα : LinearIndependent ℤ Q.α) (hh : LinearIndependent ℤ Q.cd.coroot) :
    lForm Q Coefficients.q Coefficients.pi (LaurentPolynomial Zπ) ≃+*
      SKM.K0Relations.Grothendieck S Q.skmSymmetrizer hS :=
  RingEquiv.ofBijective (gammaInt Q hS cs hf) (gammaInt_bijective Q hS cs hf hN hα hh)

@[simp] theorem gammaIntEquiv_apply (hN : SKM.NondegeneracyConjecture cs)
    (hα : LinearIndependent ℤ Q.α) (hh : LinearIndependent ℤ Q.cd.coroot)
    (x : lForm Q Coefficients.q Coefficients.pi (LaurentPolynomial Zπ)) :
    gammaIntEquiv Q hS cs hf hN hα hh x = gammaInt Q hS cs hf x :=
  rfl

theorem gammaIntEquiv_smul (hN : SKM.NondegeneracyConjecture cs)
    (hα : LinearIndependent ℤ Q.α) (hh : LinearIndependent ℤ Q.cd.coroot)
    (r : LaurentPolynomial Zπ) (x : lForm Q Coefficients.q Coefficients.pi (LaurentPolynomial Zπ)) :
    gammaIntEquiv Q hS cs hf hN hα hh (r • x) = r • gammaIntEquiv Q hS cs hf hN hα hh x := by
  simp only [gammaIntEquiv_apply, map_smul]

/-- **BE2 Theorems 11.7 and 12.1, conditional on the field case.** If the Nondegeneracy
Conjecture holds over every field of characteristic zero for the datum, then `γ` is bijective
over every ground field in which `2 ≠ 0`. -/
theorem gammaInt_bijective_of_charZeroField
    (hK : SKM.CharZeroFieldNondegeneracy Q.toSKM) (h₂ : (2 : k) ≠ 0)
    (hα : LinearIndependent ℤ Q.α) (hh : LinearIndependent ℤ Q.cd.coroot) :
    Function.Bijective (gammaInt Q hS cs hf) :=
  gammaInt_bijective Q hS cs hf
    (SKM.nondegeneracyConjecture_of_charZeroField hK (IsUnit.mk0 _ h₂) hS cs) hα hh

end OddMath.QuiverHecke.SerreComplex
