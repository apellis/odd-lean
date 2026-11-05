/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.GrothendieckIsomorphism
import OddMath.QuiverHecke.VacuumRouteSwappedRightNegative

/-!
# The Decategorification Conjecture for homogeneous parameters

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §12, the Decategorification
Conjecture: the surjective `ℒ`-algebra homomorphism `γ : U̇_{q,π}(𝔤)_ℒ → K₀(𝔘̇(𝔤))` of
Theorem 11.7 is an isomorphism. Theorem 12.1 deduces it from the Nondegeneracy Conjecture
(§8); `SerreComplex.gammaInt_bijective` formalizes Theorems 11.7 and 12.1 with the
Nondegeneracy Conjecture as a hypothesis, and without the bar-consistency condition (10.2).
Here that hypothesis is discharged by `QuiverHecke.nondegeneracy_of_symmetrizer`.

## Main results

* `Symmetrizer.degreeLocallyFinite_of_finite`: the route hypothesis `DegreeLocallyFinite` of
  Theorem 11.7 holds for finitely many colours.
* `SerreComplex.decategorification`: `γ` is bijective.
* `SerreComplex.decategorificationEquiv`: the resulting ring isomorphism
  `U̇_{q,π}(𝔤)_ℒ ≃ K₀(𝔘̇(𝔤))`, `ℒ`-linear by `gammaIntEquiv_smul`.

## Hypotheses compared with §12

BE2 §12 assumes the homogeneity condition (1.31) and a ground field `k = k₀`. The statements
here assume, in addition, that `2 ≠ 0` in `k` (the ring hypothesis of
`nondegeneracy_of_symmetrizer`), and the hypotheses that the formalization of Theorem 12.1
uses for nondegeneracy of the form of Theorem 10.1: finitely many colours, a finitely
generated free weight lattice, and linearly independent roots and coroots. The colour index
type and the weight lattice lie in one universe. The bar-consistency condition (10.2) is not
assumed.
-/

noncomputable section

open scoped Classical

namespace OddMath

namespace SKM

/-- With finitely many colours, every symmetrizer is degree locally finite. -/
theorem Symmetrizer.degreeLocallyFinite_of_finite {I X : Type*} [AddCommGroup X] [Finite I]
    {D : Datum I X} (sy : Symmetrizer D) : sy.DegreeLocallyFinite :=
  fun _ => Set.toFinite _

end SKM

namespace QuiverHecke.SerreComplex

open CategoryTheory StringDiagrams LaurentPolynomial CoveringQuantum CoveringQuantum.UDot

universe u

variable {I X : Type u} [AddCommGroup X] {k : Type*} [Field k]
variable (Q : CoveringQuantum.RootDatum I X) {S : SKM.Scalars Q.toSKM k} (hS : S.Homogeneous)
  (cs : SKM.CScalars S) (hf : Q.skmSymmetrizer.DegreeLocallyFinite)
variable [Finite I] [Module.Free ℤ X] [Module.Finite ℤ X]

/-- **The Decategorification Conjecture** (BE2, arXiv:1701.04133v2, §12) for homogeneous
parameters over a field in which `2 ≠ 0`: the homomorphism `γ` of Theorem 11.7 is bijective.
Theorem 12.1 applied to `nondegeneracy_of_symmetrizer`. The hypothesis `hf` holds by
`SKM.Symmetrizer.degreeLocallyFinite_of_finite`. -/
theorem decategorification (h₂ : (2 : k) ≠ 0) (hα : LinearIndependent ℤ Q.α)
    (hh : LinearIndependent ℤ Q.cd.coroot) :
    Function.Bijective (gammaInt Q hS cs hf) :=
  gammaInt_bijective Q hS cs hf
    (nondegeneracy_of_symmetrizer Q.skmSymmetrizer (IsUnit.mk0 _ h₂) hS cs) hα hh

/-- **`K₀(𝔘̇(𝔤)) ≅ U̇_{q,π}(𝔤)_ℒ`** (BE2, §12) for homogeneous parameters over a field in which
`2 ≠ 0`, as a ring isomorphism; it is `γ` (`decategorificationEquiv_apply`) and `ℒ`-linear. -/
def decategorificationEquiv (h₂ : (2 : k) ≠ 0) (hα : LinearIndependent ℤ Q.α)
    (hh : LinearIndependent ℤ Q.cd.coroot) :
    lForm Q Coefficients.q Coefficients.pi (LaurentPolynomial Zπ) ≃+*
      SKM.K0Relations.Grothendieck S Q.skmSymmetrizer hS :=
  gammaIntEquiv Q hS cs (Q.skmSymmetrizer.degreeLocallyFinite_of_finite)
    (nondegeneracy_of_symmetrizer Q.skmSymmetrizer (IsUnit.mk0 _ h₂) hS cs) hα hh

@[simp] theorem decategorificationEquiv_apply (h₂ : (2 : k) ≠ 0)
    (hα : LinearIndependent ℤ Q.α) (hh : LinearIndependent ℤ Q.cd.coroot)
    (x : lForm Q Coefficients.q Coefficients.pi (LaurentPolynomial Zπ)) :
    decategorificationEquiv Q hS cs h₂ hα hh x = gammaInt Q hS cs hf x :=
  rfl

end QuiverHecke.SerreComplex

end OddMath
