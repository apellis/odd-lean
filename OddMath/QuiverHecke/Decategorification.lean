/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.GrothendieckIsomorphism
import OddMath.QuiverHecke.VacuumRouteSwappedRightNegative
import OddMath.CoveringQuantum.UDot.WindowForm

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
* `SerreComplex.decategorification_of_separating`: the same for a torsion-free weight group
  with linearly independent roots and integral weights separating the coroots; the colour set
  may be infinite and the weight group need not be finitely generated.
* `SerreComplex.decategorification_sourceWeightLattice`: the same in BE2's own setting, the
  weight lattice `P = {λ ∈ 𝔥* | ⟨hᵢ, λ⟩ ∈ ℤ}` of a complex realization with linearly independent
  roots and coroots, for an arbitrary colour set.

## Hypotheses compared with §12

BE2 §12 assumes the homogeneity condition (1.31) and a ground field `k = k₀`. The statements
here assume, in addition, that `2 ≠ 0` in `k`. This is a genuine restriction, not a
convenience: it is the ring hypothesis of `nondegeneracy_of_symmetrizer`, and fields of
characteristic 2 are not covered. Nondegeneracy of the form of Theorem 10.1 uses linearly
independent roots and coroots, as in BE2's realization. `decategorification` also assumes
finitely many colours and a finitely generated free weight lattice;
`decategorification_of_separating` and `decategorification_sourceWeightLattice` drop these,
keeping the route hypothesis `DegreeLocallyFinite` of Theorem 11.7 (automatic for finitely
many colours). The colour index type and the weight lattice lie in one universe. The
bar-consistency condition (10.2) is not assumed.
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
`SKM.Symmetrizer.degreeLocallyFinite_of_finite`. Characteristic 2 is excluded: `2 ≠ 0` is the
hypothesis under which the Nondegeneracy Conjecture is proved. -/
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

omit [Finite I] [Module.Free ℤ X] [Module.Finite ℤ X] in
/-- **The Decategorification Conjecture** (BE2, §12) for homogeneous parameters over a field in
which `2 ≠ 0` (characteristic 2 is not covered), for a torsion-free weight group with linearly
independent roots and integral weights `ω` with `⟨hᵢ, ωⱼ⟩ = δᵢⱼ`. The colour set may be
infinite and the weight group need not be finitely generated; the route hypothesis `hf` of
Theorem 11.7 remains. -/
theorem decategorification_of_separating [Module.IsTorsionFree ℤ X] (h₂ : (2 : k) ≠ 0)
    (ω : I → X) (hω : ∀ i j, Q.h i (ω j) = if i = j then 1 else 0)
    (hα : LinearIndependent ℤ Q.α) :
    Function.Bijective (gammaInt Q hS cs hf) :=
  gammaInt_bijective_of_nondegenerate Q hS cs hf
    (nondegeneracy_of_symmetrizer Q.skmSymmetrizer (IsUnit.mk0 _ h₂) hS cs)
    (WindowForm.sesquilinearForm_nondegenerate_of_separating Q ω hω hα)

end QuiverHecke.SerreComplex

namespace QuiverHecke.SerreComplex

open CategoryTheory StringDiagrams LaurentPolynomial CoveringQuantum CoveringQuantum.UDot
  CoveringQuantum.SourceWeightLattice

universe u

/-- **The Decategorification Conjecture in BE2's setting** (arXiv:1701.04133v2, §1 and §12):
for a complex realization `(𝔥, hᵢ, αᵢ)` with linearly independent roots and coroots and its
weight lattice `P = {λ ∈ 𝔥* | ⟨hᵢ, λ⟩ ∈ ℤ}`, homogeneous parameters over a field in which
`2 ≠ 0` (characteristic 2 is not covered), the homomorphism `γ` of Theorem 11.7 is bijective.
The colour set is arbitrary; the route hypothesis `hf` of Theorem 11.7 remains (it holds for
finitely many colours by `SKM.Symmetrizer.degreeLocallyFinite_of_finite`). -/
theorem decategorification_sourceWeightLattice {I H : Type u} [AddCommGroup H] [Module ℂ H]
    {k : Type*} [Field k] (h : I → H) (C : SuperCartanDatum I) (α : I → Module.Dual ℂ H)
    (ha : ∀ i j, α j (h i) = (C.a i j : ℂ))
    {S : SKM.Scalars (datum h C α ha).toSKM k} (hS : S.Homogeneous) (cs : SKM.CScalars S)
    (hf : (datum h C α ha).skmSymmetrizer.DegreeLocallyFinite) (h₂ : (2 : k) ≠ 0)
    (hh : LinearIndependent ℂ h) (hα : LinearIndependent ℂ α) :
    Function.Bijective (gammaInt (datum h C α ha) hS cs hf) :=
  decategorification_of_separating (datum h C α ha) hS cs hf h₂ (omega h hh)
    (fun i j ↦ coroot_omega h hh i j) (root_linearIndependent h C α ha hα)

end QuiverHecke.SerreComplex

end OddMath
