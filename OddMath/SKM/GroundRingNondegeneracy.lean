/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ScalarChangeCoefficientBasis
import OddMath.SKM.ScalarChangeMatchingFamily
import OddMath.SKM.UniversalParameterFields

/-!
# Nondegeneracy over commutative rings from the characteristic-zero field case

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §8: the
Nondegeneracy Conjecture after Theorem 8.1. This module formalizes the
deduction of `GroundRingDescent.md` §§5–6: the field case over every field
of characteristic zero implies the conjecture over every commutative ring in
which `2` is invertible, for the same datum. The field case is an explicit
hypothesis, `CharZeroFieldNondegeneracy D`; it is not proved here.

## Main results

* `MatchingBasisChoice.homBasis`: when the expansion of a decorated matching
  choice is bijective, the decorated matchings times the coefficient monomials
  of `SYM` form a basis of the Hom module, with the explicit formula
  `homBasis_apply`.
* `nondegeneracyConjecture_scalarChange`: the conjecture is stable under every
  ring map `R → S`, because the presented Homs satisfy
  `S ⊗[R] Hom_R ≃ Hom_S` (`ScalarChange.homBaseChange`) and the chosen
  decorated matchings and coefficient basis specialize to the same family.
  No flatness or injectivity is assumed.
* `universal_nondegeneracy`: the field case implies the conjecture over the
  universal parameter ring `UniversalPolynomialParameters.ParameterRing D`,
  which need not be a domain, by joint detection through characteristic-zero
  prime fraction fields (`UniversalParameterFields.point_separate`).
* `nondegeneracyConjecture_of_charZeroField`: the conjecture for every
  commutative ring `R` with `2` invertible, every homogeneous `Sc` and every
  `cs : CScalars Sc`. No symmetrizer is inverted, and there is no domain,
  reducedness, flatness, Noetherian, finite-colour or independent-root
  hypothesis on `R`. The zero ring and rings of characteristic `p ≠ 2` are
  included.

The datum `D` is fixed throughout; whatever conditions the field statement needs
on `D` (compatible symmetrizable superdatum, positive integral symmetrizers) are
conditions on `D`, inherited unchanged by the conclusion.
-/

noncomputable section
open CategoryTheory
open scoped TensorProduct

namespace OddMath.SKM

universe u v w w'

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}

/-- Two scalar systems with the same units and coefficients are equal. -/
theorem Scalars.ext_t_s {k : Type w} [CommRing k] {Sc Sc' : Scalars D k}
    (ht : Sc.t = Sc'.t) (hs : Sc.s = Sc'.s) : Sc = Sc' := by
  cases Sc
  cases Sc'
  cases ht
  cases hs
  rfl

/-- The conjecture depends only on the scalar system and its normalization units. -/
theorem nondegeneracyConjecture_congr {k : Type w} [CommRing k] {Sc Sc' : Scalars D k}
    (e : Sc = Sc') (cs : CScalars Sc) (cs' : CScalars Sc')
    (hc : ∀ μ i, cs.c μ i = cs'.c μ i) (h : NondegeneracyConjecture cs) :
    NondegeneracyConjecture cs' := by
  subst e
  have : cs = cs' := by
    cases cs
    cases cs'
    congr
    funext μ i
    exact hc μ i
  subst this
  exact h

/-- Homogeneity (1.31) is preserved by every coefficient change. -/
theorem ScalarChange.homogeneous_scalars {R : Type w} {S : Type w'} [CommRing R] [CommRing S]
    (f : R →+* S) {Sc : Scalars D R} (hh : Sc.Homogeneous) :
    (ScalarChange.scalars D f Sc).Homogeneous := by
  intro i j p q hp hp' hq hq' h
  exact hh i j p q hp hp' hq hq' (fun h0 => h (by simp [h0]))

namespace MatchingBasisChoice

variable {k : Type w} [CommRing k] {Sc : Scalars D k} (cs : CScalars Sc) (μ : X)
  {a b : List (Letter I)}

/-- The free coefficient module on decorated matchings, with the basis given by
labels and coefficient monomials. -/
def sourceBasis (F : MatchingBasisChoice a b) :
    Module.Basis (Σ _ : F.Labels, SYM.CoefficientIndex D) k (F.Labels →₀ SYM D k) :=
  Finsupp.basis fun _ => SYM.coefficientBasis D k

@[simp] theorem sourceBasis_apply (F : MatchingBasisChoice a b) (t : F.Labels)
    (η : SYM.CoefficientIndex D) :
    F.sourceBasis (k := k) ⟨t, η⟩ = Finsupp.single t (SYM.coefficientBasis D k η) := by
  simp [sourceBasis, Finsupp.coe_basis]

/-- **Explicit Hom basis.** If the decorated family is a free coefficient basis
(`IsBasis`), then the morphisms `β_μ(η) ⊗ D_t`, a decorated matching `t` with a
coefficient monomial `η` of `SYM` placed on the right, form a `k`-basis of the
Hom module. -/
def homBasis (F : MatchingBasisChoice a b) (h : F.IsBasis cs μ) :
    Module.Basis (Σ _ : F.Labels, SYM.CoefficientIndex D) k
      ((pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ b)) :=
  F.sourceBasis.map (LinearEquiv.ofBijective (F.expansion cs μ) h)

theorem homBasis_apply (F : MatchingBasisChoice a b) (h : F.IsBasis cs μ)
    (t : F.Labels) (η : SYM.CoefficientIndex D) :
    F.homBasis cs μ h ⟨t, η⟩ =
      F.expansion cs μ (Finsupp.single t (SYM.coefficientBasis D k η)) := by
  simp [homBasis]

theorem homBasis_apply_eq (F : MatchingBasisChoice a b) (h : F.IsBasis cs μ)
    (t : F.Labels) (η : SYM.CoefficientIndex D) :
    F.homBasis cs μ h ⟨t, η⟩ =
      bubAt D Sc μ a (betaSYM cs μ (SYM.coefficientBasis D k η)) ≫
        xev cs μ a b (F.layers t) := by
  rw [homBasis_apply, expansion_single]

/-- An expansion that sends the source basis onto a basis is injective. -/
theorem injective_of_basis (F : MatchingBasisChoice a b)
    (B : Module.Basis (Σ _ : F.Labels, SYM.CoefficientIndex D) k
      ((pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ b)))
    (hB : ∀ i, F.expansion cs μ (F.sourceBasis i) = B i) :
    Function.Injective (F.expansion cs μ) := by
  have he : F.expansion cs μ = (F.sourceBasis.equiv B (Equiv.refl _)).toLinearMap := by
    apply F.sourceBasis.ext
    intro i
    rw [hB i, LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply]
  rw [he]
  exact (F.sourceBasis.equiv B (Equiv.refl _)).injective

end MatchingBasisChoice

/-- **Scalar change of nondegeneracy.** If the conjecture holds for `cs` over
`R`, it holds over `S` for the transported parameters, along any ring map.
The basis over `R` is base changed through `S ⊗[R] Hom_R ≃ Hom_S`; its vectors
are the decorated matchings with the same coefficient monomials over `S`. -/
theorem nondegeneracyConjecture_scalarChange {R : Type w} {S : Type w'} [CommRing R]
    [CommRing S] (f : R →+* S) {Sc : Scalars D R} {cs : CScalars Sc}
    (h : NondegeneracyConjecture cs) :
    NondegeneracyConjecture (ScalarChange.cScalars D f cs) := by
  rw [nondegeneracyConjecture_iff_injective]
  intro a b hab μ F
  let _ : Algebra R S := f.toAlgebra
  let bR := F.homBasis cs μ (h a b hab μ F)
  let bS := (Algebra.TensorProduct.basis S bR).map
    (ScalarChange.homBaseChange f D Sc (ob D μ a) (ob D μ b))
  apply F.injective_of_basis _ μ bS
  rintro ⟨t, η⟩
  simp only [bS, bR, Module.Basis.map_apply, Algebra.TensorProduct.basis_apply,
    MatchingBasisChoice.homBasis_apply, ScalarChange.homBaseChange_expansion_single,
    ScalarChange.symMap_coefficientBasis, one_smul, MatchingBasisChoice.sourceBasis_apply]

/-- **The field case of the conjecture**, for a fixed datum: over every field
of characteristic zero, for every homogeneous scalar system and every choice
of normalization units. This is the hypothesis of the descent below, not a
theorem proved in this module. -/
def CharZeroFieldNondegeneracy (D : Datum I X) : Prop :=
  ∀ (K : Type (max u v)) [Field K] [CharZero K] (Sc : Scalars D K),
    Sc.Homogeneous → ∀ cs : CScalars Sc, NondegeneracyConjecture cs

open UniversalPolynomialParameters UniversalParameterFields in
/-- The field case implies the conjecture over the universal parameter ring,
which need not be a domain. -/
theorem universal_nondegeneracy (hK : CharZeroFieldNondegeneracy D) :
    NondegeneracyConjecture (UniversalPolynomialParameters.normalizations D) := by
  rw [nondegeneracyConjecture_iff_injective]
  intro a b hab μ F
  rw [injective_iff_map_eq_zero]
  intro z hz
  have hpt (p : PrimeSpectrum (RationalParameters D)) :
      Finsupp.mapRange.addMonoidHom (ScalarChange.symMap (D := D) (point D p)).toAddMonoidHom
        z = 0 := by
    have hinj := (nondegeneracyConjecture_iff_injective _).1
      (hK (FieldAt D p) (ScalarChange.scalars D (point D p) (UniversalPolynomialParameters.scalars D))
        (ScalarChange.homogeneous_scalars _ (UniversalPolynomialParameters.homogeneous D))
        (ScalarChange.cScalars D (point D p) (UniversalPolynomialParameters.normalizations D)))
      a b hab μ F
    apply hinj
    rw [← ScalarChange.homMap_expansion, hz, map_zero, map_zero]
  ext t
  apply ScalarChange.eq_zero_of_symMap_eq_zero (fun p => point D p) (point_separate D) (z t)
  intro p
  simpa using congrArg (fun y => y t) (hpt p)

/-- **Ground-ring descent** (`GroundRingDescent.md` §§1, 6). If the conjecture
holds over every field of characteristic zero for the datum `D`, then it holds
over every commutative ring in which `2` is invertible, for every homogeneous
scalar system and every normalization. -/
theorem nondegeneracyConjecture_of_charZeroField (hK : CharZeroFieldNondegeneracy D)
    {R : Type w} [CommRing R] (h₂ : IsUnit (2 : R)) {Sc : Scalars D R}
    (hh : Sc.Homogeneous) (cs : CScalars Sc) : NondegeneracyConjecture cs := by
  let f := UniversalPolynomialParameters.specialize h₂ cs
  have hU := nondegeneracyConjecture_scalarChange f (universal_nondegeneracy hK)
  refine nondegeneracyConjecture_congr ?_ _ cs ?_ hU
  · apply Scalars.ext_t_s
    · funext i j
      exact UniversalPolynomialParameters.specialize_t h₂ cs i j
    · funext i j p q
      exact UniversalPolynomialParameters.specialize_coefficient h₂ cs hh ⟨i, j, p, q⟩
  · intro μ i
    exact UniversalPolynomialParameters.specialize_c h₂ cs μ i

/-- **Explicit Hom bases over commutative rings.** Under the field case, for
every pair of equal-weight words and every decorated matching choice, the
decorated matchings times the coefficient monomials of `SYM` form a basis of
the Hom module over any commutative ring with `2` invertible. -/
def homBasisOfCharZeroField (hK : CharZeroFieldNondegeneracy D)
    {R : Type w} [CommRing R] (h₂ : IsUnit (2 : R)) {Sc : Scalars D R}
    (hh : Sc.Homogeneous) (cs : CScalars Sc) {a b : List (Letter I)}
    (hab : wt D 0 a = wt D 0 b) (μ : X) (F : MatchingBasisChoice a b) :
    Module.Basis (Σ _ : F.Labels, SYM.CoefficientIndex D) R
      ((pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ b)) :=
  F.homBasis cs μ (nondegeneracyConjecture_of_charZeroField hK h₂ hh cs a b hab μ F)

end OddMath.SKM
