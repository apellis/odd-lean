/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.VacuumRouteSwappedRightNegative
import OddMath.QuiverHecke.WidthZero
import OddMath.SKM.BubbleCoefficientBasis
import OddMath.SKM.DimensionFormula
import OddMath.SKM.GroundRingNondegeneracy

/-!
# Bases of 2-morphism spaces and graded dimensions

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2: consequences of
the Nondegeneracy Conjecture of §8, which `nondegeneracy_of_symmetrizer` proves for a
symmetrizable Cartan superdatum and homogeneous parameters over a commutative ring in which `2`
is invertible.

## Main results

* `betaSYM_bijective`, `betaSYMEquiv`: the homomorphism `β_λ : SYM → End(1_λ)` of (1.21)–(1.22)
  is an isomorphism (the case `F = G = 1_λ` noted in the introduction of BE2, before the
  statement of the conjecture). Surjectivity is Theorem 8.1 for the empty boundary.
* `MatchingBasisChoice.expansionEquiv`: `Hom(E_a 1_λ, E_b 1_λ)` is a free right `SYM`-module
  with basis the decorated matchings `f(σ, λ)` (the conjecture, as a linear isomorphism).
* `MatchingBasisChoice.expansion_mapRange_mul`: the expansion is right `SYM`-linear.
* `MatchingBasisChoice.homBasisOfSymmetrizer`: an explicit basis of `Hom(E_a 1_λ, E_b 1_λ)`
  over the ground ring, indexed by pairs of a decorated matching and a monomial of the monomial
  basis of `SYM` (`SYM.coefficientBasis`); `homBasisOfSymmetrizer_apply` gives its vectors
  `f(σ, λ) β_λ(p)`. `MatchingBasisChoice.free_hom`: the Hom module is free.
* `MatchingBasisChoice.componentEquiv`: the same on each homogeneous component of fixed degree
  and parity.
* `wordHomComponent_finrank_eq_sum`, `homDimension_coeff_eq_sum`: over a field, the dimension of each
  homogeneous component, and each coefficient of the graded superdimension, is a finite sum
  over the decorated matchings of the shifted dimensions of `SYM`.
* `homDimension_eq_form_mul_symDimension`: Theorem 12.1, equation (dum): the graded superdimension of
  `Hom(E_a 1_λ, E_b 1_λ)` is `⟨e_a 1_λ, e_b 1_λ⟩` times the graded superdimension of `SYM`.

## Hypotheses compared with the source

The Nondegeneracy Conjecture is stated in BE2 for arbitrary parameters over a field; the
results here assume homogeneous parameters (1.31), a symmetrizable Cartan superdatum, and that
`2` is invertible (the hypotheses of `nondegeneracy_of_symmetrizer`). The dimension statements
also assume `DegreeLocallyFinite`, which holds for finitely many colours.
-/

noncomputable section

namespace OddMath.QuiverHecke

open CategoryTheory StringDiagrams SKM

universe u w

section Ring

variable {I X : Type u} [AddCommGroup X] {D : SKM.Datum I X} {k : Type w} [CommRing k]
  {Sc : SKM.Scalars D k}

/-- **`β_λ` is an isomorphism** (BE2, arXiv:1701.04133v2, introduction: the case
`F = G = 1_λ` of the Nondegeneracy Conjecture), for a symmetrizable Cartan superdatum and
homogeneous parameters over a commutative ring in which `2` is invertible. Injectivity is the
conjecture; surjectivity is Theorem 8.1 for the empty boundary. -/
theorem betaSYM_bijective (sy : SKM.Symmetrizer D) (h₂ : IsUnit (2 : k))
    (hc : Sc.Homogeneous) (cs : SKM.CScalars Sc) (μ : X) :
    Function.Bijective (SKM.betaSYM cs μ) := by
  refine ⟨SKM.betaSYM_injective_of_nondegeneracy cs
    (nondegeneracy_of_symmetrizer sy h₂ hc cs) μ, fun f => ?_⟩
  have hf := SKM.endOne_mem_bubbleSpan cs μ f
  rw [← SKM.betaSYM_range cs μ] at hf
  obtain ⟨x, hx⟩ := hf
  exact ⟨x, hx⟩

/-- The algebra isomorphism `β_λ : SYM ≃ End(1_λ)` of `betaSYM_bijective`. -/
def betaSYMEquiv (sy : SKM.Symmetrizer D) (h₂ : IsUnit (2 : k)) (hc : Sc.Homogeneous)
    (cs : SKM.CScalars Sc) (μ : X) :
    SKM.SYM D k ≃ₐ[k] End ((SKM.pres D Sc).obj (SKM.ob D μ [])) :=
  AlgEquiv.ofBijective (SKM.betaSYM cs μ) (betaSYM_bijective sy h₂ hc cs μ)

@[simp] theorem betaSYMEquiv_apply (sy : SKM.Symmetrizer D) (h₂ : IsUnit (2 : k))
    (hc : Sc.Homogeneous) (cs : SKM.CScalars Sc) (μ : X) (p : SKM.SYM D k) :
    betaSYMEquiv sy h₂ hc cs μ p = SKM.betaSYM cs μ p :=
  rfl

end Ring

end OddMath.QuiverHecke

namespace OddMath.SKM.MatchingBasisChoice

open CategoryTheory StringDiagrams

universe u w

variable {I X : Type u} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} {a b : List (Letter I)} (F : MatchingBasisChoice a b)

/-- **The Nondegeneracy Conjecture as a linear isomorphism** (BE2 §8), for a symmetrizable
Cartan superdatum and homogeneous parameters over a commutative ring in which `2` is
invertible: for `wt(a) = wt(b)`, finitely supported families of `SYM` coefficients on the
decorated matchings correspond to the 2-morphisms `E_a 1_λ → E_b 1_λ`, by
`(p_σ) ↦ Σ_σ f(σ, λ) β_λ(p_σ)`. -/
def expansionEquiv (sy : Symmetrizer D) (h₂ : IsUnit (2 : k)) (hc : Sc.Homogeneous)
    (cs : CScalars Sc) (hab : wt D 0 a = wt D 0 b) (μ : X) :
    (F.Labels →₀ SYM D k) ≃ₗ[k] ((pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ b)) :=
  LinearEquiv.ofBijective (F.expansion cs μ)
    (QuiverHecke.nondegeneracy_of_symmetrizer sy h₂ hc cs a b hab μ F)

@[simp] theorem expansionEquiv_apply (sy : Symmetrizer D) (h₂ : IsUnit (2 : k))
    (hc : Sc.Homogeneous) (cs : CScalars Sc) (hab : wt D 0 a = wt D 0 b) (μ : X)
    (z : F.Labels →₀ SYM D k) :
    F.expansionEquiv sy h₂ hc cs hab μ z = F.expansion cs μ z :=
  rfl

/-- The expansion is a homomorphism of right `SYM`-modules: multiplying every coefficient on
the right by `q` multiplies the 2-morphism on the right by `β_λ(q)` (`rightAction`). -/
theorem expansion_mapRange_mul (cs : CScalars Sc) (μ : X) (z : F.Labels →₀ SYM D k)
    (q : SYM D k) :
    F.expansion cs μ (z.mapRange (· * q) (zero_mul q)) =
      rightAction cs μ (F.expansion cs μ z) q := by
  classical
  induction z using Finsupp.induction_linear with
  | zero => simp [rightAction]
  | add x y hx hy =>
      rw [Finsupp.mapRange_add (fun _ _ => add_mul _ _ q), map_add, hx, hy, map_add]
      simp only [rightAction, Preadditive.comp_add]
  | single t p =>
      rw [Finsupp.mapRange_single, expansion_single, expansion_single, rightAction, map_mul]
      change bubAt D Sc μ a (betaSYM cs μ q ≫ betaSYM cs μ p) ≫ _ = _
      rw [bubAt_comp, Category.assoc]

/-- **A basis of `Hom(E_a 1_λ, E_b 1_λ)` over the ground ring**, for a symmetrizable Cartan
superdatum and homogeneous parameters over a commutative ring in which `2` is invertible: the
2-morphisms `f(σ, λ) β_λ(p)`, for `σ` a decorated matching and `p` a monomial of
`SYM.coefficientBasis` (`homBasisOfSymmetrizer_apply`). -/
def homBasisOfSymmetrizer (sy : Symmetrizer D) (h₂ : IsUnit (2 : k)) (hc : Sc.Homogeneous)
    (cs : CScalars Sc) (hab : wt D 0 a = wt D 0 b) (μ : X) :
    Module.Basis (Σ _ : F.Labels, SYM.CoefficientIndex D) k
      ((pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ b)) :=
  F.homBasis cs μ (QuiverHecke.nondegeneracy_of_symmetrizer sy h₂ hc cs a b hab μ F)

theorem homBasisOfSymmetrizer_apply (sy : Symmetrizer D) (h₂ : IsUnit (2 : k))
    (hc : Sc.Homogeneous) (cs : CScalars Sc) (hab : wt D 0 a = wt D 0 b) (μ : X)
    (t : F.Labels) (η : SYM.CoefficientIndex D) :
    F.homBasisOfSymmetrizer sy h₂ hc cs hab μ ⟨t, η⟩ =
      bubAt D Sc μ a (betaSYM cs μ (SYM.coefficientBasis D k η)) ≫ xev cs μ a b (F.layers t) :=
  F.homBasis_apply_eq cs μ _ t η

/-- `Hom(E_a 1_λ, E_b 1_λ)` is a free module over the ground ring. -/
theorem free_hom (sy : Symmetrizer D) (h₂ : IsUnit (2 : k)) (hc : Sc.Homogeneous)
    (cs : CScalars Sc) (hab : wt D 0 a = wt D 0 b) (μ : X) :
    Module.Free k ((pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ b)) :=
  Module.Free.of_basis (F.homBasisOfSymmetrizer sy h₂ hc cs hab μ)

/-- The homogeneous form of `expansionEquiv`: on the component of degree `n` and parity `p`,
families of `SYM` coefficients with the complementary bidegrees correspond to the 2-morphisms
of that bidegree. -/
def componentEquiv (sy : Symmetrizer D) (h₂ : IsUnit (2 : k)) (hc : Sc.Homogeneous)
    (cs : CScalars Sc) (hab : wt D 0 a = wt D 0 b) (μ : X) (z : ℤ × ZMod 2) :
    F.coefficientComponent (k := k) sy μ z ≃ₗ[k] wordHomComponent sy Sc μ a b z :=
  F.componentExpansionEquiv sy cs μ hc
    (QuiverHecke.nondegeneracy_of_symmetrizer sy h₂ hc cs a b hab μ F) z

end OddMath.SKM.MatchingBasisChoice

namespace OddMath.QuiverHecke

open CategoryTheory StringDiagrams SKM

universe u w

section Field

variable {I X : Type u} [AddCommGroup X] {D : SKM.Datum I X} {k : Type w} [Field k]
  {Sc : SKM.Scalars D k}

/-- **Dimensions of the homogeneous components** of `Hom(E_a 1_λ, E_b 1_λ)`: over a field in
which `2 ≠ 0`, the component of degree `n` and parity `p` has dimension
`Σ_σ dim SYM_{(n, p) - deg σ}`, over the finitely many decorated matchings `σ` of degree at
most `n`. -/
theorem wordHomComponent_finrank_eq_sum {a b : List (SKM.Letter I)} (F : SKM.MatchingBasisChoice a b)
    (sy : SKM.Symmetrizer D) (h₂ : (2 : k) ≠ 0) (hc : Sc.Homogeneous) (cs : SKM.CScalars Sc)
    (hf : sy.DegreeLocallyFinite) (hab : SKM.wt D 0 a = SKM.wt D 0 b) (μ : X)
    (z : ℤ × ZMod 2) :
    Module.finrank k (SKM.wordHomComponent sy Sc μ a b z) =
      ∑ t : F.boundedLabels sy μ z.1,
        Module.finrank k (SKM.SYM.component sy k (z - F.labelBidegree sy μ t.val)) :=
  F.wordHomComponent_finrank_of_nondegeneracy sy cs μ hc hf
    (nondegeneracy_of_symmetrizer sy (IsUnit.mk0 _ h₂) hc cs) hab z

/-- **The graded superdimension of `Hom(E_a 1_λ, E_b 1_λ)`, coefficientwise**: for a sign
`σ` with `σ² = 1`, the coefficient of `q^n` is `Σ_σ' σ^{par σ'} S_{n - deg σ'}`, over the
decorated matchings `σ'`, where `S` is the graded superdimension of `SYM`. -/
theorem homDimension_coeff_eq_sum {a b : List (SKM.Letter I)} (F : SKM.MatchingBasisChoice a b)
    (sy : SKM.Symmetrizer D) (h₂ : (2 : k) ≠ 0) (hc : Sc.Homogeneous) (cs : SKM.CScalars Sc)
    (hf : sy.DegreeLocallyFinite) (hab : SKM.wt D 0 a = SKM.wt D 0 b) (μ : X)
    (σ : ℚ) (hσ : σ ^ 2 = 1) (n : ℤ) :
    (SKM.homDimension sy cs hc hf μ a b σ).coeff n =
      ∑ t : F.boundedLabels sy μ n, σ ^ (F.labelBidegree sy μ t.val).2.val *
        (SKM.symDimension sy k σ).coeff (n - (F.labelBidegree sy μ t.val).1) :=
  SKM.homDimension_coeff_basis F sy cs μ hc hf
    (nondegeneracy_of_symmetrizer sy (IsUnit.mk0 _ h₂) hc cs a b hab μ F) σ hσ n

end Field

section RootDatum

open CoveringQuantum CoveringQuantum.UDot.GenericTensor CoveringQuantum.UDot.GenericVerma.MixedGram

variable {I X : Type u} [AddCommGroup X] [DecidableEq I] [DecidableEq X]
  (Q : CoveringQuantum.RootDatum I X) {k : Type w} [Field k] {Sc : SKM.Scalars Q.toSKM k}

/-- **BE2 Theorem 12.1, equation (dum)**, for homogeneous parameters over a field in which
`2 ≠ 0`: the graded superdimension of `Hom(E_a 1_λ, E_b 1_λ)` (with `π ↦ σ`, `σ² = 1`) is the
sesquilinear form `⟨e_a 1_λ, e_b 1_λ⟩` times the graded superdimension of `SYM`. The
hypothesis `hf` holds for finitely many colours. -/
theorem homDimension_eq_form_mul_symDimension (h₂ : (2 : k) ≠ 0) (hc : Sc.Homogeneous)
    (cs : SKM.CScalars Sc) (hf : Q.skmSymmetrizer.DegreeLocallyFinite) (μ : X)
    (a b : List (SKM.Letter I)) (hab : SKM.wt Q.toSKM 0 a = SKM.wt Q.toSKM 0 b)
    (σ : ℚ) (hσ : σ ^ 2 = 1) :
    SKM.homDimension Q.skmSymmetrizer cs hc hf μ a b σ =
      signLaurent σ hσ (sesquilinearForm Q (algebraWord Q μ a) (algebraWord Q μ b)) *
        SKM.symDimension Q.skmSymmetrizer k σ :=
  SKM.hom_dimension_eq_form_mul_sym Q cs hc hf
    (nondegeneracy_of_symmetrizer Q.skmSymmetrizer (IsUnit.mk0 _ h₂) hc cs) μ a b hab σ hσ

end RootDatum

end OddMath.QuiverHecke
