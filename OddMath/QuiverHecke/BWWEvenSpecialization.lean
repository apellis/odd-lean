/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.BWWNondegeneracy
import OddMath.SKM.BWWEvenGraded
import OddMath.SKM.BWWPresentation
import OddMath.SKM.EvenBridge.Datum

/-!
# The Brundan–Wang–Webster headline on purely even data

J. Brundan, W. Wang, B. Webster, arXiv:2505.22929v2, §2.2 (the polynomials `Qᵢⱼ(x, y)` of
(2.6)–(2.7) over an `ℕ`-graded commutative ring, homogeneous of degree `-2dᵢaᵢⱼ` when `x`, `y`
have degrees `2dᵢ`, `2dⱼ`) and Theorem 5.6 (the ordinary basis theorem for symmetrizable data
and these parameters). This file specializes the odd/mixed headline
`QuiverHecke.bwwGradedNondegeneracy` (J. Brundan, A. P. Ellis, arXiv:1701.04133v2, §8, the
Nondegeneracy Conjecture, for these parameters) to parity identically zero, with the parameters
given in Brundan–Wang–Webster's form, as polynomials (`SKM.BWWPolynomials`), rather than as the
coefficient boxes `SKM.BWWScalars` of the odd encoding.

* `bwwPolynomials_evenNondegeneracy`: for a purely even datum (`SKM.EvenBridge.IsEven`) with a
  symmetrizer, over every `ℕ`-graded commutative ring with `2` invertible, for every family of
  polynomials `Qᵢⱼ` as in (2.6)–(2.7) that is homogeneous for the grading of §2.2
  (`BWWPolynomials.GradedHomogeneous`), and every normalization, the decorated reduced
  matchings form a basis over the bubble algebra (`SKM.NondegeneracyConjecture`) of the
  2-category with these parameters.
* `bwwPolynomials_evenNondegeneracy_of_compatible`: the same in the form of the existing
  all-even declarations (`SKM.EvenBridge`), for a datum compatible with a symmetric Cartan datum
  `C` and the symmetrizer `dᵢ = (i·i)/2` (`SKM.EvenBridge.symmetrizer`), so that the dot on an
  `i`-strand has degree `i·i = 2dᵢ`, as in Brundan–Wang–Webster.
* `presBWW_bwwPolynomials`: the presentation with these parameters is `SKM.pres` of the
  underlying Brundan–Ellis parameters, the one appearing in the conclusion.
* `quadSum_bwwPolynomials`: in it, the double crossing on `Eᵢ Eⱼ 1_ν` equals `Qᵢⱼ(x, y)` pinned
  with `x` on the `i`-strand and `y` on the `j`-strand (`pinQuad`), as in (2.11).

## What this comparison does and does not establish

The parameter dictionary is checked: `SKM.bwwPolynomialsEquiv` identifies the polynomials with
the coefficient boxes, and `BWWPolynomials.gradedHomogeneous_toBWWScalars_iff` identifies the
grading conditions. The odd headline has no finiteness condition on the colour set, so none is
needed here.

The statement keeps three hypotheses beyond Brundan–Wang–Webster, Theorem 5.6
(`docs/Nondegeneracy/BWWEvenComparison.md`, §3): `2` is a unit in `k`; the normalization is a
`SKM.CScalars`, which exists exactly under the condition of `SKM.RootCover.nonempty_cScalars_iff`
(for instance for independent simple roots), whereas Brundan–Wang–Webster allow arbitrary
normalizations (Remark 2.4); and the conclusion is the ungraded basis statement. The
identification of `SKM.presBWW` with the 2-category of Brundan–Wang–Webster beyond the
quadratic relation is by inspection of their relations (2.10)–(2.15): their 2-category is not
formalized independently, so no theorem of the even literature is recovered here as a formal
statement about a separately defined object.
-/

noncomputable section

namespace OddMath.QuiverHecke

open SKM

universe u

variable {I X : Type u} [AddCommGroup X]

/-- **The Brundan–Wang–Webster headline at parity zero** (Brundan–Ellis, arXiv:1701.04133v2,
§8, for the parameters of Brundan–Wang–Webster, arXiv:2505.22929v2, §2.2): for a purely even
datum with a symmetrizer, over every `ℕ`-graded commutative ring `k` in which `2` is
invertible, for every family of polynomials `Qᵢⱼ(x, y)` as in (2.6)–(2.7), homogeneous of degree
`-2dᵢaᵢⱼ` with `x`, `y` in degrees `2dᵢ`, `2dⱼ`, and every normalization, the decorated reduced
matchings form a basis over the bubble algebra. -/
theorem bwwPolynomials_evenNondegeneracy (D : Datum I X) (sy : Symmetrizer D)
    (hD : EvenBridge.IsEven D) (k : Type u) [CommRing k] {σ : Type u} [SetLike σ k]
    [AddSubgroupClass σ k] (𝒜 : ℕ → σ) [GradedRing 𝒜] (h₂ : IsUnit (2 : k))
    (P : BWWPolynomials D k) (hP : P.GradedHomogeneous sy 𝒜)
    (cs : CScalars (bwwPolynomialsEquiv hD P).toScalars) : NondegeneracyConjecture cs :=
  bwwGradedNondegeneracy D sy k 𝒜 h₂ (bwwPolynomialsEquiv hD P)
    ((P.gradedHomogeneous_toBWWScalars_iff sy 𝒜 hD).2 hP) cs

/-- **The Brundan–Wang–Webster headline at parity zero, in the form of the all-even
declarations**: for a purely even datum compatible with a symmetric Cartan datum `C`, with the
symmetrizer `dᵢ = (i·i)/2` of `SKM.EvenBridge.symmetrizer` (so a dot on an `i`-strand has degree
`i·i`), over every `ℕ`-graded commutative ring with `2` invertible, for every graded family of
Brundan–Wang–Webster polynomials and every normalization, the conjecture holds. -/
theorem bwwPolynomials_evenNondegeneracy_of_compatible (D : Datum I X)
    (C : Categorification.QuantumGroup.CartanDatum I) (hc : EvenBridge.Compatible D C)
    (hD : EvenBridge.IsEven D) (k : Type u) [CommRing k] {σ : Type u} [SetLike σ k]
    [AddSubgroupClass σ k] (𝒜 : ℕ → σ) [GradedRing 𝒜] (h₂ : IsUnit (2 : k))
    (P : BWWPolynomials D k) (hP : P.GradedHomogeneous (EvenBridge.symmetrizer D C hc) 𝒜)
    (cs : CScalars (bwwPolynomialsEquiv hD P).toScalars) : NondegeneracyConjecture cs :=
  bwwPolynomials_evenNondegeneracy D (EvenBridge.symmetrizer D C hc) hD k 𝒜 h₂ P hP cs

/-- The coefficient boxes recover the polynomials: the headline for a coefficient box `Sc`
on even data is the statement for the polynomials `Sc.toPolynomials`. -/
theorem bwwPolynomialsEquiv_toPolynomials {D : Datum I X} (hD : EvenBridge.IsEven D)
    {k : Type u} [CommRing k] (Sc : BWWScalars D k) :
    bwwPolynomialsEquiv hD Sc.toPolynomials = Sc :=
  (bwwPolynomialsEquiv hD).apply_symm_apply Sc

/-- The presentation with the Brundan–Wang–Webster parameters `P` is the presentation `SKM.pres`
of the underlying Brundan–Ellis parameters, the one of the conclusion of
`bwwPolynomials_evenNondegeneracy`. -/
theorem presBWW_bwwPolynomials {D : Datum I X} (hD : EvenBridge.IsEven D) {k : Type u}
    [CommRing k] (P : BWWPolynomials D k) :
    SKM.presBWW D (bwwPolynomialsEquiv hD P) = SKM.pres D (bwwPolynomialsEquiv hD P).toScalars :=
  presBWW_eq_pres _

/-- The monomial `x^p y^q` pinned on `Eᵢ Eⱼ 1_ν`: `p` dots on the `i`-strand and `q` dots on
the `j`-strand. -/
def pinMonomial (D : Datum I X) (k : Type u) [CommRing k] (i j : I) (ν : X)
    (m : Fin 2 →₀ ℕ) :
    StringDiagrams.LinDiagram k (SKM.ob D ν [SKM.up i, SKM.up j])
      (SKM.ob D ν [SKM.up i, SKM.up j]) :=
  SKM.dg D ν (SKM.dotsL [SKM.up i] j [] (m 1) ++ SKM.dotsL [] i [SKM.up j] (m 0))
    ((SKM.sChain_dotsL [SKM.up i] j [] (m 1)).append (SKM.sChain_dotsL [] i [SKM.up j] (m 0)))

/-- A polynomial `f(x, y) ∈ k[x, y]` pinned on `Eᵢ Eⱼ 1_ν`, with `x` on the `i`-strand and `y`
on the `j`-strand. -/
def pinQuad (D : Datum I X) {k : Type u} [CommRing k] (i j : I) (ν : X) :
    MvPolynomial (Fin 2) k →ₗ[k] StringDiagrams.LinDiagram k (SKM.ob D ν [SKM.up i, SKM.up j])
      (SKM.ob D ν [SKM.up i, SKM.up j]) :=
  (MvPolynomial.basisMonomials (Fin 2) k).constr k (pinMonomial D k i j ν)

theorem pinQuad_monomial (D : Datum I X) {k : Type u} [CommRing k] (i j : I) (ν : X)
    (m : Fin 2 →₀ ℕ) (a : k) :
    pinQuad D i j ν (MvPolynomial.monomial m a) = a • pinMonomial D k i j ν m := by
  have h : MvPolynomial.monomial m a = a • (MvPolynomial.basisMonomials (Fin 2) k) m := by
    rw [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [h, map_smul, pinQuad, Module.Basis.constr_basis]

/-- **(2.11) on even data.** In `SKM.presBWW D (bwwPolynomialsEquiv hD P)`, the right-hand side
of the quadratic relation on `Eᵢ Eⱼ 1_ν` is `Qᵢⱼ(x, y)` pinned with `x` on the `i`-strand and
`y` on the `j`-strand. -/
theorem quadSum_bwwPolynomials {D : Datum I X} (hD : EvenBridge.IsEven D) {k : Type u}
    [CommRing k] (P : BWWPolynomials D k) (i j : I) (ν : X) :
    SKM.quadSum D (bwwPolynomialsEquiv hD P).c i j ν = pinQuad D i j ν (P.Q i j) := by
  rw [P.Q_eq_poly hD i j]
  unfold BWWScalars.poly
  simp only [map_sum, pinQuad_monomial]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  congr 1
  exact SKM.dg_congr D ν _ _ (by simp)

end OddMath.QuiverHecke
