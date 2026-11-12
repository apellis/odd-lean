# Comparison with Brundan–Wang–Webster Theorem 5.6 on purely even data

Source: J. Brundan, W. Wang, B. Webster, arXiv:2505.22929v2, §2.1–2.2 (Cartan datum, parameters (2.6)–(2.7), relations (2.10)–(2.15)) and Theorem 5.6
(nondegeneracy). This note compares its parameter class and hypotheses with the Phase 2
encoding `BWWScalars` and records the specialization the Phase 2 headline must recover.

## 1. The dictionary (checked)

`OddMath/SKM/BWWEvenDictionary.lean`:

- `BWWPolynomials D k`: polynomials `Qᵢⱼ ∈ k[x, y]` with `Qᵢᵢ = 0`, `Qⱼᵢ(x, y) = Qᵢⱼ(y, x)`
  (2.6), support in the box `[0, dᵢⱼ] × [0, dⱼᵢ]` with only the corners on its top and right
  edges (2.7), and a unit coefficient `tᵢⱼ` of `x^{dᵢⱼ}`.
- `bwwPolynomialsEquiv hD : BWWPolynomials D k ≃ BWWScalars D k` for purely even `D`
  (`hD : ∀ i, D.parity i = 0`): the coefficient of `x^p y^q` in `Qᵢⱼ` is `c i j p q`.
  The inverse `BWWScalars.toPolynomials` needs no parity hypothesis.
- `BWWPolynomials.eq_form`: for `i ≠ j`, `dᵢⱼ ≠ 0`, `Qᵢⱼ` is literally (2.7) with
  `tᵢⱼ;ᵣₛ` the coefficient of `x^r y^s`; `eq_const`: `Qᵢⱼ = tᵢⱼ` when `dᵢⱼ = 0`.

`OddMath/SKM/BWWEvenGraded.lean`:

- `BWWPolynomials.GradedHomogeneous`: every nonzero coefficient of `x^p y^q` in `Qᵢⱼ` lies
  in `𝒜 n`, `n = 2(dᵢdᵢⱼ - dᵢp - dⱼq)`, i.e. `Qᵢⱼ` is homogeneous of degree `-2dᵢaᵢⱼ`
  with `x`, `y` of degrees `2dᵢ`, `2dⱼ`, as in §2.2.
- `gradedHomogeneous_toBWWScalars_iff`: on purely even data this is
  `BWWScalars.GradedHomogeneous` of the coefficient function. The corners have coefficient
  degree `0`; for `y^{dⱼᵢ}` this uses `dᵢdᵢⱼ = dⱼdⱼᵢ`.

So, on purely even data, the BWW parameter class of §2.2 is exactly
`{Sc : BWWScalars D k | Sc.GradedHomogeneous sy 𝒜}`.

**Convention at `aᵢⱼ = 0`.** Read literally, (2.7) gives the constant `tᵢⱼ + tⱼᵢ`. BWW
define `tᵢⱼ := Qᵢⱼ(1, 0)` (§3, before Theorem 3.5), which for `aᵢⱼ = 0` is the whole
constant. The dictionary uses this reading: `Qᵢⱼ = tᵢⱼ = tⱼᵢ`, a unit, as in BE2 (1.3).

## 2. Hypothesis by hypothesis

| BWW 5.6 | Phase 2 encoding | Status |
|---|---|---|
| Symmetrizable GCM | `Symmetrizer D` | same |
| Purely even | parity function on `I` | ours is more general; `hD` specializes |
| `I` possibly infinite, rows and columns locally finite | `I` arbitrary in `Datum`; `EvenBridge` needs `[Finite I]` | **mismatch (3)** |
| `X`, `Y` free, perfect pairing, simple coroots independent | `Datum I X`: any weight group, no regularity | ours more general |
| `k` commutative, `ℕ`-graded, no condition on 2 | `GradedRing 𝒜`, `IsUnit 2` | **mismatch (2)** |
| `Qᵢⱼ` as in (2.6)–(2.7), graded | `BWWScalars.GradedHomogeneous` | equivalent on even data (§1) |
| `tᵢⱼ ∈ k₀ˣ` | `t : kˣ`, `t ∈ 𝒜 0` | same |
| Box-edge vanishing (top and right edges) | fields `c_top`, `c_outside` | implied by grading in BWW; imposed here, equivalent |
| Normalizations `cᵢ : X → kˣ`, `rᵢⱼ` arbitrary (Remark 2.4) | `CScalars`: shift law `c(μ + αⱼ) i = tᵢⱼ c μ i` | **mismatch (1)** |
| Bubble parameters (fake bubbles, infinite Grassmannian) | `CScalars` bubble data | to compare with (2.15) |
| Conclusion: `End(1_λ)` free polynomial on bubbles of degree ≥ 1, `Hom(Gⱼ1_λ, Gᵢ1_λ)` free over it on pinned reduced shapes | `NondegeneracyConjecture cs`: `MatchingBasisChoice` is a basis over `SYM` | match via `EvenBridge.symEquivMvPolynomial`; shape bijection to check |

## 3. Mismatches

**(1) Normalizations; the even statement can be vacuous where BWW 5.6 applies.** BWW work
with arbitrary group homomorphisms `cᵢ : X → kˣ`, `cᵢ(αᵢ) = 1`, and their 2-category depends
only on `Q` up to isomorphism (Remark 2.4). The Phase 1 headline quantifies over
`cs : CScalars Sc`, which imposes the shift law `c(μ + αⱼ) i = tᵢⱼ c μ i` of BE2 (1.17)
(BHLW's choice `rᵢⱼ = 1`). The presentation `pres D Sc` does not involve `cs`; the matching
basis does, through `etaP`, `epsP`, `xev` and the bubbles, and the proofs use the shift law.

*Proved* (`OddMath/SKM/RootCover.lean`, `OddMath/SKM/RootCoverUnits.lean`):

- `RootCover.nonempty_cScalars_iff`: `CScalars Sc` exists if and only if
  `Π_j tᵢⱼ^{nⱼ} = 1` for every `i` and every integer relation `Σ_j nⱼ αⱼ = 0`
  (`rootSum D n = 0`). So units exist for every `t` when the simple roots are independent
  (`nonempty_cScalars_of_injective`), and `αⱼ + αₗ = 0` forces `tᵢⱼ tᵢₗ = 1`
  (`CScalars.t_mul_t_eq_one`).
- `scripts/NonVacuity/RootCover.lean`: affine `A₁` on `ℤ²` with coroots the coordinate
  projections, `α₀ = (2, -2)`, `α₁ = (-2, 2)`, `t₀₁ = 2`, `t₁₀ = 1` over `ℚ`. These parameters
  satisfy BWW's hypotheses, and `isEmpty_cScalars` proves that there is no `CScalars`. So
  `∀ cs, NondegeneracyConjecture cs` holds vacuously there, while BWW 5.6 (with `cᵢ = 1`,
  `rᵢⱼ = 1/tᵢⱼ`) asserts a basis theorem.
- `RootCover.rootCover D`: the datum on `X × (I →₀ ℤ)` with roots `(αᵢ, eᵢ)` and coroots
  `hᵢ ∘ fst`. It has the same Cartan matrix, `dᵢⱼ` and parity and independent roots
  (`rootSum_rootCover`). Parameters transport unchanged (`coverScalars`,
  `coverBWWScalars`), and `nonempty_cScalars_rootCover` gives units for every choice of
  parameters. So the headline applied to the cover is never vacuous.

*Remaining gap* (not routine; deferred pending a decision). The projection
`X × (I →₀ ℤ) → X` is compatible with roots and coroots, so it induces the presentation
functor `RootCover.projectionFunctor : (pres (rootCover D) (coverScalars D Sc)).Presented ⥤
(pres D Sc).Presented` (`OddMath/SKM/RootCoverPresentation.lean`), with linear Hom maps
`RootCover.homMap ν s t` at a fixed right region `ν` that send each generator diagram to the
same diagram (`homMap_diag`). With dependent roots there is no map in the other
direction: a region map `f` would need `f(ν + α₀ + α₁) = f(ν) + α'₀ + α'₁`. Transferring the
basis theorem from the cover to `D` needs two further theorems about the presentation:

- (a) `homMap ν s t` is bijective whenever `s` and `t` have equal root content;
- (b) in `pres D Sc`, Homs between words of equal weight but different root content vanish
  (affine `A₁`: `E₀E₁1_λ` and `1_λ`). This is a root-content grading of the whole
  presentation.

Until (a) and (b) are proved, the even specialization covers BWW 5.6 exactly on data whose
parameters satisfy the relation condition of `nonempty_cScalars_iff`. This includes all data
with independent simple roots, and every datum when all `tᵢⱼ = 1`.

**(2) The prime 2.** BWW 5.6 has no condition on 2. `GradedCoefficientNondegeneracy` asks
for `IsUnit 2` for all data, although on purely even data `BWWScalars.two_isUnit` is vacuous.
Phase 1 recovers the integral even case through `EvenBridge`; the Phase 2 even
specialization must either drop `IsUnit 2` when `hD` holds or route through the integral
even theorem. As currently stated, Phase 2 covers BWW 5.6 only over rings with 2 invertible.

**(3) Infinite `I`.** BWW allow infinite `I`. `EvenBridge.nondegeneracyConjecture_of_isEven`
needs `[Finite I]`. Whether the Phase 2 headline needs it is to be checked when it lands; the
statement is local in the colours of `a` and `b`, so a reduction to the finite subdatum on
those colours is the natural route.

**(4) Diagram conventions (checked against the figures).** In BWW, (2.11) states that the
double crossing on `Eᵢ Eⱼ` equals `Qᵢⱼ(x, y)` pinned with `x` on the `i`-strand and `y` on the
`j`-strand. This is `quadSum`: the coefficient `c i j p q` multiplies `u^p v^q`, with `u` on
the `i`-strand. In (2.12) the first picture is the composite `σ₁σ₂σ₁` read bottom to top.
That is the left-hand side of `braidEq` in `relationBWW`: the `SChain` lists layers from the
domain up. The right-hand side is
`δᵢₖ (Qᵢⱼ(x, y) - Qᵢⱼ(z, y))/(x - z) = Σ cᵢⱼ(p, q) y^q Σ_{s<p} x^s z^{p-1-s}`. This is `braidSum`
on purely even data, where `ζ = 1` and the sum is symmetric under `s ↦ p - 1 - s`. So
`presBWW D (bwwPolynomialsEquiv hD P)` has the relations (2.10)–(2.12) of BWW with
parameters `P`. This identification is by inspection: BWW's 2-category is not formalized
independently.

None of these bears on the truth of the odd/mixed conjecture. (1) and (3) are about which
even data the statement reaches, (2) about the base ring.

## 4. Target: the even specialization

Once the Phase 2 headline exists in the form

    ∀ k 𝒜 [GradedRing 𝒜], IsUnit 2 → ∀ Sc : BWWScalars D k, Sc.GradedHomogeneous sy 𝒜 →
      ∀ cs : <bubble data for Sc>, <BWW nondegeneracy for presBWW D Sc, cs>,

the specialization to be proved is: for purely even `D` with `[Finite I]`, an `ℕ`-graded `k`
with 2 invertible, and `P : BWWPolynomials D k` with `P.GradedHomogeneous sy 𝒜`, the
2-category presented by BWW's relations with parameters `P` (that is, `presBWW D
(bwwPolynomialsEquiv hD P)`) has the bases of BWW 5.6 for every compatible normalization.
Proof plan: transport `P` through `bwwPolynomialsEquiv`, the grading through
`gradedHomogeneous_toBWWScalars_iff`, apply the headline, and identify the conclusion with
5.6 through `EvenBridge.symEquivMvPolynomial` and the relation comparison of (4).
Mismatches (1)–(3) are the hypotheses this statement keeps beyond BWW's.

**Checked statement** (`OddMath/QuiverHecke/BWWEvenSpecialization.lean`):
`QuiverHecke.bwwPolynomials_evenNondegeneracy` proves this specialization for every purely even
datum with a symmetrizer, without `[Finite I]`: transport through `bwwPolynomialsEquiv` and
`gradedHomogeneous_toBWWScalars_iff`, then `bwwGradedNondegeneracy`. The form
`bwwPolynomials_evenNondegeneracy_of_compatible` uses the symmetrizer `dᵢ = (i·i)/2` of a
compatible symmetric Cartan datum. `presBWW_bwwPolynomials` identifies the presentation of the
conclusion, and `quadSum_bwwPolynomials` checks that its quadratic relation is BWW (2.11): the
double crossing on `Eᵢ Eⱼ 1_ν` is `Qᵢⱼ(x, y)` with `x` on the `i`-strand and `y` on the
`j`-strand. Consumer: `scripts/NonVacuity/BWWEvenSpecialization.lean`.

Not established by these declarations:
- a comparison of `presBWW` with an independently formalized even 2-category for general
  parameters `Q`. categorification-lean proves nondegeneracy only for Khovanov–Lauda scalars;
  `presUnfiltered` there has no nondegeneracy theorem. The relations beyond (2.11) are
  identified by inspection, as in mismatch (4);
- the graded form of the conclusion (a homogeneous basis for the total coefficient grading);
- normalizations outside `CScalars`, mismatch (1).
