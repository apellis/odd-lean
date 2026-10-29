# Odd nondegeneracy: restart state

## Consequences of the field case: ground rings, Hom bases and K₀

Checked (conditional on the field case). `SKM.CharZeroFieldNondegeneracy D`
states the conjecture for the datum `D` over every field of characteristic
zero, every homogeneous `Sc` and every `cs`; it is an explicit hypothesis,
not proved. From it:

* `SKM.nondegeneracyConjecture_scalarChange`: the conjecture transfers along
  any ring map `R → S` (no flatness or injectivity), via
  `ScalarChange.homBaseChange` and `ScalarChange.symMap_coefficientBasis`
  (each polynomial/exterior coefficient monomial goes to the same-index
  monomial; `SYM.coefficientBasis_eq_prod`).
* `SKM.universal_nondegeneracy`: the conjecture over the universal parameter
  ring, by joint detection through `UniversalParameterFields.point_separate`
  and `ScalarChange.repr_symMap` (injectivity coefficientwise; surjectivity is
  Theorem 8.1).
* `SKM.nondegeneracyConjecture_of_charZeroField` (GroundRingDescent.md
  §§1, 5–6): the conjecture over every commutative ring with `2` invertible,
  for every homogeneous `Sc` and `cs`; no domain, Noetherian, finite-colour
  or independent-root hypothesis. Comparison with the even case:
  `EvenBridge.nondegeneracyConjecture_of_isEven` holds over every commutative
  ring including those where `2` is not a unit, but only for Khovanov–Lauda
  scalars and finitely many colours; the odd descent keeps `IsUnit 2`
  because the universal ring is built over `ℤ[1/2]`.
* `MatchingBasisChoice.homBasis`, `homBasis_apply_eq` and
  `SKM.homBasisOfCharZeroField`: the explicit Hom basis
  `β_μ(η) ⊗ D_t` (decorated matching `t`, coefficient monomial `η`). The
  graded dimension formula is the existing
  `SKM.hom_dimension_eq_form_mul_sym` with the conjecture discharged by the
  descent.
* `QuiverHecke.SerreComplex.gammaInt_bijective`, `gammaIntEquiv`
  (ring isomorphism, `ℒ`-linear by `gammaIntEquiv_smul`) and
  `gammaInt_bijective_of_charZeroField`: `K₀(𝔘̇) ≅ U̇_{q,π}(𝔤)_ℒ`
  (Theorems 11.7 and 12.1), over every ground field with `2 ≠ 0`. Route
  hypotheses inherited from Theorems 11.7 and 12.1: `DegreeLocallyFinite`,
  finitely many colours, `X` free of finite rank, independent roots and
  coroots. No missing published input was found.

Open: the field case itself; removal of the route hypotheses above; the
case of rings where `2` is not a unit, beyond the even Khovanov–Lauda case.

## Deformed cyclotomic factor: checked steps and forms

The factor targets `RouquierFamily T` with `RouquierMulticolour T Sc` (next section).

**Last-letter recursion (checked).** `CyclotomicAction/MoveHomSnoc.lean` proves
`moveHom_append_singleton`: `moveHom i l (ν ++ [x])` is `moveHom i l ν ⊗ 1_x` followed by
the intertwiner `intertwinerHom (l ++ ν) [] i x`, up to word identifications (KKO's
`V_(n+1) = g_(n+1)(V_n ⊗ 1)` in the global QP induction), with right-whiskering lemmas
`genE_whiskerRight`, `dotE_whiskerRight`, `sameIntertwiner_whiskerRight`,
`intertwinerHom_whiskerRight`. Arbitrary colours, parities and words.
`CyclotomicAction/LastToFirstSnoc.lean` proves the same for the crossing map:
`lastToFirstHom_eq_cl` writes `lastToFirstHom i ν` as the positioned word
`crossingDescent |ν| = [cross (n-1), …, cross 0]`, and
`lastToFirstHom_append_singleton` gives `T_(n+1) = τ_n (T_n ⊗ 1)`.

**Distinct-colour QP step (checked).** `CyclotomicAction/PrefixQPDistinct.lean` proves
`moveHom_lastToFirstHom_append_ne`: for `x ≠ i`,
`V_(n+1) ≫ T_(n+1) = Q_ix(x₁, x_(n+2)) ≫ ((V_n ≫ T_n) ⊗ 1_x)` on `i :: (ν ++ [x])`, with
`Q_ix` the KLR polynomial `qPoly` evaluated at the dot on the moving strand and the dot on
the new spectator (`DeformedGlobalQP.md` §3, case `ν_n ≠ i`). The transport of
`Q_ix(xₙ, x_(n+1))` through `V_n ⊗ 1_x` (`comp_qPoly`) has trivial signs: an odd colour
enters each monomial of `Q_ix` to an even power (`Sc.s_eq_zero`, `Datum.even_d_of_odd`).
Arbitrary colours, parities and words; `d_ix = 0` included.

**Repeated-colour QP step (checked).** `CyclotomicAction/PrefixQPRepeated.lean` proves, on
`i :: (ν ++ [i])` with `V = V_n ⊗ 1_i` (`moveWhisker`), `D = x_(n+1)² − x_n²`,
`E = x_(n+1) − x_n`, `D₀ = x_(n+2)² − x₁²`, `E₀ = x_(n+2) − x₁`, `s = (−1)^(p_i·|ν|)`:
`V ≫ D = D₀ ≫ V`, `V ≫ E = s E₀ ≫ V` (`moveWhisker_comp_squareDiff`, `moveWhisker_comp_sub`);
the expansion of `V ≫ g` for the same-colour intertwiner (`moveWhisker_comp_sameIntertwiner_odd`,
`_even`); and (`DeformedGlobalQP.md` §3, case `ν_n = i`)
`V_(n+1) ≫ T_(n+1) = s D₀ ≫ E₀ ≫ V ≫ T_(n+1)` for odd `i`
(`moveHom_lastToFirstHom_append_self_odd`) and `= E₀ ≫ V ≫ T_(n+1)` for even `i`
(`_even`), where `T_(n+1) = τ_n ≫ (T_n ⊗ 1_i)` (`lastToFirstHom_append_self`). These use
`τ g = τ D E` (odd) and `τ g = τ E` (even) from the two-strand identities.
Next: the induction assembly in the `Ind.tmul` target: (K) for `n+1` from (K) for `n` via
these two steps, cancelling `D₀`/`E₀` with `PrependDotCancellation`/`LinearDotCancellation`.

**Right annihilators of the target (checked).** `CyclotomicAction/PrefixQPInduction.lean`
defines `PrependKills z` (every `r z` acts by zero on `φ(1)` in `Ind q`) and proves closure
under left multiplication, sums, scalars, right multiplication by `φ(x)` and by the first
dot `x₁` (`PrependKills.mul_prepend`, `mul_firstDot`), membership of `φ(ker q)`
(`prependKills_of_cyclotomicMk`), and square cancellation `PrependKills.of_sq_sub`:
`PrependKills (z (x₁² − φ c)) → PrependKills z` for every `c`. The morphism-level form:
`KillE w Y` (the corner of `Y ∈ End(i :: w)` is `PrependKills`), closed under
postcomposition; precompositions preserving it form `goodSubalgebra`, containing
`1_i ⊗ f` and `x₁` (`goodE_whiskerLeft`, `goodE_dotZero`); `KillE.of_sq_sub` cancels
`x₁² − 1_i ⊗ c`. `CyclotomicAction/PrefixQPKilling.lean`: `killE_whiskerLeft_comp`
(`(1_i ⊗ g) ≫ Y` kills when `g` lies in the old cyclotomic kernel) and (K) with an
arbitrary right context, `killE_relation_context`: on `i :: (μ ++ [i] ++ σ)`,
`((V_(μ++[i]) ≫ (T_μ ⊗ 1_i)) ⊗ 1_σ) ≫ f_i(x₁)` kills.

**Global QP identity, eq. (3) (checked).** `CyclotomicAction/PrefixQPEquation.lean`
proves `qpIdentity μ`: for every word `μ`, `(V_μ ≫ T_μ − A_μ) ≫ f_i(x₁)` lies in `KillAll μ`
(its right whiskering by every `1_σ` is `KillE`). Here `A_μ = qpProduct μ` is the ordered
product over the letters `μ_b` of `Q_(i,μ_b)(x₁, x_(b+2))` for `μ_b ≠ i`, of
`(x_(b+2) − x₁)²` for `μ_b = i` odd, and of `−1` for `μ_b = i` even. The even factor
`−1` (instead of `1`) comes from the library's crossing convention for the even
same-colour intertwiner (`τ g = τ E`); it changes `A_μ` by a sign only and does not
affect the balance argument. Proof by snoc induction: distinct letters by
`moveHom_lastToFirstHom_append_ne` and good precomposition by `Q_ix`; odd repeated
letters by (K) in context, cancellation of `x₁² − 1_i ⊗ x_(n+1)²` (`KillAll.of_sq_sub`)
and `(x_(n+2) − x₁) D₀ = D₀ (x_(n+2) − x₁)`; even repeated letters by
`KillAll.of_linear_even`. Arbitrary colours, parities and words.
Next: P balance (`DeformedGlobalQP.md` §4), the ideal sum, the projective resolution
and local inversion, supplying the hypothesis of `globalRouquierFamily`; then
`RouquierMulticolour` for it.

**Normalizer and θ: forms to formalize.** The factor interface contains neither the
first-dot normalizer nor the bubble substitution θ; neither is formalized yet. When they
are, use these forms, not the integer-shift form of the manuscript's normality step:

* the normalizer is the coefficient-twisted automorphism `ρ(x₁) = x₁ − 2δⱼ`, where `δⱼ`
  is the odd deformation parameter of the coefficient ring (written `dⱼ` in
  `DeformedGlobalQP.md` §4 and `DeformedProjectiveResolution.md` §4), not the integer
  `2dⱼ` of a degree argument. At even cutoff `N` the identity `x fⱼ = fⱼ (x − 2δⱼ)` holds
  only modulo `δⱼ χ_m = 0` (its defect is `2 χ_m δⱼ`), so `ρ` is defined on `A_N`, not on
  the free coefficient ring. The parity action of `ρ` on coefficients as stated in the
  manuscript is incorrect and must be rederived from the local relation before use;
  only the fact that `ρ` fixes `x²` is relied on in the projectivity argument;
* θ (`SwappedNondegeneracy.md` §4) is defined on the untruncated coefficient algebra
  (symmetric functions, or a free algebra), not on `A_N`: it does not preserve
  `δ χ_m = 0`. Recovery uses θ only before the quotient map `q_first`, as written there.

## Swapped-action interfaces: factor relations and upward module action

**Factor side (input F1 of `SwappedActionAssembly.md`).** A factor model is a
`RouquierFamily T` together with `RouquierMulticolour T Sc`
(`OddMath/SKM/RouquierMulticolour.lean`). The latter records the relations
of `Presentation.Rel` that `RouquierFamily` omits, in bicategorical order
(the word `[up i, up j]` at rightmost region `a` is `E j ≫ E i`; `cross i j`
is `crossL [] i j []`; a dot on the rightmost letter acts on the first
factor): `quadZero`, `quadNe` (1.7, `i ≠ j`, parameters `Sc`),
`slideLeft`, `slideRight` (1.8, `i ≠ j`), `braid` (1.9, all triples except
`i = k ≠ j`) and `braidEq` (its corrected form), and `invNe` (1.12): the
sideways crossing `crossMate (adj i h₃) (adj i h₂) (cross i j …)` is an
isomorphism for `i ≠ j`. `crossMate` is the cup–crossing–cap mate;
`crossMate_eq_rouquierMate` identifies it with `rouquierMate` on equal
colours. A factor construction (the deformed ELV kernels) should produce
these two structures. F2 (probe left adjunction) is the existing
`RouquierLeftAdjoints`; F3–F4 (reservoir bounds, contents) are not yet
packaged.

**Consumer side.** The finite-colour swapped action, evaluated on one Hom
sector at rightmost weight `μ`, is to be supplied as
`UpwardModuleAction D Sc μ` (`OddMath/QuiverHecke/UpwardModuleAction.lean`):
modules `V t` on upward words, `act` with `act_id` and `act_comp`.
`UpwardModuleAction.bubbles` is the derived algebra action of `SYM` through
`betaSYM` and `bubAt` (multiplicativity proved from `bubAt_comp`).
`toReservoirVacuumEvaluation` turns an upward action plus vacuum,
reservoir, recovery maps, windows and affine coordinates into
`ReservoirVacuumEvaluation`; its `bubbles_eq` holds by definition. The
remaining content of the vacuum detection is then exactly
`NormalizedBubbleFormula` and `affine_coordinates`.

**Mixed block `U` (checked).** `OddMath/SKM/RouquierHomDistinctMixed.lean`
formalizes `SwappedDistinctMixedMates.md` (7), (8) and the `U` half of (15)
for a fixed pre edge `E` and an arbitrary even post adjunction `E' ⊣ F'`,
shifted by `κ` (source) and `τ` (target); the content case is
`homContentPostAdjunction`, which is `homShiftPostAdjunction (W.adj i h) _
(homContentShift D i β)` by definition. `homDistinctMixedMate` is the literal
unit–`J⁻¹`–counit word with `J = homMixedInterchange E E' κ τ`;
`homDistinctMixedMate_eq` proves (8) in the form
`U_H = (-1)^(κ(κ+τ)) · E◁(z_κ(H)▷F') ; α⁻¹ ; z_τ(E≫H)⁻¹▷F'`;
`homDistinctMixedMateInv`, `homDistinctMixedMate_inv_products`,
`homDistinctMixedMate_isIso` give (15); `homDistinctMixedMate_mem` its
parity `κ + τ`. The exponent is the written `tr` of (8) with `t = κ`,
`r = κ + τ`; the Lean formula states `U` itself, i.e. (8) solved for `U`.

**Mixed block `V₀` (checked).** `OddMath/SKM/RouquierHomDistinctMixedPre.lean`
formalizes `SwappedDistinctMixedMates.md` (3), the `V₀` line of (7) and (9),
for a pre edge `E` with a shifted left adjunction `A : F ⊣ E` of parity `σ`
and an arbitrary post edge `E'` with shifts `t` (source), `u` (target).
`homDistinctMixedPreMate` is the literal unit–`J`–counit word with
`J = homMixedInterchange E E' t u`, for any two precomposition adjunctions
`homPre E ⊣ homPre F ⋙ S_σ`; `homDistinctMixedPreMate_eq` proves (9),
`V₀_H = (-1)^(σu) · z_t ; z_σ(F≫H)▷E' ; α ; F◁z_u(H≫E')⁻¹ ; z_σ⁻¹`, given that
their unit and counit are the normalized words (3) of `A`. Supporting lemmas:
`ShiftedSuperAdjunction.unit_slide` (a parity-`q` map slides through the unit
with `(-1)^(σq)`) and `ShiftedSuperAdjunction.left_triangle_post` (the zigzag
on `F` whiskered by a post edge is the associator).
`homContentPreAdjunction_counit_app` gives the counit word (3) for an
arbitrary `RouquierLeftAdjoints L`, and `homContentDistinctMixedPreMate_eq`
is (9) for the content adjunctions.

**Mixed block `V`, dots and inverses (checked).**
`OddMath/SKM/RouquierHomDistinctMixedDots.lean` formalizes (13)–(15) for even
dots, in a source-side form. `homDistinctMixedPreMateDot Φ` is the mate of
`J ≫ S_u(Φ)` for an endomorphism `Φ` of `(E ≫ Z) ≫ E'`; it only depends on
`Φ ≫ ε ▷ E'`. `MixedTransport g Φ` (`J ≫ S_u Φ = E ◁ g ≫ J`) is closed under
`comp`, `add` and `smul`. It holds for the post dot (`mixedTransport_post`,
`g = S_t(Z ◁ y)`) and for even middle maps (`mixedTransport_middle`, via
`homMixedInterchange_naturality_even`).
`homDistinctMixedPreMateDot_eq_comp` is (13): `V(Φ) = g ≫ V₀`.
The probe dot is the Mathlib conjugate `homPreDotConj` of `x ▷ (-)` along the
precomposition adjunction. `homPreDotConj_counit` gives
`(x ▷ Z) ≫ ε = E ◁ c(x) ≫ ε`, i.e. the cup–dot–cap word (10). Further:
`homPreDotConj_comp` (it reverses composition), `homPreDotConj_inv` ((11):
even inverse dot ⇒ two-sided inverse) and `homPreDotConj_mem` (evenness, given
even unit and counit). `homDistinctMixedPreMateDot_monomial` is (13) for one
supported monomial. `homDistinctMixedPreMate_inv_products` is (15) for `V₀`
with the explicit inverse `homDistinctMixedPreMateInv`.
`homDistinctMixedPreMateDot_isIso` gives (15) for `V` from an invertible `g`.
`isIso_add_of_isNilpotent` is (14): `A + N` is invertible when `A` is
invertible and `N` is nilpotent and commutes with `A`.
Scope: only even dot powers are handled. The supported monomials of (12) have
even powers, but the relation `c(d^m) = ± c(d)^m` for an odd `d` (the sign
`p binom(m,2)` in (11)–(12)) is not formalized, since `d ▷ (-)` is not a
natural transformation. Probe invertibility and reservoir nilpotence enter as
hypotheses of the lemmas (an even inverse of `x`, nilpotence of `N`). They are
not fields of `RouquierFamily` or `RouquierMulticolour`.

**Post/post core (checked).** `RouquierHomDistinctPost.lean` defines the
literal mate (A8) of a postcomposed factor crossing along the two post
adjunctions (`homPostCrossMate`) and proves `homPostCrossMate_eq`: it is
postcomposition by the factor mate `crossMate`, conjugated by associators,
for a crossing of either parity (no crossing passes a unit or counit).
Hence `homPostCrossMateInv` is a two-sided inverse whenever the factor mate is
invertible, and `homPostCrossMate_isIso` supplies this for distinct colours
from `invNe`. The content shifts, i.e. the comparisons `E_src`, `E_tar` of
the post/post paragraph of `SwappedActionAssembly.md` §5, are added in the
shifted post/post entry below.

**Pre/pre entry (A9) (checked).** `RouquierHomDistinctPreMate.lean` defines
the factor left mate `leftCrossMate` of a crossing `E_d E_c ⟶ E_b E_a` along
left adjunctions `F_d ⊣ E_d`, `F_a ⊣ E_a` (unit of `F_d ⊣ E_d`, crossing,
counit of `F_a ⊣ E_a`), and the literal mate `homDistinctPreMate` of the
precomposed crossing along the two precomposition adjunctions (which carry the
parity shifts `σd`, `σa`). `homDistinctPreMate_eq` proves that the latter is
postcomposition by `leftCrossMate`, conjugated by associators and the shift
isomorphisms, times `sign(σa + σd r + r σa + σd σa)` for a crossing of
parity `r`; the sign is the slide of the crossing through the unit
(`unit_slide`) and the super interchange with the counit. Hence
`homDistinctPreMateInv` is a two-sided inverse whenever `leftCrossMate` is
invertible (`homDistinctPreMate_isIso`), and
`homContentDistinctPreMate_isIso` gives this for distinct colours on the
content-shifted Hom functors under `LeftMateInvertible`.

**Next targets.** The pre/pre entry (A9) above and post/post with content
shifts (`RouquierHomDistinctPostShift.lean`) are checked. The remaining work
is the assembly into `UpwardModuleAction`; its skeleton and the list of open
obligations are in the section "Upward-action skeleton and relation
obligations".

**The interface `LeftMateInvertible`.** It asserts that for `i ≠ j` the left
mate of the distinct crossing along the chosen left adjunctions of
`RouquierLeftAdjoints` is invertible. It does not follow from
`RouquierMulticolour` with arbitrary `RouquierLeftAdjoints`: `invNe` inverts
the right mate `crossMate`, and the left mate is a different 2-morphism whose
invertibility needs the cyclicity of the crossing with respect to the chosen
left and right adjunctions, which an arbitrary choice of left adjunctions does
not provide. It is to be discharged from the ELV factor action: that
2-representation interprets the presented calculus, in which the leftward
crossing (defined with the left cups and caps) is a two-sided inverse of the
left mate, by the left-cyclicity relation of the distinct crossing and the
two inverse relations for `i ≠ j`. The final theorem therefore does not carry
this hypothesis.

**Shifted post/post entry (checked).** `RouquierHomDistinctPostShift` treats the
post/post mate with the parity shifts: raising postcomposition by the colour of
`E₁, E₂` carries `S_p`, and by the colour of `E₃, E₄` carries `S_q`; the shifted
adjunctions are `homPostAdjunction ⋯ ⋙ S_p ⊣ S_p ⋙ homPostAdjunction ⋯` as in
`homContentPostAdjunction`. The shifted crossing `homShiftedPostCrossing` is
`Y ◁ t` transported along the two removals `Θ = S_p(z_q ▷ E₂) ; z_p` with
coefficient `1`, as in `MixedColourBlockCompletion.md` (4).
`homShiftedPostCrossMate_eq` proves, for `t` of parity `r`, that its literal mate
equals `G_src ≫ homPostCrossMate ≫ G_tar`, where `G_src = z_q ; (z_p ▷ F₁) ▷ E₃`
and `G_tar = z_q⁻¹ ▷ F₂ ; z_p⁻¹ ▷ F₂`, with **no residual sign**. The signs are
`pq` (moving the outer removal through `S_p(z_q ▷ E₂)`), `pp` (the shifted
counit), `qp` (the inner removal), `pr` (super interchange of `z_p ▷ F₁` with
`t`), and `p(p+r)` (the outer shift square); they sum to zero mod 2. This
confirms the residual sign `1` claimed for (A8) in the assembly note.
`homShiftedPostCrossMate_isIso` gives invertibility for distinct colours by
`invNe`, for all parities `p, q`.

**Odd-dot sign (not needed).** The odd-dot sign of (11)–(12) is not an
obligation of the assembly. A nonzero coefficient `t_{i,j;m,n}` of `Q_{ij}` has
`p(i) m = 0` in `Z/2`, so for odd `i` every supported exponent `m` is even and
`d^m` is an even map. The assembly therefore uses the conjugate
`homPreDotConj (d^m)` of the power itself, as `homDistinctMixedPreMateDot_monomial`
already does. The relation `c(d^m) = (-1)^{p binom(m,2)} c(d)^m` concerns the odd
transpose `c(d)` of a single dot, which never occurs.

**Next targets.** (iii) Componentwise assembly into `UpwardModuleAction`, which
also needs the packaged probe and reservoir data and a check of every relation of
the presentation. (iv) F3–F4.

**Correction to the equal-colour mixed crossing (A6).** An exact check in the
smallest mixed case (one odd and one even colour, small probe and reservoir)
shows that for an even colour (p=0) the matrix (A6), with `a=(x-y)^-1`, gives
`τx₁-x₂τ=-1` on the mixed summand, and the jij braid relation fails there.
The correct entry is `a=(y-x)^-1`, equivalently (A6) multiplied by `-q`
(the scalar already used on the pure probe crossing). The same correction
applies to (2)–(4) of `SwappedHomInversion.md` for p=0; both documents now
carry the corrected entry. The §5 tables of `SwappedHomInversion.md` and the
even bubble computations of `SwappedVacuumBubbles.md`,
`SwappedVacuumNonpositiveBubbles.md` are still written with the earlier sign
and are marked as proposed for even colours until rechecked. The odd formula
`a=(x-y)(x²-y²)^-1` is correct. The check also fixes `J_ij=id`, the
distinct-colour crossings `J^-1` and `Q_ij J` with `Q` itself (not the
twisted `Q^alg`). The normalized even-colour bubble at height 0 picks up the
same factor `-q`. The Lean results on the mixed blocks above are stated for
an abstract crossing and do not use (A6).

Neither structure is instantiated here. The open part of the third
obligation is to build `UpwardModuleAction` from a `RouquierFamily` with
`RouquierMulticolour`, through the content-shifted Hom functors, the
distinct-colour mate inverses of `SwappedActionAssembly.md` §5 and the
mixed blocks.

## Upward-action skeleton and relation obligations

**Skeleton (checked).** `OddMath/QuiverHecke/SwappedAssembly/`:

- `Interpretation.lean`: `LayerRep S R` (a module `M a` for each object and a
  linear map `act L : M L.dom → M L.cod` for each layer); `LayerRep.toLocal`
  turns it into a `LocalInterpretation` with `κ = id`. The relations of
  `SKM.Rel` are split into the groups `RelGroup` (`relGroup`):
  quad = `quadEq`, `quadZero`, `quadNe`; slide = `slideL`, `slideLEq`,
  `slideR`, `slideREq`; braid = `braid`, `braidEq`; zigzag = `zigE`, `zigF`;
  inversion = `invNe₁`, `invNe₂`, `invP₁`–`invP₅`, `invM₁`–`invM₅`;
  windowZero = `dcupZero`, `dcapZero`. Each group is a Prop obligation
  (`QuadRelations`, `SlideRelations`, `BraidRelations`, `ZigzagRelations`,
  `InversionRelations`, `WindowZeroRelations`): every relation of the group,
  whiskered by any `u`, `v`, evaluates to `0`. `InterchangeLaw Q` is the
  interchange obligation (it carries the Koszul sign of odd generators).
  `SwappedObligations Sc Q` bundles the seven obligations;
  `SwappedObligations.functor` is `Presentation.lift` of the induced
  interpretation, and `SwappedObligations.upwardModuleAction μ` is the
  resulting `UpwardModuleAction D Sc μ` (modules `Q.M` of the upward words at
  rightmost weight `μ`, action by the lifted functor).
- `Sectors.lean`: sectors `(b, c) ∈ (I →₀ ℕ)²` (probe content `b`, reservoir
  content `c`), the summand paths `SPath w s t` of a word (each letter takes
  the probe or the reservoir side; finitely many from each sector,
  `SPath.finite`), and `ProbeReservoir k B D Sc`: a probe family `T` with left
  adjoints `leftAdj`, a reservoir family `W`, their `RouquierMulticolour`
  data and the probe and reservoir highest weights `ΛP`, `ΛR`. `P.H s` is the
  Hom sector of `s`, `P.step` the content-shifted pre/post `E`/`F` functor of
  one letter and side, `P.pathFunctor p` the composite along a path
  (`pathFunctor_append`), and `wt_nextSector` the weight bookkeeping.
- `Matrices.lean`: the objects `C_λ` as finite-support matrices.
  `P.Mod Gs Ys a` is the module of entries `Gs s ⟶ F_p (Ys t)` over summand
  paths `p` of `a.word` with `wt t = a.endR`. `Generators` is the interface for
  the generator images: one field per shape (`dot`, `cross`, `cup`, `cap`,
  `lcross`, `dcup`, `dcap`), each a component `F_p Z ⟶ F_p' Z` for every pair
  of summand paths of the bottom and top boundaries. `layerMap` acts on the
  middle of a layer and by the identity on its whiskers; `P.layerRep Gs Ys gens`
  is the resulting `LayerRep`.

The leftward crossing has no relation constructor of its own: it is the
generator `lcross`, and the relations it must satisfy are the inversion
relations. The skeleton is stated over `D` itself; the pairing extension
`λ ↦ (λ, 0)` is not part of it. The factor hypotheses F1–F4 (in particular the
nilpotence used for the (A6) denominators) enter in the generator modules.

**Generator images: component formulas.** These are the entries that the
modules `Generators/*.lean` define, in the conventions of `Sectors.lean` and
`Matrices.lean`. A summand path of a word is a choice of side, P (probe) or
R (reservoir), for each letter; the path functor applies the leftmost letter
last, so a path `(σ₁, σ₂)` of a two-letter word at left sector `(b, c)` has
object `F_{σ₁}(F_{σ₂} Z)`. Write `A_i = homContentPreE` (up letter on P),
`B_i = homContentPostE` with `betaP` the probe content of the sector to the
left of the letter (up letter on R), and their lowering partners
`homContentPreF`, `homContentPostF`. In the notation of
`SwappedActionAssembly.md` a word is read chronologically, so the path
`(P, R)` is its `BA` and the path `(R, P)` its `AB`. All entries not listed
are zero. The image of a generator of parity `r` is the parity-`r` component.

- `dot i`: path `(P)`: the inherited pre dot `T.dot i _ ▷ Z`
  (`homContentPreSuperDot`); path `(R)`: the shifted post dot
  `homContentPostDot` (`betaP = b`).
- `cross i j`, `i ≠ j`:
  - `(P,P) → (P,P)`: the inherited reversed-label factor crossing,
    `α⁻¹ ; T.cross j i _ ▷ Z ; α`, without sign.
  - `(R,R) → (R,R)`: the post transport of `Z ◁ W.cross i j _`, by the even
    comparison `S_(p_j P(b))(β_(M_j, p_i P(b))⁻¹) ; c_(p_j P(b), p_i P(b))`
    of `SwappedActionAssembly.md` §2 (the two-colour form of
    `homContentPostWordIso`).
  - `(P,R) → (R,P)`: `J_ij`, and `(R,P) → (P,R)`: `J_ji⁻¹ ; Q_ji(x, y)`,
    where `J_ij = homMixedInterchange (T.E i _) (W.E j _) κ τ Z` goes from the
    path `(P,R)` of `Eᵢ Eⱼ` to the path `(R,P)` of `Eⱼ Eᵢ` (these are the only
    type-correct directions; an earlier version of this list had them
    inverted), with `κ`, `τ` the `homContentShift`s of the inner and outer
    reservoir letters at their own sectors (not `homContentMixedInterchange`,
    whose content labels differ from the sector labels by `2α_i`), and
    `Q_ji(x, y)` the parameter polynomial of `Sc` on the target `(P,R)` of
    `Eⱼ Eᵢ`, `x` the pre dot of its left letter and `y` the post dot of its
    right letter: `t_ji x^(d_ji) + t_ij y^(d_ij) + Σ s_ji^(pq) (y^q ; x^p)`,
    or `t_ji` if `d_ji = 0` (the original `Q`, not `parameterTwist`).
- `cross i i`, with `q = (-1)^(p_i)`:
  - `(P,P) → (P,P)`: `homContentCrossing` (that is `-q` times the inherited
    factor crossing);
  - `(R,R) → (R,R)`: `homContentPostCrossing`;
  - the mixed block (A6) with `a = (y - x)⁻¹` for `p_i = 0` and
    `a = (x - y)(x² - y²)⁻¹` for `p_i = 1`, `a ∈ End(F_R(F_P Z))`:
    `(R,P) → (R,P)`: `a`; `(P,R) → (R,P)`: `J`;
    `(R,P) → (P,R)`: `-(a ; a ; J⁻¹)` (`homContentMixedSwap`);
    `(P,R) → (P,R)`: `-(J ; a ; J⁻¹)` (chronological `;`, `J` from `(P,R)` to
    `(R,P)`), for both parities.
  Check: on the path `(R,P)` the left strand is the outer letter `R`, so the
  diagonal components of `slideREq` and `slideLEq` there are
  `a ; y - q (x ; a) = 1` and `y ; a - q (a ; x) = 1` (consistent with
  `homContentCrossing_slide`), which hold for `a` above in both parities;
  the square of the block vanishes and its `(P,R)` diagonal is forced to be
  `-(J ; a ; J⁻¹)` by the off-diagonal components of `quadEq`. (An earlier
  version of this list had `-q a` and `q (J⁻¹ ; a ; J)`: in
  `CrossingNormalization.md` the letter `A` is the reservoir, so its `AB` is
  the path `(P,R)`; the earlier list kept the sign on `(R,P)`, which is wrong
  at even colours.)
  The coefficient `a` enters as data with its two characterizing identities
  (`a ; (y - x) = 1 = (y - x) ; a`, resp. `a ; (x² - y²) = x - y`, natural in
  `Z`); its existence from F2–F3 (unit probe dot, nilpotent reservoir dot)
  is a separate lemma.
  Checked: `Generators/Cross.lean` (`crossImage c i j ν`, with entries
  `crossNeEntry`, `crossSameEntry`). The coefficient is the structure
  `CrossCoeff` (field `a` on the path `(R,P)` of `Eᵢ Eᵢ`), and its identities
  are `CrossCoeff.IsInverse` (not yet used by the image); `Q` is `mixedQ`, the
  mixed interchange `mixedJ`. The `(P,P)` and `(R,R)` entries of distinct
  colours end with the transport of the target strand along the equality of
  right sectors (`preE_obj_heq`, `postE_obj_heq`).
- `cup i`, `cap i`: diagonal. On `(R)`-letters the units and counits of
  `homContentPostAdjunction`; on `(P)`-letters those of
  `homContentPreAdjunction T _ T.leftAdjoints` (the inverse-defined left
  adjunction of the factor, F2; `ProbeReservoir.leftAdj` is not used).
  Checked: `Generators/CupCap.lean` (`cupImage`, `capImage`). The adjunction
  is taken at the left sector; the inner strand is identified with the
  adjoint along the propositional equality of the right sector with the left
  sector (`preE_obj_heq`, `postE_obj_heq`, `preF_obj_heq`, `postF_obj_heq`).
  The two-letter path splitting is `zeroTwo`, `twoZero`, `twoTwo`.
- `lcross i j`, `i ≠ j`: the block permutation of
  `SwappedActionAssembly.md` §5: `N_pre` (`homDistinctPreMateInv`, under
  `LeftMateInvertible T T.leftAdjoints`), `N_post` (inverse of
  `homShiftedPostCrossMate`), `U_ji⁻¹` (`homDistinctMixedMateInv`) and
  `V_ij⁻¹` (`homDistinctMixedPreMateInv`, with `G⁻¹` from (A15)).
  Checked: `Generators/Leftward.lean` defines `lcrossNeImage c i j ν` as the
  entrywise inverse of the sideways crossing: its entry from `p` to `p'` is
  `inv` of the entry `sigmaEntry c i j ν p' p Z` of `σ = sigmaL i j` (computed
  by `compList` for `upwardGens c`, the upward images with zero leftward
  generators) where that entry is invertible, and `0` otherwise. On a block
  permutation with invertible blocks this is the two-sided inverse, so
  `invNe₁`, `invNe₂` reduce to: the entries of `σ` vanish off the block
  permutation, and its four blocks are invertible (the four inverses above
  witness this).
- `lcross i i`, `dcup i n`, `dcap i n`: (A7) from the whole inverse of the
  same-colour augmented map at height `H = h_i(ν)`: `lcross = -r`,
  `dcup n = a_n` (`0 ≤ n < H`), `dcap n = b_n` (`0 ≤ n < -H`), zero outside
  these windows. The whole inverse enters as data with its two-sided inverse
  identities (the five products of §4 in each height regime). At even colours
  with `H = 0` its entries depend on the bubble normalization, which is kept
  as an explicit hypothesis until the independent recheck is done.
  Checked: these are the fields of the data structure `LeftwardData`
  (`lcrossSame`, `dcup`, `dcap`); the identities they must satisfy are the
  relations `invP₁`–`invM₅` and the window rules `dcupZero`, `dcapZero`.
- Assembly (checked, `Generators.lean`): `swappedGens c L : P.Generators`,
  with `swappedGens_lcross_of_ne`, `swappedGens_lcross_self`, and
  `compList_sigmaL_swappedGens` (the entries of `σ` for `swappedGens c L` are
  `sigmaEntry c`), from `compList_congr` (entries of a chain only depend on the
  images of the generators in its layers).

The relation modules may state their obligations against these formulas as a
hypothesis structure until the generator modules land.

**Post/post slide (checked).** `OddMath/SKM/RouquierHomPostCrossingSlide.lean`:
`homContentPostCrossing_slide_app` gives `c ; x_outer - q (x_inner ; c) = 1` for the
reservoir/reservoir entry `c = homContentPostCrossingApp` (the parity-`p_i` component of
`homContentPostCrossing`), with `x_outer = homContentPostDot` on the outer letter and
`x_inner` the outer functor applied to the inner `homContentPostDot`. This is the same
orientation as the pre/pre `homContentCrossing_slide`. It is deduced from the factor's
`slide_right` through `homContentPostWordIso`: `homContentPostDot_outer_wordIso` and
`homContentPostDot_inner_wordIso` transport the two dots to `Z ◁ (E ◁ x₂)` and
`Z ◁ (x₁ ▷ E)`. The two parity-shift signs cancel (`homShiftConjugationIso_naturality`),
and `SlideConj.conj_slide` transports the slide along the comparison.
**Same-colour slide blocks (checked).** `SwappedAssembly/SlideBlocks.lean`,
in an arbitrary preadditive category, reduces the four slide components of
the mixed block to identities of its diagonal entry. With `U = (R,P)`,
`V = (P,R)`, left/right dots `lU, rU`, `lV, rV`, `J : V ⟶ U` with two-sided
inverse `Ji`, and the block `b`, `J`, `-(b ; b ; Ji)`, `-(J ; b ; Ji)`:
`mixedBlock_slideL` (resp. `mixedBlock_slideR`) proves all four components
of `slideLEq` (resp. `slideREq`) from: the dots intertwine across `J` with
the sign `q` and the strands exchanged (`lV ; J = q (J ; rU)`,
`rV ; J = q (J ; lU)`), the two diagonal slide identities of `b`, and the
commutation of `b ; b` with the left (resp. right) dot.
`slide_of_inv_even` and `slide_of_inv_odd` supply these diagonal hypotheses
for `b = (l - r)⁻¹` when the dots commute, and for `b = (l - r) ; w` with
`w = (l² - r²)⁻¹` commuting with both dots when they anticommute
(`q = 1`, resp. `q = -1`).

**Interchange law (checked).** `SwappedAssembly/Interchange.lean`:
`ProbeReservoir.interchangeLaw` proves `InterchangeLaw (P.layerRep Gs Ys gens)`
from `GeneratorsSupernatural gens`: every entry `gens.image g p p'` is a
homogeneous supernatural transformation of parity `|g|` from the functor of
`p` to that of `p'`. The entry of either composite at an output path
`pu · qa · pm · qb · pr` is the double sum over the bottom paths `pa`, `pb` of
`g`, `g'`; termwise the two composites differ by moving `F_pm(η)` past `γ`,
which costs `(-1)^{|g||g'|}` (`eqToHom_map_comp_exchange`, in arbitrary
categories, with the path functors only as linear and parity-preserving).
Ill-formed layers act by zero, and the interchange preserves well-formedness
of the two layers (`valid_interchange_of_valid`). `LayerEntries.lean` holds
the tools: entries of a layer at an explicit concatenation
(`layerMap_apply_append`), transport of entries along equalities of objects
(`Mod.cast_apply`, with `SPath.append_assoc_heq`), and the composite of two
layers in `LayerRep.toLocal` (`LayerRep.res_op_op_ext`).
Remaining for the interchange: discharge `GeneratorsSupernatural` for the
generator images of item 1 below.

**Open obligations, one module each** (all under
`OddMath/QuiverHecke/SwappedAssembly/`):

1. Generator images, supplying the fields of `ProbeReservoir.Generators`:
   - `Generators/Dot.lean` (**checked**): `dotImage i ν`, with
     `dotImage_probe` (`T.dot i _ ▷ Z`) and `dotImage_reservoir`
     (`homContentPostDot` at the probe content of the left sector); zero between
     different summands. The helper `oneLetterDiag` builds a one-letter
     generator from its diagonal components.
   - `Generators/Cross.lean` (**checked**): `crossImage c i j ν`.
   - `Generators/CupCap.lean` (**checked**): `cupImage`, `capImage`.
   - `Generators/Leftward.lean` (**checked**): `upwardGens`, `sigmaEntry`,
     `lcrossNeImage`, `LeftwardData`.
   - `Generators.lean` (**checked**): `swappedGens c L`.
   - `Generators/CrossCoeffExistence.lean` (**checked**): existence of `c`.
     `rpPreDot_comp_rpPostDot`: on the path `(R,P)` of `Eᵢ Eᵢ` the probe dot
     `x` and the reservoir dot `y` supercommute, `x ≫ y = (-1)^{p_i} (y ≫ x)`
     (super-interchange through the parity shift). `CrossCoeffInputs`: `x` is a
     unit (F2) and `y` is nilpotent (F3), pointwise; `CrossCoeffInputs.of_factor`
     derives it from invertibility of every probe dot and nilpotence of every
     reservoir dot as 2-morphisms. `crossCoeffOfInputs h` is `(y - x)⁻¹` at even
     colours and `(x² - y²)⁻¹ (x - y)` at odd colours (`x - y` commutes with
     `x² - y²` since `x y = -y x`), and `crossCoeffOfInputs_isInverse` proves
     `CrossCoeff.IsInverse`. Interface for the instance: the factor dot
     hypotheses of `of_factor` (F2, F3).
   Remaining for the action: the `LeftwardData` of (A7) with the relations
   `invP`/`invM`. Reduced (checked, `SwappedAssembly/LeftwardInverse.lean`) to the
   invertibility of the augmented maps; see "Leftward data from the inverses" below.
2. `WhiskerReduction.lean` (shared helper, **checked**): reduces `evalW` of a
   whiskered relation for `P.layerRep` to the unwhiskered matrix entries.
   `compLayer gens L p q Z : F_p Z ⟶ F_q Z` is the entry of a layer between
   summand paths of its boundaries (the generator image in the middle, the
   identity on the whiskers, zero when the outer parts differ); `compList`,
   `compDiag`, `compEval` are the entries of a chain, a diagram and a linear
   combination (sums over intermediate paths). `res_opList_ext_apply`: the
   evaluation of a chain in `layerRep` is the matrix product of its entries
   with the input family. `compList_whisker`, `compList_whisker_eq_zero`: the
   entries of `u ⊗ d ⊗ v` are block diagonal in the outer paths, with block
   `F_{pu}` applied to the entry of `d` at `F_{pv} Z`. Consumer interface:
   `relHolds_of_compEval gens r h : RelHolds Sc (P.layerRep Gs Ys gens) r`
   from `h : ∀ s t p q Z, compEval gens ((SKM.pres D Sc).rel r) p q Z = 0`,
   for all summand paths `p`, `q` of the unwhiskered boundaries and all
   `Z : P.H t`.
3. Relation modules, each proving its obligation for `P.layerRep Gs Ys gens`:
   - `Quad.lean`: `QuadRelations` (checked, conditional on `CrossQuad`; see
     below).
   - `Slides.lean`: `SlideRelations` (checked, conditional on `CrossSlide`;
     see below).
   - `Braid.lean`: `BraidRelations` (checked, conditional on `CrossBraid`;
     see below).
   - `Zigzag.lean`: `ZigzagRelations` (checked, conditional on `CupCapZigzag`;
     see below). `CupCapZigzag.lean`: `CupCapZigzag (swappedGens c L)`
     (checked, unconditional).
   - `Inversion.lean`: `InversionRelations` (checked, conditional on
     `SigmaPermutation` and `LeftwardData.IsInverse`; see below).
   - `WindowZero.lean`: `WindowZeroRelations` (checked, see below).
   - `Interchange.lean`: `InterchangeLaw` (checked, conditional on
     `GeneratorsSupernatural`, the supernaturality of the odd generator
     images; see above).
4. `Action.lean`: combines these into `SwappedObligations` and hence
   `upwardModuleAction`.

**Quadratic relations (checked).** `SwappedAssembly/Quad.lean`:
`quadRelations`: `QuadRelations` for `P.layerRep Gs Ys gens` from
`CrossQuad gens`. Each relation (1.7) is one matrix identity per pair of
summand paths `p`, `q` of `Eᵢ Eⱼ 1_ν` and object `Z`. The entry of the two
crossings is `crossCross gens i j ν p q Z`, the sum over summand paths `m` of
`Eⱼ Eᵢ 1_ν` of the two crossing images (`compDiag_crossCross`). The entries of
`n` dots on one strand are diagonal, equal to the `n`-th power (`compPow`) of
the one-dot entry `leftDot` (left strand, `compLayer` of `dot i` whiskered by
`up j`) or `rightDot` (`compDiag_leftDots`, `compDiag_rightDots`,
`compDiag_rightDots_leftDots`). `CrossQuad gens` asks: `crossCross` vanishes
for `i = j` and off the diagonal for `i ≠ j`; on the diagonal it is `t_ij` if
`d_ij = 0` and `t_ij x₁^{d_ij} + t_ji x₂^{d_ji} + Σ s_ij^{ab} x₂^b x₁^a`
(with `x₁ = leftDot`, `x₂ = rightDot`) otherwise. Supporting lemmas:
`compList_append`, `compDiag_comp` (entries of composites are matrix
products), `compEval_sub`, `compEval_smul`, `compEval_sum`, `compEval_of`.
`QuadSame.lean` (**checked**): `swappedGens_quadEq c L i ν p q Z` proves the
equal-colour field `quadEq` of `CrossQuad (swappedGens c L)` for every `c`
(no identity of `a` is needed). The paths of `Eᵢ Eᵢ` between two sectors are
`PP`, `RR`, or the mixed pair (`sum_paths_PP`, `sum_paths_RR`,
`sum_paths_mixed`; the number of probe summands is read off the `i`-th probe
content, `nextSector_fst_same`); `preCrossSame_sq`, `postCrossSame_sq` are the
factor relations `T.square`, `W.square` transported, and the four mixed
entries of (A6) cancel. `CrossEntries.lean`: `SPath.mk₂`,
`SPath.exists_eq_mk₂`, `leftDot_cons`, `rightDot_cons`.
`SlideSame.lean` (**checked**): `swappedGens_slideEq c hc hin L i ν p q Z`
proves the equal-colour slide fields `slideLEq` and `slideREq` of
`CrossSlide (swappedGens c L)` entry by entry, for `c.IsInverse` and the inputs
F2, F3 (`CrossCoeffInputs`: probe dot a unit, reservoir dot nilpotent on the
path `RP`). The `PP` entry is the factor slide of `T` conjugated by the
associator (`preCrossSame_slides`, via `conj_crossing_slides`); the `RR` entry
is the factor slide of `W` transported through the word isomorphism
(`postCrossSame_slides`); the four mixed entries are
`SlideBlocks.mixedBlock_slideL/R` with the dot intertwinings
`prPreDot_comp_mixedJ`, `prPostDot_comp_mixedJ` and the diagonal identities
`crossCoeff_diag` (`y a - q a x = 1`, `a y - q x a = 1`, `a²` commutes with both
dots; the odd case uses that `x² - y²` is invertible, which `IsInverse.odd`
alone does not give). Interface: the slides use `CrossCoeffInputs` in addition
to `IsInverse`; both hold for `crossCoeffOfInputs`.
`QuadNe.lean` (**checked**): `swappedGens_crossQuad c L : CrossQuad (P.swappedGens c L)`
for every `c` and `L`, with no further hypothesis. For `i ≠ j` a summand path of
`Eᵢ Eⱼ` is determined by its end sectors (`path_eq_of_ne`), so `offDiag` is vacuous and
`crossCross` reduces to the single partner path (`swappedGens_crossCrossNe`). The
probe/probe and reservoir/reservoir entries are the multicolour (1.7) of the probe and
reservoir families, whiskered and transported along the sector casts
(`probeCore_quad`, `resCore_quad`, `quad_of_heq`); the probe/reservoir entry is
`J ≫ J⁻¹ Q = Q`, and the reservoir/probe entry is `J⁻¹ Q J`, which is `qExpr` in the
transported dots (`mixedJ_inv_mixedQ_hom`). `quadZero`/`quadNe` then read off the
two branches of `qExpr`.

**Inversion relations (checked).** `SwappedAssembly/Inversion.lean`:
`inversionRelations`: `InversionRelations` for `P.layerRep Gs Ys
(P.swappedGens c L)` from two hypotheses. (1) `SigmaPermutation c i j ν` for
`i ≠ j`: in every pair of sectors the matrix of `σ : Eⱼ Fᵢ → Fᵢ Eⱼ` is a
permutation matrix (a bijection `f` of summand paths, zero entries off `f`)
with invertible entries. Then the entrywise inverse `lcrossNeImage` is a
two-sided inverse (`sigma_lcross_sum`, `lcross_sigma_sum`), which gives
`invNe₁`, `invNe₂` (1.11), (1.12). (2) `LeftwardData.IsInverse L c`: the
equal-colour relations `invP₁`–`invP₅`, `invM₁`–`invM₅` (1.13), (1.14) hold
entrywise; these identities characterize `L` as the components of the
inverses of the augmented maps. Supporting: `compEval_dg_append` (the entry
of a two-part normal-form diagram is the matrix product of the entries),
`compDiag_lcrossL`, `compDiag_sigmaL_swappedGens`. Remaining: prove
`SigmaPermutation c` from the block structure of `SwappedActionAssembly.md`
§5, and construct `L` with `L.IsInverse c` (A7).

**Slide relations (checked).** `SwappedAssembly/Slides.lean`:
`slideRelations`: `SlideRelations` for `P.layerRep Gs Ys gens` from
`CrossSlide gens`. Each relation (1.8) is one matrix identity per pair of
summand paths `p` of `Eᵢ Eⱼ 1_ν`, `q` of `Eⱼ Eᵢ 1_ν` and object `Z`; dots are
diagonal, so a dot followed by a crossing has entry `leftDot p ≫ cross p q`
(`compDiag_leftDot_cross`, `compDiag_rightDot_cross`) and a crossing followed
by a dot `cross p q ≫ rightDot q` (`compDiag_cross_rightDot`,
`compDiag_cross_leftDot`). `CrossSlide gens` asks: for `i ≠ j`,
`leftDot p ≫ cross = (-1)^{|i||j|} cross ≫ rightDot q` and
`cross ≫ leftDot q = (-1)^{|i||j|} rightDot p ≫ cross`; for `i = j` the same
differences with sign `(-1)^{|i|}` equal the identity entry (`eqToHom` on the
diagonal, zero off it). **`CrossSlide (swappedGens c L)` is checked**
(`SlideAssembly.lean`: `swappedGens_crossSlide c hc hin L`, for `c.IsInverse`
and `CrossCoeffInputs`). The equal-colour fields are `swappedGens_slideEq`
(`SlideSame.lean`); the distinct-colour fields are `swappedGens_slideNe`. For
`i ≠ j` only the four pairs of paths `PP→PP`, `RR→RR`, `PR→RP`, `RP→PR` have
equal right sectors. `SlideNe.lean` proves the slides of each distinct-colour
crossing entry: `preCrossNe_slideL/R` and `postCrossNe_slideL/R` (the factor
slides `probeRel.slideLeft/Right`, `reservoirRel.slideLeft/Right` transported
through the associator, resp. the word isomorphism `postPairIso`), and
`mixedJ_ne_slides`, `mixedJinvQ_ne_slides` for `J` and `J⁻¹ Q_ji`: the signed
intertwinings `prPreDot_comp_mixedJ_ne`, `prPostDot_comp_mixedJ_ne` (sign
`(-1)^{|i||j|}` from super interchange through the parity shift), the
supercommutation `prPostDot_comp_prPreDot` of the two dots on `PR`, and
`mixedQ_comm` (`Q_ji` commutes with both dots: in each monomial `x^a y^b` of
`Q` the exponent of the odd variable is even, `comp_qExpr`).
`SlideAssembly.lean` moves the entry slides to arbitrary paths by `HEq`
transport (`slideL_of_heq`, `twoTwo_two_heq`, `leftDot_two_*_heq`,
`rightDot_two_*_heq`).

**Braid relations (checked).** `SwappedAssembly/Braid.lean`:
`braidRelations`: `BraidRelations` for `P.layerRep Gs Ys gens` from
`CrossBraid gens`. The entry of each side of (1.9) is a triple matrix
product of crossing entries over the summand paths of the intermediate
words (`braidLeft`, `braidRight`; `crossEntry gens ν u i j v` is the entry
of the one-layer crossing diagram `crossL u i j v`). The dot correction
terms of `braidEq` are diagonal, with entries products of powers of the
one-dot entries `dotEntry` on the three strands (`compDiag_dots_dots`,
`compDiag_dots_dots_dots`). `CrossBraid gens` asks `braidLeft = braidRight`
unless `i = k ≠ j`; for `Eᵢ Eⱼ Eᵢ`, `i ≠ j`, equality off the diagonal and,
on the diagonal, `braidLeft - braidRight` equal to the `Q_ij` divided
difference in the dot entries, with the signs and scalars of `braidEq`.
Remaining: prove `CrossBraid (swappedGens c L)`.
Whisker reduction of the crossing entries (checked,
`SwappedAssembly/BraidEntries.lean`): on a three-letter word the left
crossing entry `crossEntry gens ν [] i j [up k']` on paths `pg.append pv`,
`qg.append pv` is `gens.cross i j (wt ν [up k'])` applied to the image of `Z`
under the third summand (`crossEntry_left`) and vanishes when the third
summands differ (`crossEntry_left_eq_zero`); the right crossing entry
`crossEntry gens ν [up a] i j []` is the step-functor image of
`gens.cross i j ν` (`crossEntry_right`) and vanishes when the first summands
differ (`crossEntry_right_eq_zero`). The weight labels of the first letter in
the layer and in the target word differ only propositionally; the generic
transports `compLayer_cast_eq_of_path`, `compLayer_cast_eq_zero_of_path` absorb
them. Next: the colour patterns of (1.9) for `swappedGens c L`, starting with
the mixed probe/reservoir block of `iii` ((5A)/(5B) of
`ThreeStrandSectorBraid.md`).
Sector algebra of the `iii` braid (checked,
`SwappedAssembly/BraidSame/SectorAlgebra.lean`): on the block of paths
`{AAB, ABA, BAA}`, transported to the first path by `Φ₀ = 1`, `Φ₁ = J`,
`Φ₂ = J ≫ J`, the three-strand crossings become the matrices
`sectorU D γ = [[D,0,0],[0,-γ,1],[0,-γ²,γ]]` and
`sectorV D δ = [[-δ,1,0],[-δ²,δ,0],[0,0,D]]` (the last entry `D` is (5A)).
`sectorBraid`: `U V U = V U V` follows from `D² = 0`, `Dγ = δD + γδ`,
`Dδ = γD - δγ`, `γδ² = δ²γ`, `γ²δ = δγ²` (read in any ring; apply in the
opposite of `End`). These four relations are proved from the dot algebra:
`sectorRelations_even` (commuting dots `x₁, x₂, z`, `Dz = zD`, slides
`x₁D - Dx₂ = 1 = Dx₁ - x₂D`, `γ = (z - x₁)⁻¹`, `δ = (z - x₂)⁻¹`) and
`sectorRelations_odd` (anticommuting dots, `Dz = -zD`, slides
`x₁D + Dx₂ = 1 = Dx₁ + x₂D`, `γ(x₁² - z²) = x₁ - z`, `δ(x₂² - z²) = z - x₂`
with `x₁² - z²`, `x₂² - z²` units).
(5A) for the `iii` braid (checked,
`SwappedAssembly/BraidSame/MixedInterchangePair.lean`):
`preCrossSame_mixedJ_pair`: the probe crossing on the two left letters of
`PPR`, followed by the two mixed interchanges `PPR → PRP → RPP`, equals the
interchanges followed by the shifted probe crossing on the two right letters
of `RPP`, without sign. Generic form `homMixedInterchange_pair_whiskerRight`
(any homogeneous 2-morphism on `E₁ ≫ E₂`, equal outer shifts; the inner
shift cancels, `homMixedInterchange_pair`). This is `PairedHomInterchange.md`
§3 with all shifts retained; no discrepancy with the written proof. Next:
transport the dot entries to `x₁, x₂, z` on the first path, then assemble the
block; then (5B) on `{PRR, RPR, RRP}`.

**Window-zero relations (checked).** `SwappedAssembly/WindowZero.lean`:
`layerMap_eq_zero` (a layer whose generator image has only zero components
acts by zero) and `windowZeroRelations`: `WindowZeroRelations` for
`P.layerRep Gs Ys gens` from `DcupDcapWindowZero gens`, the assignment of zero
to `dcup i n` with rightmost weight `ν` when `⟨hᵢ, ν⟩ ≤ n` and to `dcap i n`
when `-⟨hᵢ, ν⟩ ≤ n`. Nothing about the images inside the windows is used, so
this does not depend on the even-colour bubble normalization at height `0`
(both windows are empty there). Discharged for the swapped generators:
`swappedGens c L` assigns `dcup i n ν` the entry of `L.dcup` inside the window
`n < ⟨hᵢ, ν⟩` and zero outside it (likewise `dcap` inside `n < -⟨hᵢ, ν⟩`), as in
(A7); `swappedGens_windowZero c L : DcupDcapWindowZero (swappedGens c L)` holds
with no hypothesis, and `swappedGens_dcup_of_lt`, `swappedGens_dcap_of_lt`
identify the in-window entries with those of `L` (`Generators.lean`).

**Zigzag relations (checked).** `SwappedAssembly/Zigzag.lean`:
`zigzagRelations`: `ZigzagRelations` for `P.layerRep Gs Ys gens` from
`CupCapZigzag gens`. The boundary of `zigE` (resp. `zigF`) is the single strand
`Eᵢ` (resp. `Fᵢ`), whose summand path is unique (`SPath.eq_of_single`), so each
relation is one matrix identity per summand path `q` of that strand and object
`Z`: the sum over the summand paths `m` of the cup's codomain and `r` of the
cap's domain, restricted to the pairs for which the two middle paths agree as
paths of the three-letter word (`zigE_word`, `zigF_word`), of the composite
"cup entry, transport, cap entry" is the identity. `CupCapZigzag.zigE` and
`.zigF` state exactly these identities; `zigE_entry` and `zigF_entry` identify
them with the entries `compList` of the two-layer diagrams (in the `zigF` case
the left strand of the cap layer has right weight `wt ν [up i, dn i]`, only
propositionally equal to `ν`; `SPath.cast_cons_col` transports the path). No obstruction: the reduction is exact,
and the generator modules must prove `CupCapZigzag` for their cup/cap images
(the right adjunction (1.10) of the Hom-sector functors).

**`CupCapZigzag` for the swapped generators (checked).**
`SwappedAssembly/CupCapZigzag.lean`: `cupCapZigzag_swappedGens c L :
CupCapZigzag (P.swappedGens c L)`, with no hypotheses beyond the
`ProbeReservoir` data; more generally `cupCapZigzag_of` for any generators whose
cup and cap are `cupImage` and `capImage`. Proof: a closed path of a lowering
and a raising strand of one colour stays in one summand
(`SPath.side_eq_of_closed`, by the content bookkeeping of `nextSector`), so in
each double sum exactly one pair `(m, r)` survives: both run through the summand
`σ` of the given strand. On that pair the cup and cap entries are the unit and
counit of one content-shifted adjunction (`homContentPostAdjunction` for
`σ = false`, `homContentPreAdjunction` for `σ = true`), taken at indices equal
up to the sector equality `nextSector (up i) σ (nextSector (dn i) σ s) = s`
(or its `zigF` analogue), and the composite is the identity by the triangle
identities (`triangle_left_of_eq`, `triangle_right_of_eq`). So `ZigzagRelations`
holds for `P.layerRep Gs Ys (P.swappedGens c L)` unconditionally.

**Supernaturality of the swapped dot, cup and cap (checked).**
`SwappedAssembly/Supernatural/Basic.lean`, towards `GeneratorsSupernatural
(P.swappedGens c L)`: `dotImage_supernatural` (parity `p_i`), `cupImage_supernatural`
and `capImage_supernatural` (parity `0`), for all summand paths of the boundaries, with
no hypotheses beyond the `ProbeReservoir` data. Tools: `castH h : P.H b ⥤ P.H a`, the
transport of Hom-sector objects along `h : a = b` (additive, linear, a superfunctor),
with `pathFunctor_one`, `pathFunctor_two` writing the path functor of a one- or
two-letter path as `castH e` followed by the strand functors; the reductions
`oneLetterDiag_supernatural`, `zeroTwo_supernatural`, `twoZero_supernatural` reduce a
one-letter diagonal, empty-to-two-letter or two-letter-to-empty matrix to its
components at arbitrary sectors; the generic `IsSupernatural.of_eq_conj` (conjugation by
`eqToHom` along equalities of functors), `isSupernatural_eqToHom`,
`isSupernatural_zero`. Components: the dot is `homPreTransform (T.dot i _)` on the probe
summand and `homContentPostDot` (`homContentPostDot_power_supernatural`, `n = 1`) on the
reservoir summand; the cup and cap are the unit and counit of the content-shifted
adjunctions (even natural transformations, `*_unit_mem`, `*_counit_mem`), whiskered by
`castH` and composed with `eqToHom` families between the transported strand functors
(`preE_functor_heq` and its three analogues).
Remaining for `GeneratorsSupernatural (P.swappedGens c L)`: the crossing (its
entries involve the scalar `c.a`, the polynomials of `Sc` and the mixed interchange)
and the leftward crossings (`LeftwardData`).

**Supernaturality of the swapped upward crossing (checked).**
`SwappedAssembly/Supernatural/Cross.lean`: `crossImage_supernatural c hc i j ν q q'`, the
image of `τ : Eᵢ Eⱼ → Eⱼ Eᵢ` is supernatural of parity `pᵢ pⱼ` for all summand paths,
under the single hypothesis `hc : c.IsSupernatural` (each `c.a i t hv` is supernatural
of parity `pᵢ` on the path `(R,P)`); for `i ≠ j` no hypothesis is needed
(`crossNeEntry_supernatural`). The reduction `twoTwo_supernatural` treats a matrix
between two-letter words componentwise. Components: `(P,P)` the reassociated factor
crossing `T.cross` (`preCrossNe_supernatural`, `preCrossSame_supernatural`); `(R,R)`
`Z ◁ W.cross` conjugated by the parity-shift comparisons (`postCrossNe_supernatural`,
`postPairIso_supernatural`) or by the word comparison (`postCrossSame_supernatural`);
the mixed interchange `J` and its inverse (`mixedJ_supernatural`,
`mixedJ_inv_supernatural`, parity `pᵢ pⱼ`); the polynomial `Q` is even
(`mixedQ_supernatural`): a monomial `x^p y^q` with `sᵢⱼ^{pq} ≠ 0` has `p pᵢ = q pⱼ = 0`
by the parity conditions on `Sc`, and `dᵢⱼ` is even when `pᵢ = 1`. Generic tools:
`IsSupernatural.add`, `smul`, `zsmul`, `neg`, `sum`, `mul`, `pow`, `of_parity_eq`.
Remaining for `GeneratorsSupernatural (P.swappedGens c L)`: the leftward crossings and
the degree-`n` cups and caps, which are data of `LeftwardData`, and the discharge of
`c.IsSupernatural` for the coefficient constructed from `CrossCoeff.IsInverse`.

**Supernaturality of the swapped generator images (checked).**
`SwappedAssembly/Supernatural/Generators.lean`: `swappedGens_supernatural c L hc hσ hL :
GeneratorsSupernatural (P.swappedGens c L)`, the hypothesis of `interchangeLaw`, under
`hc : c.IsSupernatural`, `hσ : ∀ i j, i ≠ j → ∀ ν, P.SigmaPermutation c i j ν` and
`hL : L.IsSupernatural` (`LeftwardData.IsSupernatural`: `L.lcrossSame i ν` of parity `pᵢ pᵢ`,
`L.dcup i n ν` of parity `pᵢ n` for `n < ⟨hᵢ, ν⟩`, `L.dcap i n ν` of parity `pᵢ n` for
`n < -⟨hᵢ, ν⟩`; outside the windows the swapped images are zero). Ingredients:
`compList_supernatural` (the entries of a chain of layers are supernatural of the sum of
the parities of its generators, for supernatural generator images; also `compLayer`,
`compLayerAt`), `upwardGens_supernatural c hc`, `sigmaEntry_supernatural` (parity
`pᵢ pⱼ`), `lcrossNeImage_supernatural c hc i j ν hσ` (entries off the permutation are
`0`, those on it are inverses of supernatural isomorphisms). Remaining: discharge `hc`
from `CrossCoeff.IsInverse`, `hσ` (`SigmaPermutation`) and `hL` for the leftward data
constructed from `LeftwardData.IsInverse`.

**Supernaturality of the same-colour crossing coefficient (checked).**
`SwappedAssembly/Supernatural/CrossCoeff.lean`: `CrossCoeff.isSupernatural_of_isInverse c
hc h : c.IsSupernatural` for `hc : c.IsInverse` and `h : P.CrossCoeffInputs` (F2: the probe
dot `x` on `(R,P)` is a unit, F3: the reservoir dot `y` is nilpotent);
`crossCoeffOfInputs_isSupernatural h`. The dots are supernatural of parity `pᵢ`
(`rpPreDot_supernatural`, `rpPostDot_supernatural`, whiskerings of `dotDiag_supernatural`).
At even colours `a` is the inverse of the even family `y - x` (`isSupernatural_iso_inv`);
at odd colours `a = (x - y)(x² - y²)⁻¹` with `x² - y²` an even unit (`crossDenom`).
The inputs are needed at odd colours: `IsInverse.odd` only fixes `a` on the image of
`x² - y²`, and does not determine `a` (or its parity) when `x² - y²` is not invertible.
This is a property of the interface, not of the construction: the constructed coefficient
satisfies both. Generic: `IsSupernatural.sub`.

**Leftward data from the inverses of the augmented maps (checked).**
`SwappedAssembly/LeftwardInverse.lean` (BE2 Def. 1.5 (1.13), (1.14); (A7) of
`SwappedActionAssembly.md`). In the summand-path entries of a `ProbeReservoir`:
`epsEntry`, `etaEntry` (entries of `ε xⁿ`, `xⁿ η` for the upward generators);
`PosInverse c i ν t s lc dc` (for `⟨hᵢ, ν⟩ ≥ 0`: `(-lc, dcₙ)` is a two-sided inverse of
`(σ, ε xⁿ)ₙ`, written as the five entry identities of `invP₁`–`invP₅`) and `NegInverse`
(for `⟨hᵢ, ν⟩ < 0`: `(lc, dcₙ)` inverts `(-σ, xⁿ η)ₙ`, the identities of `invM₁`–`invM₅`);
`AugmentedInvertible c` (such entries exist at every `i, ν, t, s`). Checked:
`leftwardOfInvertible c h : P.LeftwardData` reads the leftward crossing and `♦`-cups/caps
off the chosen inverses (zero cups for `⟨hᵢ, ν⟩ < 0`, zero caps for `⟨hᵢ, ν⟩ ≥ 0`), and
`leftwardOfInvertible_isInverse c h : (P.leftwardOfInvertible c h).IsInverse c`; the
general form is `LeftwardData.isInverse_of_posInverse_negInverse`. At `⟨hᵢ, ν⟩ = 0` the
relations `invM₁`, `invM₂` follow from `invP₁`, `invP₂` (empty sums). With
`isSupernatural_of_isInverse` (#507) the constructed data are supernatural.
Open interface: `P.AugmentedInvertible c` for the unit-dot probe and the full-ELV reservoir
(under F1–F4). Its written proof is `SwappedHomInversion.md`, which works in Hom-sector
coordinates `Hom(T(-μ₋), W(μ₊))`; besides formalizing it, a bridge is needed from the
Hom-sector inverse to the summand-path entries of `AugmentedInvertible` (both describe the
same 2-morphisms; the path entries are their matrix coefficients through
`P.pathFunctor`).

**Sector blocks of the equal-colour augmented maps (checked).**
`SwappedAssembly/Sigma/SameColourBlocks.lean`: for one colour `i`, the paths of `Eᵢ Fᵢ` and
`Fᵢ Eᵢ` change the sector by `0` (sides `(P,P)`, `(R,R)`) or by `±(i, i)` (mixed sides), and
the empty word by `0`. Between distinct sectors the empty word has no path
(`SPath.isEmpty_nil_of_ne`), `Eᵢ Fᵢ`, `Fᵢ Eᵢ` have at most one path each
(`SPath.subsingleton_upDn_self`, `SPath.subsingleton_dnUp_self`), existing together
(`SPath.nonempty_dnUp_self_iff`). So for `t ≠ s` the augmented maps are single `σ` entries:
`posInverse_of_ne`, `negInverse_of_ne` (inverse component `lc = -σ⁻¹`, no `♦`-cups/caps).
Reduction: `augmentedInvertible_of_central_of_swapping c hcentral hswap :
P.AugmentedInvertible c` from `CentralInvertible c` (inverses at `s = t`, all dotted windows)
and `SwappingInvertible c` (every `sigmaEntry c i i ν p q Z` with `t ≠ s` is an isomorphism).
Proposed bridge: `AugmentedSectorBlocks.md`. The swapping entries are single terms (cup and cap
force their sides): at `s = t + (i,i)` the reservoir mate of `-(a ; a ; J⁻¹)` (`W_B` of
`SwappedHomInversion.md` §7), at `s = t - (i,i)` the probe mate of `J` (`W_A`). The central
entries are single terms with crossing entries `-q·(probe crossing)`, reservoir crossing,
`a` (`(P,P) → (R,R)`) and `-(J ; a ; J⁻¹)` (`(R,R) → (P,P)`). Open: `SwappingInvertible`
(formalize §7 through these single terms) and `CentralInvertible` (§§2–6). Proposed sign
observation (§4 of the bridge): the checked crossing entries are `-q` times the diagonal of (2)
of `SwappedHomInversion.md` read with A = probe, so its `K` is replaced by `-q K` (the earlier
`K`); for `p = 0` this would make the §5 tables, written with the earlier sign, the correct
ones. To be rechecked against `ProbeWindowInverse.md` (4).

**Sign of the central entries: settled (written).** The diagonal of (2) of
`SwappedHomInversion.md` is now the Lean entry (`a` on `(R,P)`, `-J⁻¹ a J` on `(P,R)`, with
`a = (y-x)⁻¹` for `p = 0`), for which `crossCoeff_diag` proves the formal slides; the version
of (A6) that multiplied the diagonal by `-q` gives the even slide with right side `-1`.
Correspondingly `C_RP = -Σ_r q^(r+1) u_R(r) v_P(-r-1)`, `D_PR = Σ_s q^(s+2) u_P(-s-1) v_R(s)`
(the earlier `K`). Recomputed from (11) and (7) there, the §5 tables are exactly `Hhat_±` of
`ProbeWindowInverse.md` (`c_r = q^(r+1)`, `d_s = q^(s+2)`), and its window identities (4)
follow from the literal slide (1), whose sign does not involve `a`. So §§5–6 of
`SwappedHomInversion.md` hold as written for both parities; only the written route changed.
Open check: `SwappedActionAssembly.md` (A6) also asserts that this (Lean) diagonal breaks the
mixed `jij` braid in the smallest mixed case; the Lean braid (`CrossBraid`) is still a
hypothesis, so that assertion must be rechecked against the Lean dots (if it held, the slide
and the braid would require opposite signs).

**`CentralInvertible` needs a weight restriction (interface).** As stated,
`CentralInvertible` (and so `AugmentedInvertible`, `LeftwardData.IsInverse`) quantifies over
all `ν` independently of the sector. The entries `σ`, `ε`, `η` do not depend on `ν`; only the
window count `(D.h i ν).toNat` does. If `[σ; ε₀, …, ε_{H-1}]` is invertible, then adding one
more window row gives `[1; r]` times it, which is not invertible unless the object is zero. So
the unrestricted statement fails as soon as some `P.H t` has a nonzero object. The action only
uses weight-matched sectors (`layerEntry` needs `P.wt sr = L.cod.endR`; `compEval` is applied
through `evalW_eq_zero_of_compEval` with `hend : P.wt t.1 = …endR`). Next step: restrict
`CentralInvertible`, `AugmentedInvertible` and `LeftwardData.IsInverse` to `P.wt s = ν`
(rightmost sector), weight `relHolds_of_compEval`, and define `leftwardOfInvertible` as zero
off weight. `SwappingInvertible` does not involve `ν` and is unaffected.

**Supernaturality of the equal-colour leftward data (checked).**
`SwappedAssembly/Supernatural/Leftward.lean`: `LeftwardData.isSupernatural_of_isInverse c L
hc hL : L.IsSupernatural` for `hc : c.IsSupernatural` and `hL : L.IsInverse c`. The entries of
`L` are entries of the two-sided inverses of the augmented maps (1.13), (1.14) of BE2 Def. 1.5:
`(σ, ε xⁿ)ₙ : Eᵢ Fᵢ → Fᵢ Eᵢ ⊕ 1^{⟨hᵢ,ν⟩}` with inverse `(-lcross, ♦-cupₙ)` for `⟨hᵢ, ν⟩ ≥ 0`
(`leftward_supernatural_of_nonneg`, from `invP₁`–`invP₅`), and
`(-σ, xⁿ η)ₙ : Eᵢ Fᵢ ⊕ 1^{-⟨hᵢ,ν⟩} → Fᵢ Eᵢ` with inverse `(lcross, ♦-capₙ)` for
`⟨hᵢ, ν⟩ ≤ 0` (`leftward_supernatural_of_nonpos`, from `invM₁`–`invM₅`). The augmented maps
are built from upward generators, supernatural of parity `pᵢ²` on `σ` and `n pᵢ` on the
`n`-th component. The generic lemma (`Supernatural/MatrixInverse.lean`,
`isSupernatural_of_inverse_target` / `_source`): if a matrix of transformations with a
two-sided inverse has supernatural entries of a parity depending only on the target (resp.
source) index, so has its inverse. Proof: projecting `A B = 1` to parity `0` shows the
homogeneous parts of `B` form a right inverse, hence equal `B`; naturality from
`B F(f) = Ĝ(f) B`, `Ĝ` the signed diagonal.

**The interchange-law field of `SwappedRelationData` is redundant (checked).**
`SwappedAssembly/Supernatural/Relations.lean`:
`swappedGens_supernatural_of_isInverse c L hin hc hσ hL : GeneratorsSupernatural
(P.swappedGens c L)` for `hin : P.CrossCoeffInputs`, `hc : c.IsInverse`,
`hσ : ∀ i j, i ≠ j → ∀ ν, P.SigmaPermutation c i j ν` and `hL : L.IsInverse c`
(combining `CrossCoeff.isSupernatural_of_isInverse`,
`LeftwardData.isSupernatural_of_isInverse` and `swappedGens_supernatural`).
`SwappedRelationData.ofIsInverse hin hc quad slide braid zigzag sigma leftward windowZero`
builds `SwappedRelationData c L` without the `supernatural` field, and
`SwappedRelationData.ofCrossCoeffInputs hin …` does so for `c = crossCoeffOfInputs hin`
with no hypothesis on `c`. So `GeneratorsSupernatural` is no longer an independent
obligation of `SwappedVacuumObservation`; `sigma` (`SigmaPermutation`) remains one.

**`SigmaPermutation` from entrywise invertibility (checked).**
`SwappedAssembly/Sigma/Permutation.lean`: `sigmaPermutation_of_isIso hij ν h :
P.SigmaPermutation c i j ν` for `i ≠ j`, given only that every entry
`P.sigmaEntry c i j ν p q Z` is an isomorphism. For `i ≠ j` the summand paths of
`Eⱼ Fᵢ` and `Fᵢ Eⱼ` between fixed sectors `t`, `s` are determined by their sides
(`SPath.subsingleton_upDn`, `SPath.subsingleton_dnUp`), and one exists iff the other does
(`SPath.nonempty_dnUp_iff`, the two steps commute: `SPath.exchange_upDn`,
`SPath.exchange_dnUp`). So the permutation is forced and the off-diagonal condition is
vacuous. Remaining for `hσ`: invertibility of the four single-term blocks
(probe/probe: `homContentDistinctPreMate`; reservoir/reservoir: the shifted post mate;
mixed: `homDistinctMixedMate` and `homDistinctMixedPreMateDot`).

**The sideways crossing entry is a single composite (checked).**
`SwappedAssembly/Sigma/Entry.lean`: `sigmaEntry_eq c hij ν p q m₁ m₂ Z hp h₁ h₂`. For
`i ≠ j` and a summand path `p` of `Eⱼ Fᵢ` with sides `[a, b]`, the three-layer sum defining
`P.sigmaEntry c i j ν p q Z` (cup, crossing, cap) has exactly one nonzero term: the one
through the middle paths `m₁` with sides `[b, b, a, b]` and `m₂` with sides `[b, a, b, b]`.
So the entry is `cup(p, m₁) ≫ cross(m₁, m₂) ≫ cap(m₂, q)`, up to the path casts. The proof
tracks sides through each layer (`sides_of_cup`, `sides_of_cross`, `sides_of_cap`): a
nonzero cup entry duplicates one side, a crossing swaps two sides (`SPath.sides_upUp` for
distinct colours), a cap removes a matching pair (`sigma_sides`). Remaining for `hσ`:
invertibility of this composite in each of the four side patterns `[a, b]`.

## Old-only ELV quotient module

`ELVOldCyclotomicTarget.lean` constructs matrix-Hom components of
`H e(i,β) / H F₂ R₁(β)e(i,β)` in the signed coefficient category.
`ELVOld.insert` fixes coefficients and inserts the moving strand on the left.
`ideal` is two-sided only in the old category; `relations` permits arbitrary
ambient left multiplication, not arbitrary right multiplication. `Target`,
`projection` and `act` give the quotient module and its identity/composition laws.

`relation_mem_parity` and `twist_ideal` establish total-parity stability,
including exterior coefficients. `pair` descends the signed multiplication
pairing against the old quotient; `pair_balance` and
`pair_balance_homogeneous` prove its balance. `insert_elvPolynomial`
identifies the inserted polynomial with the second-position ELV polynomial,
and `projection_elvPolynomial` kills every ambient continuation.
`projection_top` retains the even-cutoff delta-times-top relation.
Arbitrary colours, commutative ground rings and cutoffs are retained.

The importing consumer tests positive odd/even and zero cutoffs, the empty old
word, signed balance and the top relation. It defines the moving-polynomial
class separately; it does not prove that class nonzero. A bundled signed tensor
equivalence, the right PBW comparison for this coefficient extension, and
moving-polynomial nonvanishing remain open. Full transported old-factor killing,
all-prefix QP induction/cancellation and projective resolution are next obligations;
no identification with ordinary `contentTargetTensor` is asserted.

## Signed ELV coefficient quotient category

`ELVCoefficientCategory.lean` constructs the categorical coefficient quotient
required before old-cyclotomic balancing in `DeformedGlobalQP.md` §3.
`elvCoefficientIdeal_parity` proves stability of the exact two-sided ELV
coefficient ideal under both parity projections. The generators used are the
specified elementary truncations and the even-cutoff `delta_i * chi_top`
relations, transported through the polynomial/exterior algebra equivalence.
No field, domain, flatness, finite-colour or independent-root premise is added.

`elvCoefficientGradedAlgebra` gives the quotient algebra its induced parity.
`ELVCoefficientCategory` is its signed box product with the affine category.
`elvQuotientMap_comp` and `elvQuotientMap_mem` prove preservation of actual
categorical composition and parity; `elvQuotientFunctor` is linear and a
superfunctor. `elvQuotientHomEquiv` identifies its Homs with
`ELVCoefficientHom`, and `elvQuotientMap_eq` identifies its map with the earlier
tensor quotient. `elvQuotientMap_kills_span` kills the two-sided span of the
coefficient arm of `ELVGenerator`. `elvQuotient_odd_comp_odd` retains the
negative sign when an odd coefficient passes an odd affine morphism.

The consumer retains nonzero delta at cutoffs two and three, tests the even
top relation inside categorical composites, checks the quotient map and
parity, and instantiates signed composition over `ZMod 9` with invertible two.
Cutoff zero and the empty word are included.

This is a categorical coefficient quotient, not an old-cyclotomic balanced
target or all-prefix relation killing. Neither old-strand nor moving-strand
cyclotomic polynomials are imposed. The next task is to construct the
old-strand cyclotomic quotient and its signed balanced tensor over this
category, imposing only the old-strand relations, then prove the required
relation killing there. The ordinary `contentTargetTensor` alone does not
supply that construction. QP, projective resolution and nondegeneracy remain
separate obligations.
## Inputwise locally finite mixed coefficients

`LocallyNilpotentMixedInverse.lean` constructs a linear inverse of x-y
from a unit linear operator x, a commuting linear operator y, and
`∀ v, ∃ n, (y^n) v = 0`. Both inverse products and equality with the
ring inverse are proved. `localMixedEvenInverse_expansion` identifies
its value with the ordered finite series for every annihilating bound
of the given input. Bound independence and linearity therefore follow
without a uniform exponent. For anticommuting x and y,
`localMixedOddCoefficient_rational` and `_expansion` identify
(x-y)(x²-y²)⁻¹ with the signed ordered sum through 2n. The denominator
inverse is constructed by the same local argument for x² and y².
The two `_intertwine` theorems retain a common scalar sign c with c²=1
on both dots; the square denominator transports without that sign.

These are module-level results over an arbitrary commutative ring,
without field, domain, flatness, finite-colour or independent-root
hypotheses. The finite paired-sum and square-commutation lemmas from
`RouquierHomMixedRational.lean` are exposed for reuse, not reproved.
The scoped warning-as-error build and an importing headline axiom check
pass. This is an incomplete application slice: no new non-vacuity
consumer, in particular no unbounded lowering-shift example, has been
supplied. The previous nonempty signed matrix consumer is unchanged.

Remaining: test the construction on a genuinely locally but not globally
nilpotent shift; evaluate the prescribed shifted Hom dots on modules
and assemble the signed component maps into the required natural
transformations. Then bend in the specified adjunctions to obtain
`SwappedHomInversion.md` (4)–(5). No factor-action, fusion or detector
claim is made.

## Rational mixed coefficients on a nilpotent component

`RouquierHomMixedRational.lean` proves `SwappedHomInversion.md` §3
(2)–(3) in a ring with a unit x and a supplied exponent y^n=0.
`mixedEvenDenominator_isUnit` and `mixedOddDenominator_isUnit` establish
the prescribed denominators as units, independently of the expansion.
`mixedEvenInverse_expansion` identifies `Ring.inverse (x-y)` with
the ordered sum x^(-r-1)y^r for r<n. `mixedOddInverse_expansion`
identifies `(x-y) Ring.inverse (x²-y²)` with the ordered signed sum
(-1)^r x^(-r-1)y^r for r<2n. The latter is an adequate, not minimal,
cutoff. Pairing adjacent even and odd terms proves the identity; no
rational square formula is assumed.

`homContentMixedRational_even` and `_odd` apply these identities to the
actual shifted pre and reservoir dots on the AB object, deriving their
commutation from `homContentMixedDot_exchange`. Their hypotheses are
invertibility of this pre dot and a nilpotence exponent on this object.
There is no exponent uniform over a weight fibre and no extra field,
domain, flatness, finite-colour or independent-root assumption. The
ring identities do not require 2 invertible. The importing consumer uses
odd off-diagonal 3-by-3 blocks over ℤ/9, where 2 is invertible but the
ring has zero divisors. Its reservoir cube is zero and square nonzero;
both inverse products and the failure of the unsigned series are checked.
This matrix fixture is not a construction of either Rouquier family.

The rational expression is available as a coefficient for the existing
`homContentMixedSwap`; its ordered `-J⁻¹ a²` definition is unchanged.
Remaining: assembly when only inputwise local nilpotence is available,
then bending in the specified adjunctions to obtain (4) and raw
comparisons (5), with alpha, beta, gamma, xi and exceptional zero intact.
Factor actions, the rational square calculation needed for swapping
inverses, fusion and coefficient detection remain obligations.
Next target: assemble the component coefficients with their signed
naturality, or supply the required objectwise bounds from the finite
reservoir quotients, before proving the bent entries.

The consolidated [mathematical checkpoint](STATUS.md) distinguishes the
complete written argument from the checked Lean components and remaining
formalization obligations, with exact code revisions.

## Rationalization injection for normalization parameters

`SKM.UniversalCoefficientRationalization.coefficientMap_injective` embeds the
actual `Localization.Away (2 : ℤ)` in ℚ. `rationalize_injective` maps the
normalization group algebra coefficientwise into the ℚ-group algebra on the
*same unsaturated group*, without requiring that algebra to be a domain or
that the group be torsion-free. `rationalize_single`, `rationalize_groupUnit`,
`rationalize_t` and `rationalize_c` compute the images of coefficients and
universal group units. For every variable type, `rationalizePolynomial_injective`
extends the injection to `MvPolynomial`; its constant and variable formulas
are checked. An order-two group algebra consumer verifies nonzero, distinct
zero divisors survive and tests a nonconstant polynomial.

This completes the coefficientwise rationalization injection of
[GroundRingDescent](GroundRingDescent.md) §4, for the unsaturated group and an
arbitrary polynomial variable type. The actual allowed coefficient-slot
ring is constructed below; the rational algebra on those slots is reduced
and separated by fields. The comparison identifying the generic polynomial
injection with these exact allowed slots is still required before applying
joint field separation to the integral ring. None of this proves SKM
nondegeneracy or constructs its universal matching basis.
## Integral universal parameter field family

`UniversalParameterFields.point` composes coefficientwise rationalization of
`ParameterRing D` with the prime-quotient fraction fields of the reduced
rational parameter ring. `point_separate` and `exists_point_ne_zero` show
joint zero reflection for the actual ring, retaining every colour, weight,
allowed coefficient slot and unsaturated group relation. Every target is a
characteristic-zero field. `point_t`, `point_c` and the allowed/forbidden
coefficient formulas identify images; `scalars`, `homogeneous` and
`normalizations` transport the universal systems on the unchanged datum.
The importing consumer detects a nonzero allowed coefficient at some prime
without choosing one and checks the empty-colour separation statement.
The dependent-root zero divisors remain as before; no fixed point is asserted
injective. The next mathematical obligation is the conditional scalar-change
comparison for the actual SKM expansion and complete exterior coefficient
basis; neither the field candidate nor nondegeneracy is proved here.

## Reduced rational parameter rings

`UniversalCoefficientReduced.rationalGroupAlgebra_isReduced` proves that
`AddMonoidAlgebra ℚ G` is reduced for every additive abelian group `G`.
Inversion of group labels defines a ring involution. The coefficient at zero
of `f * inversion f` is the sum of the squares of the rational coefficients,
so its vanishing forces `f = 0`. If `f² = 0`, apply this detection first to
`f * inversion f` and then to `f`; the square-zero criterion gives reducedness.
There is no finite-generation or torsion-free hypothesis.

`rationalParameters_isReduced` applies this to the exact unsaturated
`NormalizationParameterGroup.Group D` and every allowed
`UniversalPolynomialParameters.Slot D`. `rationalParameters_separate`
connects this ring directly to the constructed prime-quotient fraction fields.
The dependent-root consumer retains the nonzero order-two endpoint and
nonzero factors `u-1`, `u+1` with zero product, both in the group algebra and
in its polynomial extension. Reducedness is not a domain assertion.

This supplies reducedness and characteristic-zero field separation for the
rational parameter ring of [GroundRingDescent](GroundRingDescent.md) §4.
Coefficientwise rationalization injection for the unsaturated group algebra
and arbitrary polynomial variables is proved above. The next task is to
instantiate this injection at exactly `Slot D` and identify its domain with
the integral `ParameterRing D`, then compose with the separating fields.
The field candidate, universal matching basis and nondegeneracy deduction
remain separate obligations.
This supplies the reducedness step of [GroundRingDescent](GroundRingDescent.md)
§4. Combined with `UniversalCoefficientRationalization.rationalizePolynomial_injective`,
this supplies the injection and reduced rationalization inputs for separation of
the integral parameter ring. The field candidate, universal matching basis
and final nondegeneracy deduction remain separate obligations.

## Universal coefficient-slot polynomial ring

`SKM.UniversalPolynomialParameters.ParameterRing D` is the polynomial ring
on allowed coefficient slots modulo `(i,j,p,q) ↔ (j,i,q,p)` over `UnitRing D`.
`Allowed` imposes both separate odd-exponent support conditions everywhere,
and the exact `Scalars.Homogeneous` degree equation only in the strict used
rectangle. All other allowed positions, including diagonal and unused ones,
remain independent variables modulo swap. No Symmetrizer choice is needed
by this predicate. Colours and the original weight group are arbitrary.

`scalars`, `homogeneous`, and `normalizations` construct the universal
Scalars, its homogeneity proof, and every normalization unit. `specialize`
extends the existing unit-ring specialization; `specialize_coefficient`
recovers every supplied coefficient under precisely its homogeneity premise.
`specialize_t`, `specialize_c`, `hom_ext`, and `specialize_unique` prove
simultaneous parameter formulas and uniqueness. There is no field, domain,
flatness, finiteness, independent-root or nontriviality assumption.

The new consumer uses the two-even-colour matrix with off-diagonal entries
-2 over ZMod 9: the interior slot `(1,1)` specializes to 3 and is nonzero
universally. The unused slot `(0,5)` specializes to 4 despite failing the
degree equation; its swapped and diagonal counterparts are also tested.
Separate odd-support tests kill left and right odd exponents, including
unused positions. The earlier dependent-root unit fixture is unchanged.

This completes the polynomial parameter construction of
[GroundRingDescent](GroundRingDescent.md) §3, not nondegeneracy. The
coefficientwise rationalization injection is proved above for arbitrary
polynomial variables, and reducedness of its rational allowed-slot target
is also proved. The exact parameter-ring identification and combined
separating-field map remain to be checked. Exterior bubble generators stay
outside this purely even parameter ring; the universal matching basis and
nondegeneracy deduction remain separate.
The rationalization injection and reducedness of its rational group algebra
and polynomial extension are proved above. Exterior bubble generators remain
outside the parameter ring. The universal basis and final nondegeneracy
connection remain separate.

## Rationalization injection for normalization parameters

`SKM.UniversalCoefficientRationalization.coefficientMap_injective` embeds
`Localization.Away (2 : ℤ)` in ℚ. `rationalize_injective` maps the
normalization group algebra coefficientwise into the ℚ-group algebra on the
same unsaturated group, without assuming a domain or torsion-free group.
`rationalize_single`, `rationalize_groupUnit`, `rationalize_t` and
`rationalize_c` compute images of coefficients and universal group units.
`rationalizePolynomial_injective` extends the injection to every variable
type, including the actual `Slot D`; its constant and variable formulas are
checked. An order-two group algebra consumer verifies nonzero zero divisors
survive and tests a nonconstant polynomial. Together with the reducedness
above, this supplies the ring-theoretic inputs to the integral separating
field family, not the field candidate or SKM nondegeneracy.

## Normalization unit ring over ℤ[1/2]

`SKM.UniversalCoefficientRing.UnitRing D` is the additive group algebra of
`NormalizationParameterGroup.Group D` over `Localization.Away (2 : ℤ)`.
`groupUnit`, `t`, and `c` supply genuine units; `t_self`, `t_symm`, and
`c_shift` prove the endpoint, disconnected-symmetry and normalization laws.
`two_isUnit` proves that 2 is invertible. `lift` uses the localization and
additive group-algebra universal properties. `hom_ext` proves that the endpoint
and normalization images determine a ring homomorphism; `specialize` and
`specialize_unique` give its unique specialization to any supplied Scalars
and CScalars over a commutative ring with 2 invertible. No independent roots,
finiteness, field, domain, nontriviality or flatness are assumed.

The importing consumer evaluates the dependent-root example in ℚ × ℚ,
retaining the endpoint (1,-1), neither sign, and every normalization value.
Further evaluations use ZMod 9 (the localized inverse of 2 maps to 5) and
ZMod 1. This is the unit-ring part of [GroundRingDescent](GroundRingDescent.md)
§3, not the full polynomial parameter ring or nondegeneracy.

The coefficient-slot polynomial extension, universal Scalars/Homogeneous/CScalars
and exact coefficient specialization are constructed above. The group-algebra
rationalization injection and arbitrary-variable polynomial extension are
proved above, as is rationalized reducedness; their exact allowed-slot
assembly remains separate.
and exact coefficient specialization are constructed above. Rationalization
injection and rationalized reducedness are proved separately.

## Unsaturated normalization parameter group

`SKM.NormalizationParameterGroup.Group D` is the free abelian group on
`T_ij` and every original `X`-labelled `C_(μ;i)`, modulo the subgroup generated
by the diagonal, disconnected-symmetry and shift relators. No saturation is
taken. `lift` constructs the universal additive homomorphism; `hom_ext`
proves uniqueness. `specialize` sends the classes to the supplied units of
any `Scalars D R` and `CScalars Sc`, with both generator formulas and
`specialize_unique`. No finiteness, independent-root, domain or flatness
hypothesis is used.

The mixed-parity dependent-root consumer has `X = ℤ`, roots `(2,-1)` and
symmetrizers `(4,1)`. Its parameter in `ℚ × ℚ` is `(1,-1)`, neither sign.
It proves that `T_01 + T_01 = 0` but `T_01 ≠ 0` in the presented group itself.
Thus the construction retains the torsion required by the original roots.
This realizes the group part of the proposed deduction in
[GroundRingDescent.md](GroundRingDescent.md) §3, not the nondegeneracy endpoint.

The unit ring `Z[1/2][G]` and its unique ring specialization are constructed
above, together with the allowed-slot polynomial extension and universal
`Scalars`, homogeneity and `CScalars`. The rational group algebra is reduced;
coefficientwise rationalization injection for it and arbitrary polynomial
variables is proved. Identifying the exact integral parameter ring with this
polynomial source and applying field separation remains open.
above, together with its coefficient-slot polynomial extension and universal
`Scalars`, homogeneity and `CScalars`. Rational injection and reducedness of
the rationalized group algebra and polynomial ring are proved above.

## Prime-quotient characteristic-zero fields

For every reduced commutative ℚ-algebra `A`, `SKM.primeFractionField A p`
constructs the fraction field of `A ⧸ p.asIdeal` at each prime `p`.
`SKM.primeFractionMap A p` is the quotient map followed by fraction-field
inclusion; each target has characteristic zero, and
`SKM.primeFractionMaps_separate` proves the family jointly detects zero using
the nilradical/prime-intersection theorem. No domain or finite-generation
assumption is used. In the trivial ring the spectrum is empty and reducedness
makes the same conclusion valid. A `ℚ × ℚ` consumer retains its zero divisors,
constructs the field family, and applies the coefficientwise basis theorem.

This does not establish that the rationalized normalization-group algebra is
reduced. The coefficientwise rationalization injection is proved above; the
generic prime-field family applies only after reducedness is established.

## Ground-ring descent retaining the original realization

`SKM.linearIndependent_of_joint_scalar_images` formalizes the finite-relation
argument of [GroundRingDescent.md](GroundRingDescent.md) §6: if ring maps
`R → K_j` jointly detect zero and semilinear maps take a family in an
`R`-module to independent families over every `K_j`, the original family is
independent. The `K_j` may be commutative rings, not necessarily fields; no
individual ring map or module map is assumed injective. Given spanning,
`SKM.basisOfJointScalarImages` constructs the basis. The consumer applies it
to the unit family over `ℚ × ℚ`, where neither projection alone is injective.
This is a coefficientwise algebraic lemma, not SKM nondegeneracy.

The remaining descent inputs are the universal parameter ring with a faithful
map to its rationalization, reducedness of that rationalization, and the
expansion family's compatibility with `homBaseChange` (including the full
exterior coefficient basis). Joint field separation for a reduced rational
algebra and the presented-Hom tensor equivalence are checked below. The field
nondegeneracy candidate is still unformalized and unchanged.

[GroundRingDescent.md](GroundRingDescent.md) gives a proposed deduction from
`SwappedNondegeneracy.md` over characteristic-zero fields to its full scope
over arbitrary commutative rings with 2 invertible, without inverting the
symmetrizers. The frozen field candidate is unchanged and remains unformalized.

The universal parameter ring is `Z[1/2][G][z_v]`, where the abelian group G
presents all endpoint units and all original X-labelled CScalars with their
shift equations. It need not be a domain: the compatible dependent-root
datum with roots `(2,-1)` in Z and Cartan matrix `[[2,-1],[-4,2]]` forces a
unit parameter to square to one without selecting its sign. The note proves
that the universal ring nevertheless embeds in a product of characteristic-zero
fields. Existing arbitrary-ring expansion spanning and the full exterior
coefficient basis then give the universal basis from field independence;
only that basis, not the field detecting action, is specialized.

The general ground-ring nondegeneracy endpoint is not formalized. The
presentation-level `S ⊗[R] Hom_R(a,b) ≃ₗ[S] Hom_S(a,b)` and its raw-diagram,
inverse-entry and normalized-cup/cap formulas are checked below for any
commutative scalar map; the universal expansion square and coefficient basis
remain to be established. An integral low-PBW-weight projection also replaces
the candidate's bounded vector-space splitting whenever its stated high-ideal
bound is available. Neither observation supplies the unfinished full-ELV
field action or the complete mixed Hom inversion.

## Canonical written nondegeneracy proof

[SwappedNondegeneracy](SwappedNondegeneracy.md) composes the full-ELV factor
construction, swapped action assembly and cofinal bounded observations into
the full written proof. Its exact scope is a purely even field with 2
invertible, a compatible symmetrizable Cartan superdatum with positive
integral symmetrizers, admissible homogeneous Sc with separate odd-exponent
support and leading units, and supplied cs : CScalars Sc. Arbitrary colours
are handled by finite contextual witnesses, retaining the whole weight group.
The statement has no additional detecting-model hypothesis. It remains
**proposed until checked in Lean**, not a formal nondegeneracy theorem.

Remaining Lean work: full-ELV factor implementation, whole swapped action
assembly, vacuum/bubble/bounded recovery realization, and final composition
with finite-witness passage. The conditional notes below retain their local
claim boundaries; the canonical document explains how their hypotheses
are supplied at the written level. Their historical open-step summaries
are not the status of the composed written proof.

## Cofinal bounded observations

`SwappedDetectingFamily.md` supplies the written simultaneous parameter
choice from the full deformed factor inputs: fix the finite-colour pair and
degree, set N0=d+2 choose(length(t),2)+1 and m=N0, use the balanced schedule
at -mu, and truncate every positive even coefficient to power N0 in one
common tower algebra. Probe content zero is nonzero (T_0=k) and already has
the required external Hom weight; no positive-content reachability is assumed.
Closure series lengths are chosen after the fixed-content grading bounds,
independently of the cyclotomic cutoffs. Thus no circular inequality arises.
The literal all-reservoir evaluation, all-height coefficient substitution,
and bounded signed extraction supply the field-valued bounded cyclic
recovery data at that pair and degree, including degree zero. This is a
proposed written result relative to full factor existence, not a Lean
instance, an arbitrary-ring splitting, or a global arbitrary-colour Hom
action. Full factor construction and formalization remain separate.

## Conditional finite-colour swapped superaction

`SwappedActionAssembly.md` now states the conditional written finite-colour
parity-superaction theorem with explicit factor inputs F1–F4 and a complete
`Presentation.Rel` dictionary. The four distinct-colour blocks are inverted
componentwise: normalized-left pre/pre with
`delta=t_ij (-1)^(p_i p_j sigma) g(k-d_ij)/g(k)`, transported factor
post/post, and the indexed mixed mates U_ji,V_ij for s_ij. The U calculation
uses the exchanged (j,i) content square and parity shifts; V retains (i,j).
The QJ mate bends the unit probe strand;
its polynomial uses the normalized-left transposed probe dot Z and the
surviving nilpotent reservoir dot Y, retaining the signed transpose powers
and both dotless residual signs. Whole same-colour matrices, not merely
the principal components, supply the height-window inverse generators.

The specified vacuum has only its all-reservoir upward path.
`SwappedVacuumBubbles.md` and `SwappedVacuumNonpositiveBubbles.md` give
all-height elementary series `C_i(-z)/(1+z)^M_i` at odd colours and
`E_i(-z)/(1-z)^P_i` at even colours, with odd bubble
`(-1)^(N_i+1)L_delta_i`. Composing the filtration-preserving coefficient
substitution with `SwappedVacuumCoordinates.md` gives recovery on the
explicit admissible bounded windows. The arbitrary-colour finite-witness
implication is conditional on finite-colour detecting models.

These are written results. Factor existence and full formalization are
not inferred; admissible-observation packaging and its detection consumer
remain separate. No total zero-window extension, full integer-graded
fusion, arbitrary-Hom base change or nondegeneracy is claimed. The
kernel-checked pre/post principal comparisons below are preserved as
separate formalized results; they do not certify the whole matrices.
## ELV coefficient-quotient tensor transport

`ELVCoefficientTransport.lean` constructs `elvCoefficientQuotient` from
abstract SYM to its exact `elvCoefficientIdeal` ring quotient, and
`elvHomQuotient` from coefficient-extended affine Hom to
`(SYM / elvCoefficientIdeal) ⊗ Hom`. The latter kills every ideal
coefficient times every affine morphism, with no descent or flatness premise.
Elementary truncations and `delta_i * chi_(cutoff_i/2)` at even cutoffs
vanish; at cutoff zero the latter kills `delta_i` itself.

`elvMonicCoefficient_mem_parity` proves that the degree-j coefficient has
parity N-j. `elvDotPolynomial_first` identifies the polynomial at position
zero with the existing `elvCyclotomic`; `elvHomQuotient_dotPolynomial`
gives its coefficientwise image in the quotient tensor module.
`elvDotPolynomial_transport` and `elvDotPolynomial_old_transport`
transport its projected composites through the affine intertwiner chain
with sign `(-1)^(N p(i)p(ν))`, for moving and old strands respectively.
No field, domain, finite-colour or flatness assumption is introduced.

The consumer retains a nonzero odd coefficient in the exact quotient at
cutoffs two and three, checks the corresponding coefficient lists, tests
the even-cutoff top relation both in the ring and after tensoring, and
includes zero cutoff and empty chains. Transport and the top relation
are also instantiated over `ZMod 9`, with invertible two and a nonzero
square-zero element.

The transport module alone does not construct categorical composition;
`ELVCoefficientCategory.lean` now supplies that structure and its quotient
functor. It does not construct an SKM action. The next obligation is to
compare these coefficient-extended
modules with the deformed old-cyclotomic balanced target and prove the
relation-killing step there, then perform `DeformedGlobalQP.md` §3.
The existing ordinary-polynomial `contentTargetTensor` does not supply
that comparison. Full QP and the projective resolution remain open.


## Source-coefficient polynomial transport

`CoefficientPolynomialTransport.lean` proves
`coefficientDotPolynomial_comp_moveHom` and
`coefficientDotPolynomial_mem_comp_moveHom` in the existing `CoefficientH`
category, with coefficients inserted by `sourceCoefficientHom`. If the
coefficient of degree `m` has parity `P - m p(x)`, the polynomial moves
through `moveHom i l ν` with the common sign `(-1)^(P p(i)p(ν))`.
This applies both to the moving strand and to any old strand. The proof
combines coefficient composition, `moveHom_parity` and the affine dot
transport; it does not assume odd coefficients central. There is no
field, finite-colour or monicity hypothesis, beyond the given commutative
ground ring and scalar datum.

The odd rank-one rational consumer proves its exterior generator `delta`
nonzero and tests `1 + delta*x + x²` and `delta + x`. It includes moving
and internal old strands, odd and even chain lengths, and an empty chain.
For the even polynomial the coefficient sign cancels the odd-dot sign;
for the odd polynomial both terms acquire the same overall sign.

This establishes the affine full-source-coefficient identity in
`DeformedProjectiveResolution.md` §1 (1). The finite ELV coefficient-quotient
tensor transport and polynomial identification are now recorded above.
The deformed balanced target comparison and repeated-colour induction
remain obligations. No finite ELV action or balanced QP identity is asserted.

## Signed ordinary-polynomial transport

`SignedPolynomialTransport.lean` proves `dot_pow_comp_moveHom`,
`polynomial_comp_moveHom` and `polynomial_mem_comp_moveHom`. For the moving
strand, every ground-ring polynomial transports through the prescribed
`moveHom i l ν` by substituting `(-1)^(p(i)p(ν))` times the destination dot.
For an old strand of colour `x`, the substitution uses
`(-1)^(p(x)p(i)p(ν))`. Powers include zero; polynomials may have mixed parity
and need not be monic. No finiteness assumption on the colour set is used.

The importing consumer has a fully specified odd rank-one datum over ℚ.
It tests an inhomogeneous cubic at an odd-length chain, sign cancellation
at an even-length chain, an old strand inside a longer chain, and empty
chain/zero-exponent boundaries.

This proves only the ordinary-coefficient part of the transport in
`DeformedProjectiveResolution.md` §1. The full source-coefficient sign is
now proved in `CoefficientPolynomialTransport.lean`, as recorded above.
Descent through the full ELV relations and the repeated-colour balanced
QP induction of `DeformedGlobalQP.md` §3 remain open. Neither that induction
nor a full ELV action is asserted by these polynomial identities.

## All-prefix cyclotomic relation killing

`IntertwinerRelation.lean` proves `allPrefix_relation_tmul_zero`: for every
finite prefix `ν`, moving colour `i`, and ambient left multiplier,
`f_i(x₁) T_|ν| V_(|ν|+1)` on `(i,ν,i)` vanishes in the prescribed prepend
balanced tensor with coefficient `qCoefficient`. The bare prefix is the
recursive morphism `lastToFirstHom`; the theorem includes the empty prefix,
repeated colours and arbitrary spectator parities. Polynomial parity is
unchanged, so odd cutoffs and cubic odd-colour polynomials are allowed.

`append_move_factor` reuses established moving-strand naturality and retains
the parity involution on the entire old expression. The stronger
`append_relation_move_tmul_zero` permits arbitrary inhomogeneous old factors
on both sides of the relation. `prepend_kernel_tmul_zero` kills the resulting
old quotient-kernel element by balancing, rather than assuming relation
vanishing or using flatness. `prefix_relation_move_tmul_zero` supplies the
typed word representative in the target of `parityCyclotomicContentQ`.

This closes the relation-killing step for the existing ordinary-polynomial
coefficient implementation only. Signed polynomial transport and the
inductive QP calculation remain; no global QP, full coefficient-superalgebra
extension, ideal-sum equality or projective resolution is asserted.
## Content-shifted mixed Hom interchange

`RouquierHomMixedInterchange.lean` constructs the prescribed J of
`HomSwappingMates.md` §1 (1): remove the source content shift, apply the
inverse pre/post associator, and insert the target shift. On the supplied
factor families the shifts are κ(β) and κ(β+i); their sum is the colour
parity. `homContentMixedInterchange_pre` and `_post` derive the q signs
from super-interchange and homogeneous shift naturality.
`homContentMixedDot_exchange` proves the shifted pre/post Koszul exchange.
The two `_square` theorems transport dot squares with no residual sign.

`homContentMixedSwap_products` composes the prescribed coefficient
`-J^-1 a²` with this literal J on both sides, retaining the minus. Here a
is an arbitrary AB endomorphism, not a constructed rational coefficient;
this theorem does not assume or prove its finite expansion. Importing
odd rank-one consumers check both dot signs, their anticommutation, the
square transports, distinct content parities and the negative composite.
No nonzero factor model is constructed. All statements hold over any
commutative ring; there is no weight-height case split or additional
field, domain, flatness, finite-colour or independent-root hypothesis.

The componentwise prescribed rational a and finite-series identity are
now supplied by `RouquierHomMixedRational.lean` above. Assembly from
inputwise local nilpotence, then bending in the specified adjunctions
to prove (4) and raw comparisons (5), remain open. Retain alpha, beta,
gamma, xi and the source-height normalization, including exceptional
zero. No literal mixed-entry comparison, fusion or detector is claimed.

## Negative precomposition windows and the literal mate slide

`RouquierHomPreMateSlide.lean` proves `homContentCrossing_slide` from the
factor’s `slide_left` relation and the prescribed reversed crossing
`-q pre(t)`. Applying `rouquierMate_slide` to the specified normalized
pre adjunctions gives `homContentPreMate_slide`, equation (1) of
`SwappedHomInversion.md` §2. No slide for an inverse component is assumed.

`RouquierHomPreNegativePowers.lean` defines exponent −n by the nth power
of the inverse probe dot. Both whiskered inverse identities are proved.
`homPreDotInverse_power_supernatural`, `homPreNegativeCup_supernatural`
and `homPreNegativeCap_supernatural` give signed naturality on the full
Hom supercategory. The coordinate theorems retain alpha at −n and beta
at −n, including the inverse `leftAdjScalar` at the source height. At n=0
they agree with the existing nonnegative windows. Gamma and xi conventions
are unchanged; this slice does not use or alter either comparison.

Hypotheses: supplied Rouquier family in a Π-2-supercategory over an
arbitrary commutative ring; invertibility of the probe dot only for the
negative powers. No field, domain, flatness, finite-colour, independent-root
or global nilpotence-bound hypothesis is introduced. Importing odd rank-one
examples verify the mate-slide sign, both inverse identities, odd and even
negative-power naturality, both coordinates and exponent zero. These are
consumers of supplied factor data, not a nonzero factor construction.

Remaining and next target: prove `SwappedHomInversion.md` §3 (3), the finite
expansion in the nilpotent postcomposition reservoir variable for the
prescribed swapping entries, then bend them in their actual adjunctions
to obtain the literal central entries (4) and raw comparisons (5). Retain
`-J^-1 a²`, every alpha/beta/gamma and xi sign, and reservoir bounds local
to each content. No central-entry comparison, fusion or detector theorem
is asserted here.


## Normalized precomposition supernatural inverses

`homContentPreSuperInvNeg` and `homContentPreSuperInvPos` lift all five
pointwise augmented inverse identities into the full Hom SCat superfunctor
category at opposite factor-height signs. The normalized crossing mate is
the literal adjunction mate, while every dotted unit and counit is the
specified raw-power window. Signed naturality holds on arbitrary odd Hom
morphisms for the mate, the dotted windows and every inverse principal,
row and column. The two normalized shift-removal coordinates have equal
left-adjunction parity; their contributions cancel around each transported
factor inverse entry. The row and column proofs retain the left-adjunction
parity inside the raw cup/cap windows; the cap column retains the beta
coefficient at the source height, and both principals retain gamma.
At zero height the principal supernatural inverses agree, with
`homPreGamma p 0 = koszulSign p p`, not an implicit unit coefficient.

The hypotheses are a supplied Rouquier family in a Π-2-supercategory over
an arbitrary commutative ring. Odd rank-one importing examples check all
five identities at Hom heights −2 and 2, odd–odd signed naturality for
both inverse principals and the first dotted cup and cap, beta and gamma
signs and the zero-height comparison. No nonzero factor action is
constructed. Mixed-sector blocks, fusion and full nondegeneracy remain
separate obligations; the next bounded target is the source's mixed Hom
block comparison using these inverse transformations, not a conditional
repackaging of them.
## Normalized precomposition inverse at positive Hom height

`homContentPreInvPos` supplies all five `SuperSumInvTo` identities for the
prescribed normalized pre-Hom mate and dotted counits when the factor height
k is nonpositive (Hom height −k ≥ 0). It transports the reversed factor cap
window through the same homogeneous source and target coordinates and their
even associators. The normalized cap comparison retains the inverse
`leftAdjScalar` at the source height; its integral involutive coefficient is
`homPreBeta`, including the sign depending on the dot power. The principal
inverse retains gamma(k), including gamma(0)=(-1)^p, and the cap columns
retain the ordered finite triangular series. `homContentPreInv_zero` identifies
the two principal inverses at the empty window. The odd rank-one importing
examples exercise all five products at Hom height 2, the nontrivial beta
coefficient, and the zero-height principal comparison.

The hypotheses remain a supplied Rouquier family in a Π-2-supercategory over
a commutative ring. No nonzero factor model or inverse premise on the
prescribed Hom maps is inferred. Bundling the pointwise inverses into
supernatural natural transformations is established above for both
orientations. The remaining obligations are the central mixed blocks and full
fusion; neither follows solely from these sector inverses.


## Normalized precomposition inverse at nonpositive Hom height

`homContentPreInvNeg` in `RouquierHomPreInverse.lean` supplies all five
`SuperSumInvFrom` identities for the prescribed normalized pre-Hom mate and
dotted units, with principal parity p, nth window parity np and window length
k.toNat when the factor height k is nonnegative. The Hom height is −k.
The hypotheses are a supplied Rouquier family in a Π-2-supercategory over a
commutative ring; no inverse hypothesis is added on the Hom maps.

`RouquierHomPreCoordinates.lean` constructs the actual source and target
isomorphisms, including their even associators, and proves that their
homogeneous parities agree by the adjacent-height equation. The existing
principal and dotted-unit formulas identify the forward entries after
transport of `leftWindowInvFrom`. The inverse principal has coefficient
gamma(k), the inverse rows have the involutive coefficient alpha_n, and the
finite ordered triangular series in `leftWindowCupRowNat` is retained.
`homContentPreInvNeg_zero_principal` keeps gamma(0)=(-1)^p rather than
identifying it with one. The importing odd rank-one examples exercise the
inverse products at Hom heights −2 and 0 and the nontrivial alpha_1 sign.

The positive Hom-height cap-window orientation, zero-height principal
agreement and both supernatural lifts are proved above. Full fusion and
nondegeneracy remain separate obligations. The factor family is still input
data, not a constructed nonzero model.

## Raw reversed left-window inverses

`RouquierLeftWindowInverse.lean` proves the raw augmented inverses from
`ReversedReservoirMatrix.md`, §§3–5. At positive factor height the prescribed
left dotted cup window, together with `-sigL`, has principal inverse `sig`
and explicitly transformed inverse rows. At negative height the dual left
cap window has explicitly transformed inverse columns. All five inverse
identities hold in each regime; at zero height both windows are empty and
both principal products are identities.

The old window index is reversed. Its transition is unit triangular, and
its inverse is the finite ordered series in `1 - transition`. Coefficients
remain ordinary identity endomorphisms, not central scalars. The annihilation
and old-coordinate expansion are derived from the existing inverse relations
and signed dot slide. Window entries, inverse rows and inverse columns retain
parity `p(h+1)+np`. Neither dot invertibility nor dot nilpotence is required.

The next step is transport through the specified homogeneous pre-Hom
coordinates and the known alpha, beta and gamma normalizations at Hom
height `-h`, including the exceptional gamma at height zero. These raw
factor identities alone are not yet a pre-Hom augmented inverse, a full
Hom family, fusion, or a nonzero model construction.
## Decorated matching-family specialization

`ScalarChangeMatchingFamily.lean` proves that coefficient change commutes with
horizontal placement, `bubAt` on every closed diagram, and `xlay`/`xev` on
every extended layer and word, including both normalized left bends. For the
actual fixed `MatchingBasisChoice` and its serialized dots, the image formula
`homMap_expansion_single` combines this with `homMap_betaSYM`; the finite
`homMap_expansion` follows by additive induction, and
`homBaseChange_expansion_single` expresses the same generator formula through
the tensor comparison. The original datum, weight group, representatives and
full odd/exterior coefficients remain unchanged. The two-odd-colour
`ZMod 9 → ZMod 3` check uses an inhabited complete choice containing a literal
oriented cup and two dots, together with an exterior/elementary bubble
coefficient; separate layers exercise a normalized left cap.

The remaining obligation for arbitrary-ring nondegeneracy is an independent
universal diagram basis (equivalently injectivity of the matching expansion).
Neither the image formula nor the tensor comparison proves that basis or
injectivity of bubble evaluation.

## Full coefficient and bubble specialization

`ScalarChangeBubbleFamily.lean` constructs a ring homomorphism on the all-colour
polynomial/exterior algebra `SYM` (1.21), fixing each elementary and exterior
generator while applying the ground-ring homomorphism to coefficients. It
preserves the prescribed shifted units and specializes the full left and right
bubble families of Definition 2.3, including fake negative-dot cases and the
odd bubble. `homMap_betaSYM` commutes with evaluation (1.22) for every `SYM`
expression, not merely generators; `homBaseChange_betaSYM` expresses the same
comparison through the proved tensor equivalence. The two-odd-colour
`ZMod 9 → ZMod 3` consumer checks noninjective coefficient change, the
exterior generator, arbitrary bubble indices and a mixed exterior/elementary
product. No nonzero presented Hom class is asserted.

The diagram-family image formula for the actual `MatchingBasisChoice.layers`
is now proved above. It is distinct from independence of the family, which
still requires the universal diagram basis; no nondegeneracy or injectivity
of `betaSYM` follows from coefficient change.

## Coefficient change on the presented category


`ScalarChange.scalars` carries Brundan–Ellis (1.5)–(1.6) across an arbitrary
commutative ring homomorphism `f : R →+* S`, including units and the odd-colour
invertibility condition on two. `ScalarChange.cScalars` preserves (1.17).
`ScalarChangePresentation.lean` now constructs the forward comparison for
`GroundRingDescent.md`, §7, on the original datum and full weight group:

- `coeffFunctor` uses the free additive-category lift with restricted target
  scalars; `coeff` is the resulting semilinear map on raw linear diagrams.
- `coeff_relation` proves preservation of every `Rel` constructor, including
  all entries of both products for each augmented inverse matrix.
  `coeff_interchange` preserves signed interchange.
- `coeff_mem_ideal` proves preservation of the whole ideal, including arbitrary
  horizontal contexts and arbitrary linear pre- and post-compositions.
- `homMap` descends to the presented Hom quotient, and `presentationFunctor`
  is the induced additive functor. `homMap_diag`, `homMap_layer`, `homMap_cl`
  and `homMap_whisk` give diagram, generator and horizontal-context formulas.
  `homMap_etaP` and `homMap_epsP` preserve the supplied normalized left cups
  and caps, including inverse units and all height cases.

The two-odd-colour `ZMod 9 → ZMod 3` consumer exercises the quotient map,
relations and left adjunction, and sends three times an odd dot to zero.
The coefficient three is proved nonzero in `ZMod 9`; no claim that its
multiple of the presented dot is nonzero is needed or made. No injectivity,
flatness, domain, field, finite-colour or nondegeneracy premise is added.

`ScalarChangeBaseChange.lean` supplies the tensor comparison and its inverse:

- `tensorLin` evaluates each target raw diagram as `1 ⊗` its source class.
- `exists_source_whiskRel` lifts each target relation label, including signed
  interchange, through an identical source relation with any horizontal context.
- `tensorLin_mem_ideal` kills the entire target ideal. The proof expands arbitrary
  target linear pre- and post-compositions into raw diagrams; it does not assume
  that those target contexts lift through the coefficient map.
- `fromTensor` extends `homMap`; `toTensor` descends the inverse evaluation.
  `toTensor_fromTensor` and `fromTensor_toTensor` prove both inverse identities.
- `homBaseChange` is the resulting `S`-linear equivalence
  `S ⊗[R] Hom_R(a,b) ≃ₗ[S] Hom_S(a,b)`, using explicitly `f.toAlgebra`.
  `toTensor_cl`, `toTensor_etaP` and `toTensor_epsP` retain every inverse-entry
  generator and the prescribed normalized cups and caps.

The two-odd-colour `ZMod 9 → ZMod 3` tensor consumer exercises both directions,
annihilation of the coefficient three inside the tensor product, both inverse-entry
families, arbitrary contextual relations, and the normalization unit `-1`.
This completes the presentation comparison of `GroundRingDescent.md`, §7,
item 2, for arbitrary commutative rings and arbitrary unchanged datum and weights.
It does not prove arbitrary-ring nondegeneracy. The next obligation is the
universal diagram basis and its diagram-family image formula; only then can
`homBaseChange` transport that basis to a specialization.

## Finite-subtype restriction of defining relations

`FiniteColourRestriction.lean` constructs `Datum.restrictColours`,
`Scalars.restrictColours` and `CScalars.restrictColours` on `J : Finset I`.
The weight group remains the original `X`; roots, coroots, parity and
parameters are inherited by evaluation on the subtype. Roots need not be
independent, and the coefficient ring may be trivial.

`FiniteColour.inclusion` is a parity-preserving signature map and therefore
acts on all free diagrams. `diagram_mkD` computes its action on complete
normal-form layer lists. `restrictLabel` handles every constructor of
`Rel`, with `relationLabel_restrictLabel` proving the roundtrip.
`linear_relation` proves compatibility with every defining linear
expression, including all finite inversion sums and scalar coefficients.
`linear_restrictLabel` and `relation_finite_lift` give the finite-subtype
lift of each user relation. Their heterogeneous equality records only
the explicit boundary-word identifications, not an additional hypothesis.

`RelationContext.colours` now includes `allRelColours`: raw user-label
parameters, or the two generating shapes and intervening word of an
interchange instance. Expanded linear support alone is insufficient:
the zero-ring consumer proves that the cup/cap relation has empty linear
support while its raw support is the singleton containing its colour.
`cupCapDiagram_support` computes the interior diagram support, and
`cupCapRelation_restricted` lifts the relation to its computed singleton.
The importing consumer also exercises the mixed braid relation on the
connected odd/even datum with nonzero interior coefficients over ℚ.

`FiniteColourContextRestriction.lean` now restricts arbitrary supported
free diagrams, not only normal-form diagrams. `restrictWord`, `restrictObj`,
`restrictShape`, `restrictLayer`, `restrictLayers` and `restrictDiagram`
retain every original region label. `inclusion_layer_valid_iff` and
`inclusion_chain_iff` reflect validity through the existing signature map.
`diagram_restrictDiagram` and `supported_diagram_lift` recover the entire
original free expression, using casts along proved boundary equalities.
Internal colours of closed cup/cap diagrams are included.

`restrictInterchange` restricts both generating vertices and the middle
word from raw support. Its validity is proved; `restrictInterchange_odd`
retains each generating parity and `restrictInterchange_sign` retains the
integer sign. `includeInterchange_layers` recovers both ordered layer lists,
and `includeInterchange_rel` / `supported_interchange_lift` recover the full
signed linear relation over any commutative ring. `allRelColours_interchange`
identifies this raw support with the one in `RelationContext.colours`.
The importing consumer applies the free-diagram lift to a closed odd
cup/cap and the signed-relation lift to two adjacent odd dots, over both ℚ
and the zero ring. It also verifies that a cup/cap's expanded zero-ring
support is empty while its raw and interior supports remain singleton.

`FiniteColourIdealRestriction.lean` extends diagram restriction to finite
linear combinations at canonical common restricted endpoints.
`restrictDiagramAt` identifies all diagram summands at those endpoints;
`include_restrictDiagramAt` and `include_restrictLinear` recover the entire
free expression after inclusion and endpoint transport, over any
commutative ring, including the zero ring. `inclusion_cast_comp` and
`inclusion_lin_whisker` prove compatibility with composition and
whiskering at transported endpoints, without changing region labels.
The result is not yet an ideal-membership theorem. Both kinds of
presentation generator now have typed restricted lifts: `inclusion_allRel`
uses the raw relation parameters and handles both interchange parities.

`FiniteColourContextLift.lean` proves `supported_context_lift`. Its
`ContextLift` records the restricted contextual generator and recovers the
raw `AllRel` label, both whiskering contexts, pre/post linear diagrams and
the complete value through inclusion. `ContextLift.idealGen` identifies
the lifted value as an actual generator of the restricted presentation
ideal. `inclusion_whiskerOK_iff` reflects whiskering compatibility;
`supported_linear_lift_at` uses prescribed common endpoints rather than
nested transports. No field, domain, flatness or independent-root
hypothesis is needed. Raw labels survive zero-ring cancellation.

The importing consumer uses a cup/cap relation with nonempty left and
right whiskering and closed cup/cap pre/post diagrams. It also uses
whiskered interchange with two-dot pre/post diagrams at both parities,
over ℚ and the zero ring. It extracts ideal generation and exact recovery.

`FiniteColourIdealDescent.lean` proves `supported_ideal_lift_at`: induction on the
finite contextual span lifts every generator into the restricted presentation
ideal at one prescribed pair of restricted endpoints, then closes under zero,
addition and scalar multiplication through linear inclusion. The generator
transport uses injectivity of raw object inclusion, not faithfulness of the
presented category. Arbitrary original weights and commutative coefficient
rings, including the zero ring, remain unchanged. The importing consumer
lifts a sum of two distinct positive-inversion matrix relations with nonempty
whiskering and internal cup/cap diagrams at common endpoints, over the mixed
Bool datum and both ℚ and the zero ring. Earlier signed interchange
consumers retain both parity signs.

Open: derive equality in some enlarged finite-colour presentation from
`eq_finiteColourIdeal` and `supported_ideal_lift_at`. Enlarge the witness by
both input diagrams' `linearColours` before `supported_linear_lift_at`;
the support of their difference may hide cancelled colours. Use the
restricted quotient's `lin_eq_iff` after identifying the included difference
with the descended ideal element. No faithfulness for a chosen finite J is
asserted. Arbitrary-colour detection and nondegeneracy remain separate.


## Signed linear dot cancellation

`LinearDotCancellation.lean` proves injectivity of `targetRightDot -
targetRightCoefficient z`, where `z` is the cyclotomic image of the old
`affineLastDot`. The odd dot anticommutes with this coefficient, so the
square is `targetRightDot² + targetRightCoefficient (z²)`. At even colour
the complementary product instead gives the difference of squares.
`contentTargetRightDot_sub_lastDot_injective` transfers cancellation through
`contentTargetEquiv` into its fixed-projector submodule, not an equivalence
onto the full target. No domain, flatness, monicity or nonzero-quotient
hypothesis is added. Height zero and odd cubic shifts remain included.

This is cancellation only. The all-prefix relation-killing step is now
proved above for ordinary polynomial coefficients; signed polynomial
transport and induction needed for global QP remain. No global QP,
projective resolution or full nondegeneracy conclusion follows here.


## Supernatural postcomposition augmented inverses

`RouquierHomPostNaturalInverse.lean` proves signed naturality against arbitrary
homogeneous probe morphisms, including odd ones, for the prescribed dot
powers, mate, cups, caps and both families of inverse entries. The even
source and target coordinate comparisons are natural isomorphisms; the
inverse entries are transported from the specified factor maps, with the
original right adjoint `N S`. Every raw natural-number inverse entry is
retained, while product identities use the finite height window.

`RouquierHomPostSuperInverse.lean` constructs `homContentPostSuperInvPos`
and `homContentPostSuperInvNeg` in the existing SCat Hom category. All five
identities are lifted by homogeneous component extensionality, and the two
zero-height principal inverses agree as supernatural transformations. The
principal map equals the actual ordered cup–crossing–cap mate. The even
natural lifts use literal `homParityShiftDatum` comparisons, including the
identity summands, not unsigned shift identifications. No object-category
biproduct hypothesis is needed.

This closes the natural-transformation packaging of the same-colour local
augmented inverse. It does not supply the remaining fields of a full Hom
Rouquier family, mixed-sector braid relations, fusion, negative dot powers,
or a nonzero factor model in Lean.

## Pointwise content-shifted postcomposition inverse

`RouquierHomPostInverse.lean` constructs `homContentPostInvPos` and
`homContentPostInvNeg` from the specified factor inverse and the checked
principal and dotted-entry comparisons. All five finite-window products
and homogeneous parities hold over a commutative ring, at every content
and height. The forward maps remain the prescribed mate and dotted unit
or counit, rather than maps defined by conjugation.

The even-component theorems retain the literal parity-shifted identity
summands, including their diagonal and off-diagonal products. The principal
inverse, inverse rows and columns have explicit factor-coordinate formulas;
the zero-height presentations agree. These pointwise data are lifted to
supernatural transformations by the modules above. Fusion and construction
of a nonzero factor model in Lean remain separate.


## Input-side prepend decomposition

[PrependCoordinates.md](PrependCoordinates.md) records the construction for
the whole affine prepend corner at all heights, including height zero.
`PrependEquivalence.lean` now checks this affine coordinate equivalence.
Inverting `parabolicEquiv` yields the unique factorization
`w = d_j * blockPerm 1 v`; the input dot list splits uniquely into zeroes
and shifted old dots. Unitriangularity then gives spanning and independence,
and associativity proves right-old-algebra compatibility. Explicit balanced
forward and backward maps are supplied in the written argument; no flatness,
projectivity, diagram reflection or coefficient centrality is assumed.

`InputParabolic.lean` checks `prependPermutationEquiv`,
`length_prependPermutation` and `prependCrossingWord_spec`.
`CyclotomicAction/PrependCoordinates.lean` constructs the finite crossing
sums `prependShuffleElement` and the prescribed terms `c_j x^m φ(b)`.
`prependPBWTerm_corner` and `prependPBWCorner_right` check these terms in
the existing corner and right action. The consumer also exercises the
existing `qCoefficient` right action at the corresponding tensor terms.
The whole corner has free old-algebra coefficients in the written proof;
a fixed target word instead has idempotent-summand coefficients.

`PrependBasis.lean` now checks the input leading-index equivalence
`PrependIdx.leadEquiv`, the concrete chronological diagram comparison
`prependElt_eq_comp`, and `prependElt_approx`. Applying `basisOfTriangular`
gives `prependBasis`, a scalar basis of each `Hom(i :: s,t)`, including
height zero and repeated colours. Its old coefficient is the existing
normal form `PrependIdx.old.nf`.

`CyclotomicAction/PrependMatrix.lean` identifies the scalar prepend diagrams
with matrix terms: `prependPBWTerm_old_nf` sends the single old normal form
to the single `prependElt`. The intermediate formula `prependPBWTerm_single`
is valid for every old morphism and new exponent, including zero.
`prepend_single_expansion` gives the resulting finite expansion of every
allowed matrix entry, with scalar coefficients from `prependBasis.repr`
and single old normal forms as the old-algebra coefficients.

`CyclotomicAction/PrependEquivalence.lean` regroups finite scalar entry
expansions into old-algebra coefficients. `prependExpansion_projection`
identifies reassembly with multiplication by the actual prepend idempotent,
and `prependExpansion_injective` recovers coefficients using `prependBasis`
and `basisNF`. Thus `prependCoordinateEquiv` is the literal finite sum of
`prependPBWCorner`, with both round trips and forward/inverse right-action
laws. Its consumer includes repeated colours, old dots and a nonidentity
permutation, height zero, and exponent zero.

`PrependTensorCoordinates.lean` now checks the balanced extension (9):
`prependTensorEquiv` is an explicit additive equivalence for every unital
left old-algebra module, including height zero. The maps are the finite
sum of elementary prepend tensors and the balanced affine-coordinate
extraction, with both round trips proved without flatness.
`PrependCoefficientCoordinates.lean` specializes to the prescribed shifted
`qCoefficient` at affine height r+1. `qPrependTensorEquiv_symm_insert`
retains its parity involution; `qPrependTensorEquiv_symm_right` identifies
the prescribed right cyclotomic action coordinatewise. These are additive
and right-coefficient comparisons, not assertions of a new ambient action,
k-linear tensor structure, or tensor grading. Content comparisons remain
projectors on the uncut tensors. The degree-two raising formula and
coefficient-difference cancellation are checked below.

## Prepend square-dot operator and coefficient cancellation

`IntertwinerSquareDot.lean` checks the square operator needed for KKO I,
arXiv:1206.5933v2, Lemma 8.1 and Theorem 8.5. `affineFirstDot_sq_comm`
commutes the first-dot square with every old affine element, including at
height zero. `targetRightDot_sq_tmul` identifies the square of the existing
shifted right dot on `InductionAlong.Ind` with two first-dot corner actions
and the unchanged `qCoefficient`. `targetDotCorner_twice_val` identifies
that corner value with right multiplication by the first-dot square.
`contentTargetRightDot_sq_tmul` proves the same cancellation of the
coefficient involution on the unital content tensor. These require only
the existing finite colours, scalar datum, commutative ground ring and
polynomial homogeneity; no monicity or projectivity assumption is added.
The tensor statements retain positive coefficient height. The consumer
uses an odd-degree cyclotomic polynomial and arbitrary height and content.

`PrependDotCancellation.lean` checks `prependPBWTerm_mul_sq` using the
prescribed order `c_j x^m φ(b)` and whole-old-algebra square commutation.
`targetRightDot_sq_prepend` and `qPrependTensorEquiv_symm_sq` identify the
existing shifted right-dot square with raising m by two in the additive
balanced coordinates. `targetRightDot_sq_sub_coefficient_injective` then
proves injectivity of the square minus the existing right coefficient
operator for arbitrary cyclotomic c; `targetRightDot_sq_sub_lastDot_sq_injective`
specializes to the prescribed last-dot square. The proof uses a maximal
occupied exponent in finite support, not tensoring scalar independence.
It keeps all shuffle indices, repeated colours, polynomial parity and the
shifted coefficient at affine height r+1. The consumer includes odd cubic
polynomials, an odd coefficient shift, odd dot anticommutation, multiterm
families, last-dot-square and nonhomogeneous coefficients, and zero boundaries.

The next step is to identify the odd linear difference and its square
(the sum of the prescribed dot squares), then use this cancellation in
the global QP argument. The coefficient-difference theorem permits negative
coefficients as well; it does not itself identify that square or supply
the QP map identity. Reversing the difference changes its leading sign
but not injectivity. The old-dot contribution is the coefficient right
action, not a right-linear endomorphism of the noncommutative old algebra.
The empty old word
has no old last dot and is the separate base case of the QP induction,
not a case of cancelling a difference of a dot with itself. The proposed
arguments in `DeformedGlobalQP.md` and `DeformedProjectiveResolution.md`
still require their remaining operator identifications and QP induction. No all-height QP,
projectivity, literal P, or full coefficient-extension theorem follows.

## Repeated-odd two-strand cyclotomic error

`IntertwinerError.lean` proves the local quotient reduction needed in KKO I,
arXiv:1206.5933v2, Theorem 8.5 for the word `[i,i]`, with `p(i)=1`.
For `D=v²-u²`, `S=u²+v²`, the existing odd intertwiner `g` gives
`K=Tg-S=S-D(v-u)T` and `H=v²+2uv-u²-(v+u)DT`.
`error_pow` proves `u^m K = (if Even m then K else H) v^m` for every natural
exponent. `error_polynomial` yields the corresponding right factorization
for a central-coefficient polynomial supported in one parity.

`repeatedOddError_factor` instantiates the presented quiver Hecke dots and
crossing, using `oddTwo_block`; endomorphism products reverse composition.
The existing `CyclotomicPolynomialParity` condition is **homogeneity**, not
necessarily even support: odd degree uses H, even degree uses K. No extra
even-degree, monicity, nontriviality or domain hypothesis is imposed.
Constants and the zero polynomial are included.
`prepend_generator_single` identifies the right factor with the shifted old
cyclotomic generator, including its constant term. Balancing in the existing
`InductionAlong.Ind` over `prependAlgebra`, with the existing `qCoefficient`,
gives `repeatedOddError_tmul_zero` for arbitrary left multipliers and shifted
coefficients. Thus the local reduction requires neither inversion nor
cancellation of a dot difference.

This is not a literal Q∘P theorem: P and its `T_i^{Λ_i}` source have not been
constructed. The source's projectivity argument, full multicolour prefix
induction, and super coefficient polynomials remain separate obligations.
The consumer checks arbitrary monomial exponents, zero, and a polynomial
with several even terms and a nonzero constant, in the prescribed tensor.

## Content-tensor right dots

`IntertwinerContentDot.lean` constructs the source last-dot and shifted target
first-dot maps directly with `InductionAlong.Ind.lift` over `ContentAlgebra`.
The even central content identity is fixed by the parity involution; its
restriction pairs the corner dot with the coefficient involution in the
balance proof. No tensor action is defined by equivalence conjugation.
`contentTargetRightDot_insert` retains `(-1)^(p(i)p(β))`, the first dot and
`φ_i` on the coefficient. The forward comparisons commute with the existing
content-dot maps, and `contentTensorShiftedQ_rightDot` closes the dot generator
of KKO I, arXiv:1206.5933v2, Proposition 8.4 alongside the coefficient theorem.
The scope remains finite colours, positive coefficient height, polynomial
parity and an arbitrary commutative ground ring, without nontriviality or
signed-left premises. No graded comparison, zero-height extension, full ELV
coefficients or QP conclusion is asserted.

## Independent right coefficient descent

`IntertwinerContentCoefficient.lean` defines the right operators directly by
`InductionAlong.Ind.map`: source coefficients are multiplied in the unital
cyclotomic content corner, and the target restricts the existing shifted
right action to `qContentCoefficient`. Centrality gives source closure;
commutation with the existing affine left action gives target closure and
well-defined balancing. Neither operator is defined by equivalence conjugation.
The pure-tensor formulas, compatibility with `sourceContentRightCoefficient`
and `targetContentRightCoefficient`, and reverse composition law are proved.
`contentTensorShiftedQ_rightCoefficient` intertwines these operators for the
existing prescribed moving-strand Q. Finite colours, positive coefficient
height, arbitrary commutative ground ring and polynomial parity are unchanged.

This supplies the coefficient generator of KKO I Proposition 8.4; the dot
generator and its first-dot/involution sign are supplied above.
No signed-left-linearity premise is needed.
The consumer checks all-odd and mixed data and audits every owned declaration.

## Shifted target tensor over the content algebra

For KKO I, arXiv:1206.5933v2, Proposition 8.4,
`IntertwinerTargetTensor.lean` defines `contentTargetTensor` independently of
`qTargetContent`: the first factor is the prepend left ideal over the unital
`ContentAlgebra`, and the second is the content submodule of the existing
`qCoefficient`. Its action is restricted from `qCoefficientModule`, retaining
the parity-shift twist; no ring structure on the shifted coefficient is used.

`contentTargetForward` includes both factors; `contentTargetBackward` cuts
both by the content identity. `contentTargetBackward_forward` is identity,
and `contentTargetForward_backward` is the existing target content projector,
not identity on the entire height tensor. `contentTargetEquiv` gives the
explicit two-sided comparison. `qContentCoefficientCut_insert` and
`contentTargetEquiv_cut_tmul` identify the cuts with the prescribed shifted
representatives. `contentTensorShiftedQ_representative` proves the literal
moving-strand formula between the separately defined source and target tensors.

Hypotheses remain finite colours, positive coefficient height and polynomial
parity over the existing commutative ground ring and scalar datum. These are
underlying left-module statements, not a graded identification. The direct
right coefficient and dot actions and their Q compatibilities are supplied
above, retaining the first dot, involution and `(-1)^(p(i)p(β))`. Enlarged target-block
support, graded comparison, zero height, full ELV coefficients and QP are
separate obligations.

## Source tensor over the content algebra

`contentSourceEquiv` in `IntertwinerContentTensor.lean` identifies the KKO I §8 source
`R(β+αᵢ)e(β,i) ⊗[R(β)] RΛ(β)` with `qSourceContent`. Both coefficient
algebras use Mathlib's unital idempotent corners; the coefficient action is
the existing quotient map restricted to those corners. The append left ideal
is supported on content `β+αᵢ` (`contentSourceCorner_support`).
The forward map includes both factors. The inverse cuts both factors by their
content identities, is balanced over the unital corner, and has two checked
composites: identity on the source tensor, the content projection on the
height tensor. No arbitrary choice of equivalence or new action axiom is used.
`contentTensorQ_representative` gives the existing moving-strand formula on
this source carrier. Finite colours and positive coefficient height remain;
polynomial parity is needed only for Q.

The shifted target comparison and right coefficient/dot compatibility on
both tensor carriers are supplied above. The
zero-height case, QP and full nondegeneracy are not consequences of this step.

## Bounded cyclic recovery

`upwardCoefficientMap_injective_of_bounded_cyclic_recovery` consumes, for each
fixed pair `t,t′` and degree `d`, one `BoundedCyclicRecovery` at a colourwise
cutoff bounded below by `N > d + 2 * choose(length t, 2)`. It derives the pure
coefficient observation from source precomposition and the normalized
elementary/exterior bubble formulas, extends over `extensionBasis`, and applies
C0 with the unchanged word indices. The theorem works over a commutative ring.
No windows at other pairs or inadmissibly small cutoffs are required; degree
zero still requires recovery, including identities and crossing-only vectors.
The concrete two-colour importing consumer is conditional: construction of
the cyclic action, normalized bubbles and bounded affine recovery remains open.
No nonzero model or nondegeneracy theorem is asserted.

## Content-shifted postcomposition coordinates

`RouquierHomPostCoordinates.lean` bundles the specified
`homContentPostAdjunction` in `SCat`, with right adjoint `N S`, not its
output-shifted replacement. `homContentPostWordIso` is the prescribed
`S(beta_M⁻¹);xi` comparison followed by the even postcomposition associator.
`homContentPostCrossing` transports `W.cross i i h h₂ h h₂` with no scalar gauge.
Its component and parity are proved.

`homShiftConjugationIso_supernatural` proves cancellation of both comparison
signs, for arbitrary shift and homogeneous transformation parity.
`homContentPostFactorCrossing_shift` specializes this to the prescribed factor
crossing. The specified unit and counit have coordinates `u;b⁻¹` and `a;v`,
proved by `homContentPostAdjunction_unit_coordinates` and
`homContentPostAdjunction_counit_coordinates`. The source coordinate has the
signed two-removal formula `homShiftConjugationIso_hom_signed`; its factorization
is `homShiftConjugationIso_comp`. `homShiftConjugationIso_unit_cancel` cancels
the inner shift-square against the shifted word comparison.

`RouquierHomPostPrincipal.lean` now proves equation (B) as
`homContentPostCrossing_principal`: the source-coordinate inverse, specified
`rouquierMate`, and target coordinate compose to
`associator.hom; Z ◁ (W.loc i h h₂).sig; associator.inv`.
The proof cancels the shift comparisons inside the literal mate, then uses
even prefix/suffix coherence and crossing naturality. It covers arbitrary
content, every weight and both parities over a commutative ring; no comparison
premise is added. Odd-colour consumers apply this equality at odd and zero
content shift, jointly importing the normalized precomposition principal
theorem. The Rouquier family remains an input.
`RouquierHomPostPowers.lean` proves the natural-power part of §3 (9):
`homContentPostCup_coordinates` and `homContentPostCap_coordinates` identify
all dotted entries with the literal factor unit/counit words, including their
whiskering and associators. `homContentPostDot_power` identifies powers of the
prescribed shifted dot with shifted raw powers. Both comparison signs cancel;
no transpose sign or invertibility assumption is introduced. These theorems
apply to every finite window, both colour parities, all content and weights.
The importing consumer checks both parities, zero and odd content, and powers
zero and three, and audits every declaration owned by the module.
The pointwise whole augmented inverse and literal parity-shifted summands
are now checked as described above. Negative powers, natural inverse
packaging, swapping mates, fusion and a nonzero model remain separate.


## Raw normalized Hom mate coordinates

`homContentCrossing_coordinates_raw` proves cancellation of both comparisons
in the **defined** mate, with no additional premise. Its source is
`E_h ≫ F_h ≫ Z` and target is `F_h₂ ≫ E_h₂ ≫ Z`. It retains the raw cup,
the inherited crossing evaluated at `F_h ≫ Z`, and the normalized cap
with coefficient `leftAdjScalar i (-nuP)` inverse, not the lower-edge scalar.
The odd rank-one consumers specialize to arbitrary weights and height zero;
they take a Rouquier family as input, not a constructed nonzero model.

The proof first moves the input inverse through the even normalized unit
by ordinary naturality. Crossing supernaturality and the signed counit
give `koszulSign p sigma * koszulSign sigma sigma`. The remaining
unshifted map has parity `p + sigma`; output removal contributes
`koszulSign sigma (p + sigma)`. Their product is one, using edge parity
agreement. Thus no parity comparison or shift functor remains.

## Normalized principal Hom comparison

`homContentCrossing_coordinates` proves (10) of `HomPrincipalMate.md`:
the defined normalized mate in raw coordinates is the insertion of
`(T.loc i h₂ h).leftCrossingWord`, scaled by `-koszulSign p p` and
`leftAdjScalar i (-nuP)` inverse. Its even reassociation uses naturality
and structural coherence without swapping the cup, crossing or cap.

`homContentCrossing_principal` combines this equality with
`RouquierFamily.leftCrossingWord_eq` and `principalWord_scalar` to give
`D_H = gamma(k) P_(-sigL)`, with gamma(k)=(-1)^(p*k) for nonzero k and
gamma(0)=(-1)^p. Both parities and every integer height are covered over
any commutative ring. Odd rank-one consumers check arbitrary height and
height zero, where the component is the insertion of `sigL`.
No new coherence, scalar-evaluation or triangle hypothesis is imposed.

The remaining targets are the shifted swapping mates, their tensor
support, the residual identity-summand matrix, fusion and joint separation.
No whole-matrix or nondegeneracy consequence is claimed here.

## Inherited Hom crossing and its specified mate

`RouquierHomCrossing.lean` defines `homContentCrossing` using the inherited
same-colour `T.cross`, multiplied by `-koszulSign p p` and conjugated by
the even precomposition associator. `homContentCrossing_app` computes every
component and `homContentCrossing_mem` proves parity p.
`homContentCrossing_mate_app` specializes the SCat mate bridge to this
crossing and expands both normalized adjunction components. It retains
both parity comparisons, the counit sign, and c(k) inverse at the cap edge.
The output/input comparisons now cancel by
`homContentCrossing_coordinates_raw` in `RouquierHomMateCoordinates.lean`.
Equation (10) and the principal word comparison are proved above.
The consumer specializes the expanded mate to the odd
rank-one datum at arbitrary weights; no nonzero model is constructed.

## Normalized Hom adjunction in SCat

`RouquierHomSuperAdjunction.lean` packages the specified
`homContentPreAdjunction T W T.leftAdjoints` as `homContentSuperAdjunction`
in the existing `SCat` 2-supercategory. The unit and inverse-scaled counit
are proved even from their normalized formulas; no new zigzag premise is used.
`rouquierMate_scat_app` unfolds the defined mate, and
`homContentSuperAdjunction_mate_app` specializes it to these Hom adjunctions,
giving the literal unit–mapped crossing–mapped counit component at either parity.
The general bridge accepts an arbitrary crossing; the inherited specialization
is given above. Both shift removals are proved in the raw coordinates above;
`HomPrincipalMate.md` (10) is proved above. All heights, the existing normalization c(k), and gamma(0)
are unchanged. The odd rank-one consumer uses arbitrary weights; it does
not construct a nonzero family.

## Unit output comparison

`homContentPreAdjunction_unit_output_coordinates` removes the output shift
following the specified normalized Hom unit and a homogeneous map of parity q.
It retains the factor `koszulSign sigma q` and all cup associators. Its
odd rank-one consumer allows every height and either parity. This first
shift cancellation is now used in `homContentCrossing_coordinates_raw`
with the prescribed crossing and counit. The input comparison cancels
there as well; equation (10) is proved by `homContentCrossing_coordinates`.

## Unnormalized principal word

`RouquierPrincipalWord.lean` proves `HomPrincipalMate.md` §3 (11) at every
integer height: `RouquierFamily.leftCrossingWord_eq` gives coefficient one
at nonpositive height and `koszulSign p p` at positive height. The proof uses
the signed cup/cap pitchforks and the proved canonical F triangle; no new
left-triangle or principal-comparison premise is added. Local nonnegative
and nonpositive theorems overlap at zero and keep its exceptional pitchfork
coefficient. `principalWord_scalar` proves (16), retaining gamma(0)=(-1)^p.
The importing odd rank-one consumer checks arbitrary heights and -1, 0, 1.

The specified shifted Hom mate is identified with this word by
`homContentCrossing_coordinates` and evaluated by `homContentCrossing_principal`.
No whole-matrix, fusion, or separation theorem follows here.

## Residual windows and execution-order comparisons

`HomResidualWindows.md` computes every corrected central Schur window and
the leading comparison `S mod J = L H Q`, with the nilpotent ideal generated
by positive-degree reservoir supercentral coefficients. The original factor
inverses, c(k), gamma(0), parity lifts and every identity summand are retained.
At zero total height the residual is generally nonempty.
`ProbeWindowInverse.md` supplies a finite two-sided inverse algorithm for
the displayed negative-power probe-window matrices H at every pair of
heights, using the specified whole probe inverse, invertible dots and the
literal mate slide. It retains both nonempty zero-total cases and all
parity lifts. Lifting this inverse to the exact residual and constructing
the required localized factor actions remain separate tasks.

`ExecutionBraidNormalization.md` proves the reversal identity
`-C_ij(z,y,x)=(-q_i)C_ij(x,y,z)` and the conditional even rational comparison,
without changing Q. `ParitySectorComparison.md` gives the actual signed
word removals, the forced conditional identification `H_BA=J^-1 h k`, and
one odd AAB braid component. It does not supply the sorted-sector h or
the complete odd/localized comparison. These are written calculations, not
Lean theorems or a full fusion proof.

## Reservoir dotted coordinates

`RouquierHomReservoirPowers.lean` proves `HomSectorTransport.md` §2 (5)
for all natural powers and every reservoir source height. The dot is the raw
`T.dot ▷ Z`; cups and caps are defined using the same normalized
`homContentPreAdjunction T W T.leftAdjoints`. Removing the output comparison
from the cup gives `koszulSign σ (n*p)` times the raw dotted cup. Moving the
cap comparison past the dot power gives `koszulSign σ (1+n*p)` times the raw
dotted cap, retaining `leftAdjScalar⁻¹ • leftCap`. The power has parity `n*p`,
and its naturality is proved for every homogeneous map, not only even maps.
These are window coordinates for the Hom principal and central comparisons;
no principal-block identification, window inverse, or fusion comparison follows
from these formulas alone. The consumer checks arbitrary odd rank-one heights
and powers, and powers zero, one, and two at nonzero output shift.


## Fixed normalized reservoir adjunction

`RouquierFamily.leftAdjoints` now uses the explicit involutive unit
`leftAdjScalar i x = koszulSign σ σ * (if h < 0 then 1 else koszulSign p p)`
at the source height h, with unit `leftCup` and counit `leftAdjScalar⁻¹ • leftCap`.
Both triangles follow from the canonical triangles; no chosen-scalar uniqueness
or faithfulness is used. `RouquierNormalizedHomAdjunction.lean` specializes the
existing `homContentPreAdjunction` without an additional `LeftZigzags` premise.
It proves the reduced cup/output-shift unit formula and the signed-cap counit
formula of `HomSectorTransport.md` §2. The theorem
`homContentPreAdjunction_leftAdjoints_counit_app` retains the outer
`koszulSign σ σ`, with σ at the reservoir source height, and the inverse-scaled
`leftCap`. Homogeneous comparison naturality cancels the shift-square and
commuting maps; the normalized adjunction itself is unchanged. The odd rank-one
consumer checks this component for arbitrary heights and audits all owned
declarations. No fusion or nonzero model is claimed.

## Canonical F triangle and shifted left adjunctions

`OddMath.SKM.reflection_triangle_scalar` in `RouquierFTriangle.lean`
proves the cup/cap reflection scalar product at every integer height by the
binomial recurrence and involutive signs, including the separating height -1.
`SuperRouquierLoc.leftAdj_triangle_F` applies the E triangle to the explicitly
reflected local data, with the derived reflected crossing squares and braid.
It reads back the horizontal-opposite unitors, associator and whiskerings,
then cancels the canonical cup/cap scalar product. Its coefficient is
`koszulSign σ σ * (if h < 0 then 1 else koszulSign p p)`, where `σ=p(h+1)`.

`RouquierFamily.leftZigF_eq` specializes this to every family edge;
`RouquierFamily.leftZigzags` discharges the existing two-triangle condition.
`RouquierFamily.leftAdjoints` normalizes the cap by the explicit involutive scalar.
There is no new cyclicity, faithfulness or left-triangle hypothesis. The
rank-one odd consumer checks arbitrary heights and the boundaries -1 and 0,
and audits every declaration owned by the new module.

This closes the triangle obligation of `SignedFTriangle.md`, not the existence
of a nonzero odd inversion model, the multicolour action, fusion or separation.

## Content-shifted probe augmented inverse

`HomProbeMatrix.md` supplies a written proof of the probe comparison
(B), without assuming the shifted sector's inverse. For fixed reservoir
content, the prescribed Koszul transport is
`Theta=S(beta_M^-1);xi=S M(z_kappa(M-));z_kappa(MM-)` and
`T_BB=Theta;post(t_B);Theta^-1`; the dots are `S(post(x_B))`.
The explicit unit--map--cap computation gives
`B_s^-1;P(T_BB);B_t=post(sigma_B)` with scalar one. The intermediate
four-strand comparison has endpoint signs `(-1)^kappa` twice and crossing
exchange signs `(-1)^(kappa p)` twice, all cancelling.

All dotted cups/caps retain their raw coordinates, also for negative powers
of the invertible probe dot. Both whole augmented matrices and inverses are
transported, with explicit z lifts on every parity-shifted identity summand;
at zero height the empty-window inverse has no exceptional scalar.
Consequently `I_B=B_t;post(R_B);B_s^-1` and
`Rcal_B=post(R_B)`, conditional only on the specified probe factor local
inverse data and coherent crossing prescription. No bare-crossing inverse
is asserted at nonzero height. This discharges the separate probe-sector
input of `HomCentralFeedback.md`; it does not establish or independently
validate that note's central nilpotence result. The literal C/D convention,
residual inversion, grading and full fusion remain separate. No Lean theorem
is added by this written calculation.

## Equal-colour crossing normalization and central feedback

`CrossingNormalization.md` derives the repaired mixed equal-colour matrix
`[[-q a,J],[-J^-1 a^2,q J^-1 a J]]`. With execution AB (reservoir first),
the previous diagonals gave -q, not 1, in the fixed library slides. That
claim is withdrawn. Both slides and the square are derived using the
specified J/dot transport; the swapping maps, factor crossings, dots and
adjunctions are unchanged. This is a written two-strand correction,
not a Lean theorem. The scalar sector-inversion gauge explains the local
sign change but needs a consistently signed comparison family; the even
rational comparison and its mixed-colour braid correction remain open.

`HomCentralFeedback.md` retains the historical literal series C,D and all
shift coordinates. The corrected literal entries are Cnew=-q C,Dnew=-q D;
C,D are normalized corrected mates, as in `FusedFeedbackComparison.md`.
Feedback is unchanged. It factors through the intrinsic left closures
`U_r;f;V_s`, retaining c(k), gamma(0)=q and every inverse identity window.
Their positive reservoir degrees prove fixed-content feedback nilpotence
conditional on the specified factor actions and finite homogeneous coefficient
quotients. `HomProbeMatrix.md` supplies the probe augmented inverse. No probe
grading or uniform infinite-weight-fiber bound is used. The all-height residuals use
`Knew=-q [[0,C],[D,0]]`, not the historical K; they are not inverted.

Next checks: actual cap/cup residual coordinates and
inversion; rational/source/localization braid comparisons, coherent integer
word shifts, full (TC), fusion and separation. No full-action claim follows.
The older restart paragraphs below are historical where superseded here.

## Content-shifted swapping mates

`HomSwappingMates.md` evaluates the two swapping partial mates of the
specified upward matrix, by unit–map–cap words and the normalized snakes.
With kappa'=kappa+p, the raw mixed coordinates are
`(-1)^(sigma kappa') h_A` and
`-(-1)^(kappa p) h_B;g_B`, where, for an odd colour,
`g_B=(X²-W²)(X²+W²)^(-2)` and W is the right-transposed probe dot.
The xi signs and every parity-removal map are retained. Finite geometric
series give g_B inverse, and the note writes both inverse composites for
both shifted maps. Their projected supports contribute no additional
Schur term to the same-sector central block.

This is a written derivation conditional on the accepted normalized
left snake, not a Lean theorem. It supersedes the swapping-mate open
obligations in the historical paragraphs below, but not full (TC).
Central C,D/feedback transport must still include the principal inverse
`gamma(k) f`, particularly `gamma(0)=(-1)^p`, all dotted windows and
homogeneous comparisons. The chosen upward normalization has swapping
degrees 0 and -4d on the presently specified functors: a common degree
-2d requires an additional coherent integer word-shift construction.
No such construction or probe integer grading is assumed here. Residual
inversion, fusion relations and separation remain open.

## Principal component of the reversed Hom matrix

`HomPrincipalMate.md` derives the unbundled same-colour Hom crossing as
`-(-1)^p` times the inherited reservoir crossing from the reversed-slot
KLR slides. In the specified normalized-left Hom adjunction, all four
shift-removal signs cancel. Signed cup/cap pitchforks then give
`C_src^-1;P_H(tau_H);C_tgt = gamma(k) P_R`, where `R=-sigL`,
`gamma(k)=(-1)^(p k)` for nonzero reservoir height k, and
`gamma(0)=(-1)^p`. The exceptional zero coefficient is retained.

This is a written derivation, not a Lean theorem. Combined with the window
calculations in `ReversedReservoirMatrix.md`, the whole-matrix comparison
rescales every finite identity summand and
gives principal inverse `gamma(k) f`. The principal derivation itself
does not use those window calculations. Shifted swapping mates and their
tensor support, (TC), residual inversion, fusion and separation remain
open; a principal-entry evaluation does not establish them.

## Reversed reservoir window comparison

`ReversedReservoirMatrix.md` derives the Hom reservoir height `-k` from
reservoir height k, identifies its two mixed-word coordinates, and computes
both left dotted windows as ordered antitriangular changes of the original
inverse windows. It proves both inverse identities for the resulting
augmented matrices with principal entry `R=-sigL`; their principal inverses
are the original right mate. Integer/parity shifts, cap normalization and
heights zero and plus/minus one are retained.

These are written component calculations, not Lean theorems. That note
leaves `C_src^-1;P_H(tau_H);C_tgt` unevaluated; the separate principal
calculation above supplies its scalar relative to R without changing the
window argument. Same-height right reflection does not give this
weight-reversing comparison. (TC), shifted swapping mates, residual
inversion and separation remain open.

## Specified Hom-sector adjunction and interchange components

`HomSectorTransport.md` derives the unit and counit of the actual
output-shifted reservoir Hom adjunction and the composed probe adjunction.
The reservoir counit has the extra factor `(-1)^σ`; removing two probe
shifts with bare ζ differs from ξ by `(-1)^κ`. It gives all dotted
cup/cap coefficients and the content-changing swapping map of parity p,
using κ′=κ+p rather than identifying it with raw even interchange.

These are written derivations, not new Lean theorems. The remaining
transport comparison must identify the reversed, normalized-left reservoir
augmented matrix and principal inverse with the intended right-factor
coordinates, then evaluate both shifted swapping partial mates. Neither
principal-feedback nilpotence for the actual Hom realization nor full
fusion follows merely from these component formulas.

## Tensor feedback calculations and the remaining transport

`FusedFeedbackComparison.md` gives the six partial-mate supports, the
untwisted external-tensor rational coefficients, and the supported feedback
sign `-(-1)^(p r s)`. It proves principal-block nilpotence only under its
explicit transport condition (TC). Both augmented elimination formulas retain
the identity summands and the residual matrices at arbitrary factor heights.

These are written calculations, not Lean theorems or a fused action. Raw
even interchange is not the odd content-shifted swapping map. The actual
Hom-sector components are supplied above; reversed reservoir matrix comparison, residual
invertibility, fusion relations and separation remain separate obligations.

## Fixed-content reservoir bounds on paper

`DeformedReservoirBound.md` supplies finite-dimensional coefficient
quotients retaining the independent odd ELV parameters and their relations.
Finite right generation plus the central monic annihilator gives finite
dimension of every fixed-content algebra. The enriched supercentre then
bounds identity transformations on all modules, without asserting arbitrary
Hom-finiteness. Positive-degree principal-inverse closures are jointly
nilpotent at each content and on finite content windows.

This is a written proof, not a Lean theorem. It gives no uniform bound over
an infinite weight fiber. Component-preserving degree-zero inverse families
can assemble without such a bound, but identifying the actual fused feedback,
its tensor-factor signs and supports, the residual identity-summand matrix,
and truncation-compatible separation remain separate obligations.

## Canonical signed F triangle on paper

`SignedFTriangle.md` derives the second triangle for the prescribed
inverse-defined cups and caps by horizontal super-opposition and signed
right transposition. It constructs the reflected local data, including the
prescribed mixed mate and every inverse-component comparison; it assumes
neither cyclicity nor the F triangle. With s=(-1)^p, σ=p(h+1), and
e(h)=1 for h<0 and s for h≥0, the canonical F composite is
koszulSign(σ,σ)e(h) id. The E composite is e(h) id. Rescaling only the
cap by the involutive unit koszulSign(σ,σ)e(h) gives the shifted left
adjunction normalization of `LeftZigzags`.

This is a written proof, not a kernel-certified F triangle. The supporting
all-height E-triangle development and the first right-transposition lemmas
are included here, but the inherited cap/pitchfork chain still needs the
full-package CI gate. `RouquierRightTranspose` proves the actual counit
bending equivalence, its cup–map–cap transpose, parity preservation,
linearity, signed anticomposition, and the power coefficient
`q(n)=koszulSign p p ^ (n.choose 2)`. Its concrete local consumer
`SuperRouquierLoc.rightTranspose_capD` proves that the reflected dotted cap
is `q(n)` times the original `capD n`, at every height and parity.
The full-Hom equivalence `SuperAdjunction.unitBend` is also constructed
from precomposition adjunction, with explicit forward and inverse formulas.
`rightTranspose_unit` proves the second bending identity for the same
counit-defined transpose. `SuperRouquierLoc.rightTranspose_cupD` identifies
the reflected dotted cup with `q(n)` times the original `cupD n`, at its
original weight boundary, for every height and parity. Odd two- and
three-dot cups and caps are exercised on the prescribed composites.
No left triangle, cyclicity, faithfulness, or nonzero-model input is used.

`RouquierCompositeAdjunction` constructs `SuperAdjunction.comp` for
`E₁ ≫ E₂` with right adjoint `F₂ ≫ F₁`. Both triangles are derived by
composing the even underlying right adjunctions. `comp_unit` and
`comp_counit` identify the resulting maps with the nested units and counits,
including every associator and unitor. Its consumer applies the same
full-Hom transpose to an odd crossing at arbitrary height; no odd map is
restricted to the even underlying bicategory.

`RouquierTransposeComparison` proves the typed partial-mate comparison:
`mixedMateBend_rouquierMate` identifies `Q(P(t))` with right transposition
for `A₁.comp A₂`, and `mixedMateBend_symm_rightTranspose` gives `R(M(t))=P(t)`.
Here `P` is the prescribed `rouquierMate`; `Q` uses the existing rectangular
Hom equivalence with the adjunctions interchanged, and its inverse `R` has
an explicit unit–map–counit formula. Counit uniqueness, the composite
counit expansion and even-cap interchange prove the comparison for the
full Hom space, including odd crossings. The consumer specializes to
rational scalars, odd parity and arbitrary integral height, retaining local
inversion data as premises rather than asserting a nonzero model.

`RouquierTransposeWhiskering` proves
`SuperAdjunction.rightTranspose_whiskerLeft` and
`rightTranspose_whiskerRight` for arbitrary maps between independently
right-adjointable source and target 1-morphisms. Both composite adjunctions
are explicit. The counit-bend proof moves each arbitrary argument only past
even counits or coherence maps, so neither law carries a sign.
`rightTranspose_associator_inv` identifies the transpose of the inverse
associator with the inverse associator on the reversed adjoint string,
using the two explicitly bracketed triple composite adjunctions. Its
consumer checks both whiskered odd dots retain parity one.

`HorizontalSuperOpposite` constructs `HOpS B` and its `TwoSupercategory`
instance on the unchanged Hom supercategories, with reversed 1-morphisms,
exchanged whiskerings, inverse reversed associator and exchanged unitors.
Its interchange proof solves the original signed equation using the
self-inverse Koszul sign. `SuperAdjunction.horizontalOpposite` reflects
`E ⊣ F` to `F ⊣ E` with the same unit and counit and exchanged snakes.
The rational odd consumer retains degree-one transposed dots and verifies
the negative odd–odd interchange in the reflected category.

`RouquierHorizontalReflection` proves `rouquierMate_horizontalOpposite`, identifying
the reflected `rouquierMate` with `mixedMateBend.symm` on arbitrary maps.
Only its even prefix and suffix use underlying bicategorical coherence.
Combined with `mixedMateBend_symm_rightTranspose`, it recovers the original
prescribed mixed mate from the reflected mate of the right transpose;
the rational odd consumer checks this for a degree-one crossing.

`RouquierReflectedLocal` constructs `SuperRouquierLoc.horizontalReflection`
at the unchanged height, with transposed dots and crossing `s M(t)`.
Both signed slides follow by transposing the original opposite slide.
The prescribed mixed mate is `s` times its original, and each dotted
window entry is `q(n)` times its original. `SuperSumInvTo.rescale` and
`SuperSumInvFrom.rescale` prove all five augmented inverse equations in
both orientations, including the empty window. Inverse components are
copied explicitly; the four `horizontalReflection_invPos/Neg_f'/g'`
comparison formulas are definitional. `reflectedCross_square` transports
the nilpotent square. The rational odd consumer checks both height-zero
inverses, the negative second-window coefficient, and both boundary windows.

`RouquierReflectedBraid` proves `rightTranspose_associator_hom` by
transposing the inverse identity, and `rightTranspose_bracketed_whiskerRight`
with the explicit triple composite adjunctions. `reflectedCross_braid`
transports the bracketed three-strand braid to the prescribed crossings
`s M(t)`; the equal palindromic transpose signs cancel without any
cyclicity or left-triangle hypothesis.

`RouquierReflectedCupCap` identifies the canonical `sigL`, every `cupN`
and `capN`, the dotted right cups/caps, and both piecewise `cupL`/`capL`
with their original maps times the coefficients of `SignedFTriangle.md`
§5. All integer heights, including zero and both unused zero branches,
are retained. The consumer specializes both canonical comparisons and
the bracketed braid to odd parity over rational scalars.

Still missing in Lean are the symbolic all-integer-height scalar product
`a(h+2)b(h)=koszulSign (p(h+1)) (p(h+1))`, and application of the local
E theorem followed by explicit horizontal-opposite readback. Neither the
canonical F equation nor `LeftZigzags` is discharged yet.
Transport to fusion and regular-bubble detection remains separate.

## Full graded deformed action on paper

`DeformedActionAssembly.md` and `DeformedMixedBraid.md` complete the written
action of the full underlying SKM supercategory over the stated full-ELV
coefficient algebra. The construction includes the prescribed distinct-colour
mate, mixed quadratic parameter normalization with reversed labels, the
arbitrary-exponent corrected braid, and explicit zero out-of-range inverse
components. It uses the same-colour matrix argument below, without a further
kernel or pivot assumption. Tensoring applies to all modules, not just projectives.

`DeformedGradedAction.md` supplies the standard SKM integer grading:
E_i is unshifted induction and F_i1_λ=q^[d_i(h_i(λ)−1)] Res_i1_λ.
It transports the adjunction on each edge and checks every generator and
inverse-component degree. Infinite weight fibers use finite-bidegree Hom
families, not unrestricted products of underlying Hom spaces.
This is not a Lean implementation. Hom-finiteness, fusion, detection and
nondegeneracy remain open.

## Prescribed same-colour inversion on paper

`DeformedCyclotomicTopRow.md` supplies a proposed written proof of the
previously implicit cyclotomic top row. With the source's short-column
inclusion, P' sends h tensor pi^epsilon b to
h f_i(x_1)(tau_1 ... tau_(n−1)) tensor pi^p b. Its image is the kernel
of the canonical quotient onto B e tensor_D Pi^p(e B), whose vertical
arrow is a tensor pi^p b ↦ a tau_n b. The proof tensors the lower-height
resolution only for right exactness; injectivity comes from P and the
affine column embeddings. It retains total coefficient parity and the
even-cutoff relation, including the absent-corner cases. This argument
is not independently accepted or Lean-checked; it does not promote full
factor/action existence. Review of this bridge is the next written target.

`DeformedMackeyBoundary.md`, `DeformedBoundaryDivision.md`,
`DeformedRouquierMatrix.md` and `DeformedMatrixComparison.md` now give a
written proof that the prescribed tensor-mate/dotted-cup/dotted-cap matrix
is invertible at every height over the stated full-ELV coefficient algebra.
The odd parameters remain independent, with the required coefficient
relations; no exterior-flatness assumption is used. The cap rows require
output parity transport between explicitly twisted bimodule targets.
The kernel-window and semilinear unit-pivot calculation are proved, not
extra inversion hypotheses. The local right-factored g signs in
`DeformedProjectiveResolution.md` and `DeformedGlobalQP.md` are corrected
without changing the definitions, cancellation or final QP formula.

This is not a Lean theorem. The full-coefficient distinct-colour mate and
graded action are supplied above; fusion remains separate. The existing polynomial-coefficient Lean
implementation is narrower. The general nondegeneracy conjecture remains open.

## Deformed right projectivity on paper

`DeformedSquareResolution.md` assembles the written right-projectivity argument
from `DeformedGlobalQP.md` and `DeformedIdealSum.md`. It constructs the actual
central right `B[s]` actions and finite corner-projective PBW modules, proves
P-linearity and injectivity, identifies its cokernel, and lifts a central monic
annihilator through the nilpotent odd-parameter ideal. The coefficient twists
are retained in both raw quotient and right-B-linear tensor coordinates.
These are written arguments, not Lean theorems. Left projectivity and reverse
adjunctions remain separate; prescribed same-colour inversion is supplied above.

## Actual induced-tensor parity grading

`CyclotomicAction/IntertwinerGrading.lean` constructs `qSourceSpace` and
`qTargetSpace` on the **existing** `InductionAlong.Ind` carriers. The raw tensor
is the original integral tensor. Its odd projection is the sum of even-odd
and odd-even tensor projections. `InducedParity.relation_odd_mem` proves that
the original balancing submodule is stable, by homogeneous decomposition of
the corner, balancing algebra, and coefficient. Restricting its scalars to
`k` leaves the quotient carrier unchanged; no comparison equivalence is assumed.

`qSourceSpace_tmul_mem` and `qTargetSpace_tmul_mem` give total tensor degrees;
`qSourceSpace_smul_mem` and `qTargetSpace_smul_mem` prove grading of the actual
left action. Corner projection stability follows from the even idempotent,
and append/prepend and coefficient action grading are proved, not postulated.
The imported consumer exercises all-odd height three and mixed height two,
both with nonzero coefficient shift, and audits the module's declarations.

`contentMove_parity` now proves the matrix degree `p(i)p(β)` from
`intertwinerHom_parity` and `moveHom_parity`, including the equal-odd polynomial
intertwiner. The finite matrix sum uses its actual content support and the
order-independent multiset parity. `parityCyclotomicContentQ_even` proves
Q-evenness on these existing source and target spaces, using the pure-tensor
criterion and the two cancelling parity shifts. `parityCyclotomicContentQLinear`
is only scalar restriction of the existing Q, not a replacement map.
The consumer specializes actual Q-evenness and pure-tensor membership at
all-odd height three and mixed height two, both with shift one, and audits
all owned declarations. Right-dot degree is now proved in
`IntertwinerDotGrading`; full right-superalgebra structure remains open.
Source comparison: KKO I, arXiv:1206.5933v2, Proposition 8.4 and (8.13),
PDF page 42. Finite colours, positive indexing and
`CyclotomicPolynomialParity` are retained. Ordinary coefficients
`I → Polynomial k` are still narrower than full odd-coefficient deformations.
No full Proposition 8.4, QP formula, or nonzero categorical inversion model
is asserted.

## Finite polynomial operators on the moving-strand quotients

`CyclotomicAction/IntertwinerRightPolynomial.lean` evaluates every finite
ordered family `∑ t^m ⊗ c_m` on the same `qSourceSpace` and `qTargetSpace`.
`sourceRightPolynomial` and `targetRightPolynomial` are additive maps to
endomorphisms; their constant-unit law is proved. `rightPolynomial_Q`
proves equivariance for every such family, from the existing dot and
coefficient formulas, without any assumed action interface.

`sourceRightMonomial_comp` and `targetRightMonomial_comp` prove the
ordered multiplication law: composing the operator for `t^r ⊗ b` with
that for `t^s ⊗ c` gives `(-1)^(s p(i) q)` times the operator for
`t^(r+s) ⊗ bc`, when `b` has degree `q`. Composition reverses right
products. All natural powers are retained; odd variables are not exterior
variables. Consumers exercise odd and mixed data with nonzero target
shift, finite two-term polynomials, and both signs at exponents one and two.

`CyclotomicAction/IntertwinerSkewAction.lean` now constructs the associative
parity-skew polynomial ring using Mathlib's `SkewPolynomial` and the proved
`coefficientParityAction`. The underlying coefficient map is the sign
endomorphism `φ(c)=(-1)^(p(i)|c|)c`; its multiplicativity and unit law follow
from the existing cyclotomic grading. No action law is assumed.
`sourceRightSkew` and `targetRightSkew` are ring homomorphisms into ordinary
opposite endomorphism rings on the same induced quotients, including the
shifted target. Their multiplication law is reverse composition, and
`rightSkew_Q` proves Q equivariance for every skew polynomial.

Coefficient-first `c X^m` acts as `T^m C_c`. The `*_dotFirst` and
`*_coefficientFirst` theorems prove both order conversions: dot-first
`X^m c` is coefficient-first `φ^m(c) X^m`, with
`φ^m(c)=sgn(m p(i))(c)`. The twist is involutive, so the inverse conversion
uses the same formula. All natural powers remain; odd dots are not exterior.
The consumer checks ring products, Q equivariance, and order/sign conversion
on odd and mixed data with nonzero target shift.

`CyclotomicAction/IntertwinerSupertensorAction.lean` identifies the
scalar-balanced tensor product `k[t_i] ⊗[k] R^Λ(n)` with the parity-skew
polynomial ring. `polynomialTensorSkewEquiv` is a ground-ring-linear
equivalence, sending `t^m ⊗ c` to `φ^m(c) X^m`; its inverse monomial
formula is proved. `polynomialSupertensorSkewRingEquiv` preserves the
transported associative ring multiplication, and
`polynomialSupertensor_mul_tmul` proves the exact Koszul product
`(t^r ⊗ b)(t^s ⊗ c) = (-1)^(s p(i) q) t^(r+s) ⊗ bc` for homogeneous
`b` of parity `q`. The transported unit is `1 ⊗ 1`. The multiplication
and semiring projections are selected explicitly; the ordinary unsigned
tensor-product instances are neither used for this product nor disabled.

`sourceRightSupertensor` and `targetRightSupertensor` transport the ring
representations onto the same quotient carriers, retaining the target shift.
Their pure-tensor formulas recover the dot-first operators, and
`rightSupertensor_Q` proves equivariance for every balanced tensor.
`polynomialSupertensorAlgebra` preserves the existing tensor scalar action,
and `polynomialSupertensorSkewAlgEquiv` bundles the normal-order comparison
as a ground-ring algebra equivalence. Scalar centrality follows from the
linearity of the coefficient parity twist. `qCoefficientScalarTower` proves
compatibility of the ground-ring and affine-algebra scalar actions on the
existing shifted coefficient superspace. Neither quotient is replaced.
`IntertwinerSupertensorScalars.lean` now proves
`sourceRightSupertensor_smul` and `targetRightSupertensor_smul`: both
representations send `r • f` to `r • ρ(f)` in the existing ground-ring
endomorphism modules. Balancing transfers the scalar to the corner as
`algebraMap k B r`; the existing quotient scalar tower identifies this
with its superspace scalar action. No new quotient module is introduced.
The coefficient and skew-polynomial actions satisfy the same scalar law.
`rightSupertensor_scalarQ` gives equivariance for scalar multiples of Q.
The importing consumer checks arbitrary scalars and tensor arguments in
odd and mixed data with nonzero target shifts, and audits every declaration
owned by the scalar-compatibility module against the standard axioms.

Odd and mixed consumers check both signs at exponents one and two,
nonzero target shifts, the algebra-map identity, and definitional agreement
of the algebra scalar action with the original tensor module. This is
the balanced algebra comparison for the right action in KKO I,
arXiv:1206.5933v2, Proposition 8.4, not its complete statement.
`IntertwinerSupertensorGrading.lean` proves that the dot-first monomial
`t^m ⊗ c` with coefficient parity `q` acts with degree `m p(i) + q`.
`polynomialSupertensorPart` is the ground-ring span of these homogeneous
tensors in the existing scalar-balanced tensor product.
`sourceRightSupertensor_parity` and `targetRightSupertensor_parity` extend
the degree statement to every element of this span, including finite sums
and scalar multiples, on the unchanged source and shifted target.
`rightSupertensor_Q_gradedSquare` combines these results with the proved
evenness and equivariance of Q, without additional premises.
The homogeneous spans are not yet bundled as a direct-sum grading.
The right actions use ordinary left-module compatibility; a separate
signed-left condition is not required. The fixed-content restriction is
proved below. A separate tensor comparison over the unital content algebra,
zero-height, full-ELV coefficients and QP remain open.

## Right cyclotomic coefficients and the polynomial variable

`CyclotomicAction/IntertwinerRightCoefficient.lean` descends right
cyclotomic multiplication to the existing source induced quotient and the
shifted `qCoefficient.ract` to the existing target. The descent uses
`InductionAlong.Ind.map`: coefficient right multiplication is proved
left-affine-linear, so the integral balancing relations are preserved.
Both resulting operators remain endomorphisms over the larger affine algebra.
Their unit, product (reverse composition), zero and addition laws are proved.

`qCoefficientInsert_mul` derives right-linearity of the canonical insertion
from its superbimodule homomorphism law, with **no additional sign**.
`rightCoefficient_Q` then proves Q equivariance by its pure-tensor formula.
`sourceRightCoefficient_parity` and `targetRightCoefficient_parity` give the
homogeneous coefficient degree on `qSourceSpace` and `qTargetSpace`.
`sourceRightDot_coefficient` and `targetRightDot_coefficient` prove
`R_t ∘ R_c = (-1)^(p(i)q) R_c ∘ R_t` for a coefficient of degree `q`.
The sign comes from the coefficient parity involution, including on the
shifted target; no square-zero condition on the odd variable is imposed.

This is the right-coefficient and dot/coefficient part of KKO I,
arXiv:1206.5933v2, Proposition 8.4, with the right action setup preceding
Lemma 8.1. The consumer checks all-odd height three and mixed height two,
both with shift one, and uses a concrete odd cyclotomic dot for the grading
and supercommutation hypotheses. These are quotient examples, not nonzero
inversion models. Full polynomial-supertensor action packaging, comparison
with the source's fixed-content corners, full-ELV coefficients and QP remain
open. Finite colours, positive quotient indexing and
`CyclotomicPolynomialParity` are unchanged.

## Graded polynomial-variable square

`CyclotomicAction/IntertwinerDotGrading.lean` proves `sourceRightDot_parity`
and `targetRightDot_parity`: both existing right-dot operators have degree
`D.parity i` on the constructed induced gradings. The proof uses homogeneous
corner products with `affineLastDot_parity` and `affineFirstDot_parity`, and
preservation of coefficient degree by the sign involution. In particular,
the target still uses the parity of its shifted coefficient.

`sourceRightDotLinear` and `targetRightDotLinear` only restrict scalars of
these operators. `rightDot_Q_square` is the existing `targetRightDot_Q`
on the graded carriers. `rightDot_Q_gradedSquare` combines this equality
with Q-evenness and both dot degrees, giving the polynomial-variable
portion of KKO I Proposition 8.4 on these quotients. The imported consumer
checks all-odd height three and mixed height two, both with shift one,
and audits all owned declarations.

These are graded right operators, not signed left-superlinear morphisms.
No square-zero relation for an odd polynomial variable is asserted. Full
right-superalgebra structure, full Proposition 8.4, full-ELV coefficients,
QP and nonzero inversion models remain separate obligations.

## Constructed right dots and Q compatibility

`CyclotomicAction/IntertwinerTargetDot.lean` constructs `targetRightDot`
on the actual prepend-corner induced module with coefficient `qCoefficient`.
It sends `a ⊗ c` to `a x_first ⊗ sgn(p(i))(c)`. The theorem
`targetDotCoefficient_insert`, derived from `Envelope.ζPow_inv_mem` and
`SVec.sgn_comp_of_mem`, proves that on `c = π^η b`, with `η = p(i)p(β)`,
this is exactly `(-1)^η a x_first ⊗ π^η φ_i(b)`. Both factors are present.

`affineFirstDot_twist_comm` derives balance from homogeneous superinterchange.
`contentMove_firstDot` assembles `dot_comp_moveHom` into the signed matrix
identity, respecting reversal of diagram composition by matrix multiplication.
`targetRightDot_Q` proves the equality of actual linear-map composites
`targetRightDot.comp parityCyclotomicContentQ =
parityCyclotomicContentQ.comp sourceRightDot` by balanced-tensor induction.
Neither balance nor the matrix identity is assumed. The imported consumer
checks the equality on all-odd height-three and mixed height-two contents,
both with nonzero coefficient shift, and audits the owned declarations.

Source comparison: KKO I, arXiv:1206.5933v2, (8.13) and Proposition 8.4,
PDF page 42, give precisely this target `t_i` formula and compatibility.
The theorem retains finite colours, content projection, positive quotient
indexing, and `CyclotomicPolynomialParity`. It does **not** establish the
induced tensor super grading, full right-superalgebra action, or full
Proposition 8.4; no QP relation is claimed.

## Source right-dot operator

`CyclotomicAction/IntertwinerRightDot.lean` constructs `sourceRightDot` on
`Ind (CyclotomicAlgebra a n) (appendAlgebra i (n+1))`. It is an ordinary
left `Hn (n+2)`-linear endomorphism with pure-tensor formula
`a ⊗ b ↦ a x_last ⊗ φ_i(b)`. The coefficient involution is the regular
cyclotomic supermodule's `SVec.sgn`; `rightDotCoefficient_of_mem` gives
its homogeneous sign. `affineLastDot_twist_comm` derives balance from
`affineLastDot_comm`, and `rightDotCoefficient_smul` supplies the matching
coefficient twist. There is no assumed balance or assumed intertwining.
Mixed and all-odd consumers use the existing cyclotomic balanced tensor;
the mixed consumer checks the minus sign on odd coefficients.

The source and target right-dot endomorphisms and their Q compatibility are
now constructed as described above. The induced-tensor grading is now supplied
by `IntertwinerGrading`, including Q-evenness; the dot degrees are supplied by
`IntertwinerDotGrading`. The full superbimodule assertion remains open. Finite colours, positive quotient
indexing, and `CyclotomicPolynomialParity` are retained.

## Canonical parity-shifted coefficient target

`CyclotomicAction/IntertwinerParity.lean` refines the target of the existing
`cyclotomicContentQ`. `qCoefficient` is the existing `Envelope.piPow` of the
regular cyclotomic superbimodule, with exponent `p(i)p(β)`;
`qCoefficientInsert_mem` proves the coefficient parity, and
`qCoefficientInsert_smul` proves the actual semilinear coefficient identity.
`qCoefficientTransfer` moves the involution out of the right corner action,
and `parityCyclotomicContentQ` composes this with the already descended map.
`parityCyclotomicContentQ_tmul` retains the actual moving-strand representative.
No new balance hypothesis, flatness assumption, or duplicate parity-shift
interface was introduced. Mixed and all-odd consumers activate a nonzero
shift, use the actual cyclotomic quotient, and audit all owned declarations.

Source-statement comparison: KKO I, arXiv:1206.5933v2, Proposition 8.4 also
requires the induced super grading and signed right `t_i` compatibility.
The latter is now proved by `targetRightDot_Q`; induced grading is now supplied
by `IntertwinerGrading`, while Q-evenness remains open.
Its target right action contains both
`(-1)^{p(i)p(β)}` on the first-dot action and the coefficient involution
`φ_i(b)`; the latter cannot be dropped when balancing across odd coefficients.
The new coefficient grading requires `CyclotomicPolynomialParity`; the old
ungraded map remains unchanged and more general. The `[Fintype I]` scope,
content projection (zero on the other blocks), and positive-height indexing
`CyclotomicAlgebra a n` over `Hn (n+1)` are unchanged. This is not full
Proposition 8.4, not a graded superbimodule-map theorem, and not QP.

## Rectangular mates and the capped pitchfork

`SKM/RouquierMixedMate.lean` defines `rectangularMate` for independent outer
adjunctions and proves its explicit cup–map–cap formula and both naturality
laws. `rouquierMate_postTranspose` identifies the prescribed rightward mate
with the postcomposition transpose; `rouquierMate_pitchfork_cap` then follows
from the Hom-adjunction inverse. Its triangle is the existing right-adjunction
E-strand triangle, not a left zigzag. `rouquierMate_parity` derives homogeneity
without inversion data, and `rouquierMate_cross_interchange` proves the single
odd–odd exchange with coefficient `koszulSign p p` (minus one at odd parity).

The three-adjunction signed expansion is now `rouquierMate_comp_mate`:
`P = koszulSign p p • M(B ≫ A)`, with the final output associator included
in `M`. Its proof transports the existing odd interchange through the even
outer unit and applies the derived capped pitchfork. No exchange or mixed
identity is assumed. Only pure coherence is checked in the underlying-even
bicategory; the odd crossing exchange remains in the supercategory.
`rouquierMate_mixed_braid` derives `C ≫ P = P ≫ D` from the explicitly typed
upward braid and the two rectangular naturality laws. Its coefficient is one
at both parities: the common expansion coefficient is not cancelled or inverted.
The importing consumer exercises both headlines at parity one, including the
minus sign in the expansion, and audits every owned declaration. It retains
the supercategory and adjunctions as parameters; no nonzero inversion model
is constructed.

`SuperRouquierLoc.sig_capCross` now follows by postcomposing the sign-free
mixed braid with the upper left cap, without exchanging that cap.
`sig_capCross_of_neg` computes its crossing component at `h < 0`, with
`h' = h + 2`: it is zero except at `h = -1`, where its coefficient is
`s = koszulSign p p`. `whiskerRight_hom_ext_of_nonpos` extracts equality
from the total augmented inverse equation, and `capCross_eq_of_neg`
assembles the crossing and all dotted-cup components. Writing
`C = L.capL ▷ E₂ ≫ λ.hom` and
`R = α.hom ≫ E₂ ◁ A₂.counit ≫ ρ.hom`, its formula is
`U.capCross = s • (-C + R)` at `h = -1`, and `U.capCross = -C` at
`h < -1`. In particular, the odd boundary is `C - R`; scaling only `R`
would fail the undotted-cup equation. Inputs are the adjacent local data,
both upward square relations, the upward braid, and the height relation.
The proof uses no assumed left zigzag or target cap relation.

The imported `RouquierCapSwap` consumer specializes the boundary to both
parities, applies the theorem to the local data of a `RouquierFamily`
(deriving the height shift and using its square/braid fields), and audits
101 owned declarations. `capL_pitchfork_at_neg_one` derives the left-cap
pitchfork at `h = -1` from the cap swap and the positive inverse; its
coefficient is `s`, with an importing odd-parity consumer.
`capL_pitchfork_below_neg_one` proves the remaining negative-height case,
with coefficient one, by `whiskerLeft_hom_ext_of_nonpos` at upper height
`h+2` and `curlEG_cupD_zero`. Its importing consumer tests arbitrary parity
at height `-2` and all lower heights for a `RouquierFamily`.
`leftAdj_triangle_E_of_neg` now proves the canonical E-strand zigzag is
`𝟙 E₂` for every `h < 0`, including `h = -1`: at the boundary the common
cap-swap sign cancels, and below it the pitchfork reduces to
`curlEG_cupD_self`. `RouquierFamily.leftZigE_of_neg` gives this directly for
`leftZigE`, with the existing `leftCup` and `leftCap`, without rescaling.
The consumer checks arbitrary parity and negative height and the family API.
These remain parametric consumers, not a nonzero odd inversion model.
The positive augmented inverse now gives `cupCross_eq_of_nonneg`, using
all its crossing and dotted-cap components rather than an unsigned duality.
Writing `R = ρ.inv ≫ E₂ ◁ U.cupL`, the cup-side double crossing equals
`-s • R` at `h = 0` and `-R` at `h > 0`. The component calculation
`cupCross_capD_boundary` retains both the crossing/dot interchange sign
and the positive single-curl coefficient. `cupL_pitchfork_of_nonneg`
then has coefficient `s` at zero and one above zero. It assumes the same
adjacent-height relation, both upward squares, and upward braid as the
cap pitchfork; it does not assume left zigzags.

Consequently `leftAdj_triangle_E_of_nonneg` and
`RouquierFamily.leftZigE_of_nonneg` prove the canonical E zigzag is
`s • 𝟙 E₂` for `h ≥ 0`, **not** an unsigned identity at odd parity.
`RouquierFamily.leftZigE_eq` assembles all heights: coefficient one below
zero and `s` at nonnegative height. No cup or cap was rescaled. Importing
consumers check both parities at zero and arbitrary positive height,
the signed cup pitchfork, and the actual family API.

The canonical F triangle and a common normalization remain open. For
`σ = leftAdjParity D i x` and E coefficient `e` just computed, the remaining
compatible F formula is `leftZigF = (koszulSign σ σ * e) • 𝟙 F`.
`RouquierFamily.leftZigzags_iff_leftZigF` now proves that this exact F
formula is equivalent to `LeftZigzags`. The reverse implication constructs
`c = koszulSign σ σ * e` as a unit with inverse itself. For the forward
implication, `SuperAdjunction.smul_id_right_of_left` transfers equality of
scalar multiples of `𝟙 E` to `𝟙 F` using the existing right-adjunction
triangle. It does not assert scalar faithfulness or infer F from E alone.
The named `FNormalizationChecks` consumers check even parity and odd
heights zero and one, and construct `RouquierLeftAdjoints` **conditional
on the exact F equation** via the existing `leftAdjointsOfZigzags`.
The canonical F equation itself, hence unconditional normalized left
adjunctions, is still unproved in Lean at every height.
[SignedFTriangle.md](SignedFTriangle.md) now gives a written mathematical
proof by explicit right-mate reflection, including the signed vertical
composition law, horizontal opposite, comparison of the prescribed mixed
mate, and every field of the mirrored local inversion data. With
`s=(-1)^p` and `q(n)=s^(n(n-1)/2)`, the mirrored crossing is `s M(t)`;
the dotted components and their inverses are scaled by `q(n)`.
The reflected canonical cup and cap have coefficients `a(h+2),b(h)`
whose product is exactly `s^(h+1)=koszulSign σ σ`. Applying the already
proved local E theorem to these mirrored data therefore gives the
canonical F coefficient `s^(h+1)` for `h<0`, and `s^h` for `h≥0`.
The document is not kernel-checked; formalizing the generic mate calculus
and the mirrored local construction remains necessary. No cyclicity,
left adjunction, or scalar faithfulness is assumed in the argument.
No nonzero odd inversion model or full-root certification is claimed.

## Reservoir closure audit

[FusionReservoirLemma.md](FusionReservoirLemma.md) audits the inversion argument
of `NondegeneracyProof.md`. The proposed graded proof gives the correctly typed
closure `cap_s ∘ principalInverseBlock ∘ cup_r` degree `2d_i(r+s+1)`;
bounded-above reservoir grading support then gives joint nilpotence in every
parity and at every height. This is a written argument, not a new Lean theorem.
The draft's ordinary-centre formulation and radical/degree-zero equivalence
need correction. More importantly, nilpotence of these closures does not prove
fused inversion: the augmented factor inverses leave a residual matrix on
positive-height cap rows and negative-height cup columns. The even
`RouqCoproduct.isIso_lift_of_schur` and `schur_const_eq` explicitly retain and
invert this matrix. The all-height super residual matrix and its dotted-window
comparison remain open; §5.4's two-by-two reduction cannot yet be used as a
proved reduction to Lemma β alone.

## Cyclotomic deformation coefficients

`CyclotomicDeformationProof.md` gives proposed written proofs, not new Lean
claims. Arbitrary homogeneous exterior-coefficient cyclotomic polynomials
need not be flat: over `Λ(d,e,f)`, the one-strand relation
`x²−xd+ef=0` forces `def=0`. KKO's permitted even-coefficient deformations
and their odd-cutoff exterior translates have a general freeness argument
from KKO tower projectivity, graded splitting and compatible translation.
The full ELV family must use its relation `d_iχ_(i,m)=0` at even cutoffs;
its coefficient ring is itself not flat over the exterior subalgebra.
Multicolour freeness over the full ELV ring still needs the balanced
deformed projective resolution. Nilpotent lifting of the specified Rouquier
matrix needs only `Tor₁(A/J,target)=0`, but also exact base-change comparison
of its corners, tensor adjunction, signed generators and cup–crossing–cap
mate, and a proof of invertibility of that reduced matrix (A1-map).

## Deformed cyclotomic transport and repeated-odd cancellation

`DeformedProjectiveResolution.md` gives a proposed written proof, not a Lean
theorem, of full ELV polynomial transport through arbitrary multicolour
intertwiner chains. The coefficient sign and dot sign combine to the uniform
polynomial-parity sign. In the first-dot polynomial balanced module this
proves `f(x)τg=f(x)(x²+y²)` by cancelling the monic square difference, not
by assuming cyclotomic freeness. The even-cutoff normalizer defect before
imposing the ELV coefficient relation is exactly `2χ_m d_i`.
The document specifies the twisted balanced K₀, K₁, K₁′ and the global QP
formula. The all-prefix induction, P balance and tensor-map assembly are
still open; no full projectivity or action theorem is claimed. Once those
steps are supplied, the central-square argument gives projectivity over the
preceding block without an A-flatness assumption on that block.

## All-prefix deformed QP calculation

`DeformedGlobalQP.md` gives a proposed written proof of the all-prefix
identity, using the affine pitchfork to put the killed relation at old
position 2 before cancelling the moving square difference. The two
repeated-odd prefix signs cancel; repeated-even strands contribute no
factor. A separate old-generator P balance argument retains total
coefficient parity and the shift `p(i)(N_i+p(β))`. These arguments are
not Lean theorems and still require independent review. The separate
ideal-sum argument is recorded below. The exact projective resolution and
resulting global projectivity remain conditional; the central-monic lemma
is not applied.

## Deformed cyclotomic ideal sum

[DeformedIdealSum.md](DeformedIdealSum.md) gives a proposed written proof of
KKO I Lemma 8.2 for the full ELV coefficient ring. First-strand parabolic
normality, with total coefficient parity and `x₁ ↦ x₁−2d_i`, replaces
centrality. Choosing affine PBW words adapted to the tail parabolic proves
`H F₁ H = Σ_a H F₁ τ₁⋯τ_a`, hence
`(H F₁ H)e(β,i) = H F₁ ι_R(R) + H F₁ τ₁⋯τ_n e(β,i)`.
Both inclusions and all old factors are retained; no cyclotomic flatness
is assumed. This identifies the kernel of the old-to-new quotient map.
Identification with `im P` is conditional on the separately proposed P
balance/descent. A projective `B[s]` resolution additionally requires the
reviewed QP injectivity argument and specified square-right actions and
projective module structures. The proof awaits independent review; no
full action or new Lean theorem is asserted.

## Moving-strand balance on arbitrary Hom entries

`CyclotomicAction/IntertwinerNaturality.lean` proves `hom_comp_moveHom` for
any morphism `f : H(t,t')`, including inhomogeneous morphisms:
`(1_i ⊗ f) ≫ move(t') = move(t) ≫ (twist_(p(i)p(t))(f) ⊗ 1_i)`.
The proof uses the normal-form spanning theorem, not a homogeneity
assumption on `f`. `cl_mem_chainParity` identifies the positioned-word
parity with its actual parity in the presented category. The hypotheses
are only a Cartan superdatum, its scalar system, and a commutative base ring.

`CyclotomicAction/IntertwinerCorners.lean` now assembles these entries in
`Hn`: `contentMove` is the finite sum over words of content β, and
`contentMove_balance` proves
`append(twist_(p(i)p(β))(z)) * G_β = G_β * prepend(z)` for arbitrary
inhomogeneous `z`. The only additional hypothesis is `[Fintype I]` for
the height-algebra colour sums. `prependAlgebra` and
`homMatrixTwistAlgebra` use the existing finite-support Hom coordinates.

`CyclotomicAction/IntertwinerTensor.lean` constructs `contentQ` on the
existing `InductionAlong.Ind` balanced quotient, with formula
`a ⊗ b ↦ a G_β ⊗ b`; no balance/descent hypothesis is assumed.
`cyclotomicContentQ` takes the actual cyclotomic quotient as coefficient
module. The target right action is `prepend ∘ twist_(p(i)p(β))`.
This is an underlying left-module descent, not yet the full Q of
Proposition 8.4: identification with the explicitly parity-shifted
coefficient superbimodule and signed right `t_i` compatibility remain.
The QP identity of Theorem 8.5 remains downstream. No flatness statement
is used. `scripts/NonVacuity/IntertwinerTensor.lean` checks all-odd and
mixed-parity asymmetric data and audits all declarations in both modules.
The consumer `scripts/NonVacuity/IntertwinerNaturality.lean` exercises
arbitrary Hom entries and identity plus an odd dot on an all-odd
asymmetric two-colour datum, and audits the module's axioms.

## Fixed-content restriction of Q

For KKO I, arXiv:1206.5933v2, Proposition 8.4,
`CyclotomicAction/IntertwinerContent.lean` restricts the previously constructed
Q to the right images of the cyclotomic content idempotent. The construction
cuts to content rather than identifying the whole height quotient with it. The source projection is
`x ⊗ b ↦ x append(e_β) ⊗ b`; the shifted target projection is
`x ⊗ πb ↦ x prepend(e_β) ⊗ πb`. Both equalities are proved by balancing
and multiplication on quotient representatives. The corresponding induction
principles show that these cut representatives generate each summand.

`appendContent_mul_contentMove` removes the redundant append idempotent.
`contentCornerQ_tmul` gives `x e(β,i) ⊗ b ↦ x G_β v ⊗ πb`, using
multiplication by `contentMove` and the canonical coefficient insertion. `contentCornerQ_left`,
`contentCornerQ_rightCoefficient` and `contentCornerQ_rightDot` prove the
three module compatibilities on the restricted carriers.
`targetContentRightDot_tmul` retains the sign `(-1)^(p(i)p(β))`, first dot,
and coefficient involution. No module action is transported along a chosen
equivalence; ordinary right multiplication is left-linear, without an extra
signed-left condition.

This establishes restriction and representative generation inside the
height-balanced quotients. It does not yet give a separately defined tensor
over the unital algebra `R(β)` with a two-sided comparison to these summands.
Finite colours, positive quotient height (`n+1`) and polynomial parity remain.
The zero-height formula, full ELV coefficients and QP are still open.

## Global content indices

`GlobalProduct.lean` constructs the full weight supercategory
`globalWeightSpace`, the product of all `GlobalContentModules β` of the
given weight. The pointwise parity decomposition works for arbitrary
products; it does not require finitely many contents. This constructs the
objects of the weight action, not yet its induction and restriction maps.

`GlobalHeight.lean` adds the empty-word algebra and supermodule category to
the tower without altering a positive-height quotient. `heightAppend` is
the vacuum map at zero and the existing quotient inclusion thereafter;
`heightAppend_parity` proves every such inclusion is even.
`GlobalContentModules β` uses height `β.card`, including zero.

`GlobalSupport.lean` retains both parity components on full content
subcategories, with `fullSupercategory`, `fullLiftTrans`,
`globalBlockInduction` and the odd `globalBlockDot`. The dot's homogeneous
parity is the colour parity, and its naturality is the original signed
naturality. These constructions do not discard odd module morphisms.


`GlobalInduction.lean` extends superinduction to every height of the tower,
including the vacuum: `heightSuperInduction` uses the colour-cut bimodule over
`heightAppend`, and `heightSuperInduction_succ` is definitional agreement with
`cyclotomicSuperInduction` at positive height. `heightContentSupported_induction`
moves content `β ↦ {i} + β` at all heights (at zero via `vacuumAppend_content`).
`globalContentInduction (h : {i} + β = δ)` is the superfunctor between global
content categories, composed with the identity transport `heightContentCast`
along `β.card + 1 = δ.card`.

`GlobalRestriction.lean` restricts `cyclotomicSuperRestriction` to content
blocks (`globalBlockRestriction`) and the even unit and counit to
`globalBlockAdjunction : globalBlockInduction ⊣ globalBlockRestriction`; both
components are even (`globalBlockUnit_mem`, `globalBlockCounit_mem`). This is
the positive-height block adjunction; the vacuum unit and counit are open.

`GlobalWeightRestriction.lean` ports `globalF`: `heightSuperRestriction` is the
colour-cut restriction bimodule along `heightAppend` at every height,
definitionally `cyclotomicSuperRestriction` at positive height
(`heightSuperRestriction_succ`), and restriction from one strand to the empty
word uses `vacuumAppend`. `globalContentRestriction (h : {i} + β = δ)` lands in
the vacuum condition `β = 0` at height zero, and
`globalF i h : globalWeightSpace y ⟶ globalWeightSpace x` is the product of
these superfunctors along `blockSucc`, retaining odd morphisms.

`GlobalWeightInduction.lean` ports `globalE`. Each block has at most one
predecessor (`blockSucc_injective`), so the component at `δ` is
`globalContentInduction` from it (`inductionComponent_blockSucc`) and the zero
supermodule otherwise (`inductionComponent_isZero`, `globalZero_isZero`).
`globalE i h : globalWeightSpace x ⟶ globalWeightSpace y` is the resulting
superfunctor.

`GlobalHeightAdjunction.lean` restates the corner pairing, even unit and
counit and both triangle identities along `heightAppend` (they only use a
unital even multiplicative strand map), so the adjunction now also covers the
empty word to one strand. `heightContentAdjunction` restricts it to content
blocks at every height, and `globalContentAdjunction (h : {i} + β = δ)` gives
`globalContentInduction h ⊣ globalContentRestriction h` (composed with the
mutually adjoint transports `heightContentCastAdjunction`).

`GlobalWeightAdjunction.lean` assembles `globalWeightAdjunction :
globalEFunctor ⊣ (globalF).toFunctor` from the blockwise adjunctions,
transported along `inductionComponent_blockSucc`, with zero counit at blocks
without predecessor; unit and counit are even (`globalWeightUnit_mem`,
`globalWeightCounit_mem`). `globalActionAdjunction` packages it as
`SKM.SuperAdjunction (globalActionE i h) (globalActionF i h)` in the `SCat`
target of `ActionSupercategory`, i.e. the `adj` field of `RouquierFamily` on
weight spaces.

`GlobalHeightDot.lean` defines the last dot of the extended tower
(`heightLastDot`; at one strand the image of `affineLastDot` in the
height-one quotient) and restates the signed corner map of `SuperDot` along
`heightAppend`: `heightSuperInductionDot`, homogeneous of parity `|i|`, its
content restriction and `globalContentDot`. `GlobalWeightDot.lean` transports
it along `inductionComponent_blockSucc` to `globalWeightDot`, with
`globalActionDot_mem : globalActionDot i h ∈ parity (globalActionE i h) _ |i|`,
the `dot`/`dot_mem` fields of `RouquierData` on weight spaces.

`GlobalHeightCrossing.lean` defines the last-pair crossing of the extended
tower (`heightLastCrossing`; on two strands the image of
`affineLastCrossing` in the height-two quotient) and restates the two-colour
corner, functor comparison, signed corner crossing and transported crossing
along `heightAppend`: `heightSuperInductionCrossing`, homogeneous of parity
`|i||j|`, now also from the empty word. `GlobalHeightBlockCross.lean` proves
`heightLastCrossing_square` (at two strands from `affineLastCrossing_square`),
`heightSuperInductionCrossing_square`, and restricts the crossing to content
blocks with explicit target content at every height (`heightBlockCross`,
`heightBlockCross_square`). `GlobalWeightCross.lean` identifies two global
content inductions with `heightBlockInduction₂` followed by a height
transport (`globalContentInduction_comp`), and transports `heightBlockCross`
blockwise to `globalWeightCross`; both composites vanish off two-step
successor blocks (`globalEFunctor_comp_isZero`). `globalActionCross_mem` is
the `cross`/`cross_mem` field of `RouquierData` on weight spaces.
`GlobalRouquierData.lean` proves `globalActionCross_square` and assembles
`globalRouquierData Λ : SKM.RouquierData D` in `cyclotomicActionTarget`
(weight-space induction, dot, and the even file's signed crossing
`globalActionSignedCross`: `-ψ` for equal colours, `ψ` otherwise), with
`globalRouquierData_square`; `globalActionAdjunction` supplies `adj`. Open
toward `RouquierFamily`: the braid field on weight spaces (port of
`GlobalBraid`/`GlobalBraidQ` through `blockSucc₃`, using A's `Braid`), the
slides (`GlobalSlides`), nilpotence (needs an odd cyclotomic analogue of
Brundan–Kleshchev Lemma 2.1, absent), and `GlobalLoc` (local inversion is stream A's pending statement).

`GlobalSlideAlgebra.lean` proves the equal-colour dot slides on the last pair of
strands. Locally `x₁ τ - s τ x₂ = 1` and `τ x₁ - s x₂ τ = 1` (`s = (-1)^{|i|}`,
`inductionStrand_slide_left/right`, from relations (1.8) via `Centre.slide_left_eq`);
whiskered by an old word (`induction_slide_left/right`) and summed, in the algebra
`c y₁ - s y₂ c = θ(1)` and `y₁ c - s c y₂ = θ(1)`, where `c` is the last-pair crossing,
`y₁` the appended and `y₂` the new last dot (`affineLastCrossing_slide_left/right`,
and at every height of the extended tower `heightLastCrossing_slide_left/right`).
`GlobalHeightSlides.lean` lifts these to the two inductions: on the equal-colour corner
`T = C θ(1)` signed right multiplication by `y₂` and by `y₁` are superbimodule
endomorphisms (`heightCompositionRightMul`, hypotheses `CornerMulData`); the comparison
`F ≅ T ⊗ -` sends the outer dot to `y₂` and the inner dot to `y₁`
(`heightComparison_dot_outer_app`, `heightComparison_dot_inner_app`), so
`ψ x₁ - s x₂ ψ = s` and `x₁ ψ - s ψ x₂ = s` on components (`heightInduction_slide_left/right`,
diagrammatic order). For the Rouquier crossing `t = -ψ` these are exactly
`SuperRouquierLoc.slide_left/right`; the transport to weight blocks is still open.
`GlobalBraidAlgebra.lean` gives the algebra half of the equal-colour braid: with
`c₁ = φ(c)` the appended crossing and `c₂` the last-pair crossing on three strands of
colour `i`, `c₁ c₂ c₁ = c₂ c₁ c₂` on each word (`induction_braid_same`, positional
`braid_ne`), in the affine algebra and at every height (`heightLastCrossing_braid_same`).
`GlobalHeightBraid.lean` (checked) gives the functor half at every height: the transported
crossing acts on idempotent tensors `e₁ ⊗ e₀ ⊗ w` by left multiplication by the last-pair
crossing (`heightSuperInductionCrossing_idempotent`); equal-parity maps out of three
inductions agreeing on triple idempotent tensors are equal (`heightSuperInduction₃_hom_ext`);
hence, with inner crossing `Ind(t)` and outer crossing `t_{Ind}`,
`outer ≫ inner ≫ outer = inner ≫ outer ≫ inner` (`heightSuperInduction_braid_same`).
The signed Rouquier crossing `-ψ` satisfies the same relation ((-1)³ on both sides).
`GlobalWeightBraid.lean` (checked) transports it to weight spaces: on content blocks the
two crossings are `Ind(t)` and `t_{Ind}` conjugated by height/content casts
(`heightContentBraid`, reduced to the cast-free `heightContentBraidAux`), away from
three-step successor blocks the triple composite vanishes (`globalEFunctor_comp₃_isZero`),
so `t₂ t₁ t₂ = t₁ t₂ t₁` with `t₁ = t ▷ E`, `t₂ = E ◁ t` (`globalActionCross_braid`), and
for `-ψ` (`globalActionSignedCross_braid`, `globalRouquierData_braid`): the `braid` field of
`RouquierFamily` for `globalRouquierData`.
`GlobalWeightSlides.lean` (checked) transports the slides to weight spaces: normalized
height forms `s (ψ x₁) - x₂ ψ = 1`, `s (x₁ ψ) - ψ x₂ = 1`
(`heightInduction_slide_left_one`, `_right_one`), content forms conjugated by casts
(`heightContentSlideLeft/Right`, reduced to the cast-free `…Aux`), and for `t = -ψ`
`E₁ ◁ x₂ ≫ t - s (t ≫ x₁ ▷ E₂) = 1`, `t ≫ E₁ ◁ x₂ - s (x₁ ▷ E₂ ≫ t) = 1`
(`globalActionSignedCross_slide_left/right`): the `slide_left/right` fields of
`SuperRouquierLoc`. `GlobalRouquierFamily.lean` (checked) assembles
`globalRouquierFamily L : SKM.RouquierFamily D` on the weight spaces (`F`, `adj` =
`globalActionAdjunction`, `square`, `braid`, and `loc` via `globalSuperRouquierLoc` with dots,
crossing parity and both slides proved). The only hypothesis is `L`, a family of
`GlobalLocalInversion`: exactly the `invPos`/`invNeg` inverses of the Rouquier mate at each
middle weight. Route for `L` (matrix chain, no projectivity): `DeformedMackeyBoundary.md`,
`DeformedBoundaryDivision.md` ((U2), (L)), `DeformedRouquierMatrix.md` §4,
`DeformedMatrixComparison.md` §4 (window `H_(r,k)`), `DeformedActionAssembly.md` §5; distinct
colours by KKO I Thm 9.1 with deformed (9.3) (`DeformedActionAssembly.md` §2). Note: as stated,
`GlobalLocalInversion` takes an arbitrary `a` with `CyclotomicPolynomialParity` and an unrelated
`Λ`; it is false in that generality (`a i = 1`, `⟨h_i,Λ⟩ = 5`: at the weight with `x₁ = -Λ`
the composites `M`, `N` vanish but the `5` dotted unit columns have nonzero source
`B`, so `invNeg` fails). Discharging it needs `a i` monic of degree `⟨h_i,Λ⟩` (assumed throughout the notes);
`CyclotomicDegreeMatch D a Λ` (checked definition) states this, and `globalRouquierFamily` now
takes it as an explicit hypothesis `_hdeg` beside `L`. The top-row cokernel step
(`DeformedCyclotomicTopRow.md` §4) uses the lower-height ideal sum (`DeformedIdealSum.md`) and
the square resolution (`DeformedSquareResolution.md`), both proposed.
`RouquierMateKernel.lean` (checked): the mate kernel `s = -F̄J` of display (2) of
`DeformedMatrixComparison.md`, `x ⊗ y ↦ -(-1)^{|i||x|} φ₂(x) τ φ₂(y) ⊗ e₂`, as a
superbimodule morphism `B e ⊗_A e B ⟶ e₂C ⊗_C C e₂` of parity `|i|` (`rouquierMateKernel`,
`rouquierMateKernel_parity`, `rouquierMateKernel_apply`); balance over `A` is the Koszul sign of
`J` cancelling that of `heightLastCrossing_intertwines` (`rouquierMateKernel_balance`).
`RouquierCupCapKernel.lean` (checked): the dotted cup `j_m : A ⟶ e B ⊗_B B e`,
`a ↦ x₁^m φ₁(a) ⊗ e` (`rouquierCupKernel`, stated at the same level `n` as the cap; in the
mate at `x₀ → x₁ → x₂` it is applied one height up), and dotted cap `κ_m : B e ⊗_A e B ⟶ B`,
`x ⊗ y ↦ (-1)^{mp|x|} x x₁^m y` (`rouquierCapKernel`), superbimodule morphisms of parity `m p`;
in (2)/(4) of `DeformedMatrixComparison.md`, `u_m = d_m j_m` and `c_m = d_m κ_m`. Input:
`heightAppend_mul_heightLastDot_pow`.
`RouquierKernelComparison.lean` (checked): the height-level identifications. With the dot power
`x^m` on `P = B e` (`heightInductionDotPow`, `y ↦ (-1)^{mp|y|} d_m y x₁^m`,
`heightInductionDotPow_apply`) and `d_m = (-1)^{p(m choose 2)}` (`rouquierDotSign`):
unit then dot power `= d_m (j_m ⊗ M)` (`heightSuperUnit_dotPow`), dot power then counit
`= d_m (κ_m ⊗ M)` (`heightDotPow_superCounit`), and unit at `n + 1`, crossing `ψ`, counit at `n`
on `P ⊗ Q ⊗ M` `= -(s ⊗ M)` (`heightRouquierMate_eq`; for the signed crossing `-ψ` of
`globalRouquierData` this is `s ⊗ M`), all up to unitors/associators.
`GlobalRouquierMateKernel.lean` (checked): the same identifications on content blocks and at
the weight level of `globalRouquierData`. Content level: `heightContentMate` (the content mate
with all height transports is `-(s ⊗ N)`, `contentMateKernel`), `contentUnit_dotPow`
(`= d_m contentCupKernel`), `contentDotPow_counit` (`= d_m contentCapKernel`). Weight level,
at a block `β` and its successor: `globalRouquierMate_app_blockSucc` (the component of the
weight-level `rouquierMate` of the signed crossing is the transported `contentMateKernel`),
`globalActionDotPow_app_blockSucc` (dot powers are transported content dot powers),
`globalDottedCounit_app_blockSucc` (`d_m` times the transported `contentCapKernel`) and
`globalDottedUnit_app` (`d_m contentCupKernel` followed by the canonical object identification),
all up to `eqToHom`s between the transported objects. The monic-degree hypothesis of
`globalRouquierFamily` (`CyclotomicDegreeMatch`) is already on the research branch. Next: the
boundary/division inputs and the window matrix of (2)/(4) in `DeformedMatrixComparison.md`,
fed by these component formulas.
`BoundaryDivision.lean` (checked): the finite monic division of
`DeformedBoundaryDivision.md` §5 in the abstract polynomial window. The window
`⊕_l t^l B` is `ℕ →₀ B` with right coefficients and the semilinear moving dot
`(t^l b) t = t^(l+1) σ(b)` (`tShift`, `tPow`); `skewMul` is the skew product with `b t = t σ(b)`.
Checked: (9) `degLT_sub_tPow`, (10) `degLT_norm_sub_skewMul`, the leading term of `ψ ⋆ S`
(`skewMul_top`), the monic quotient (11) ⇒ (12) (`monic_quotient`, `σ` injective) and
`boundary_division`: from the recurrence (8) `deg(φ_(k+1) − φ_k t) < 1`, the norm identity (7)
`Σ_(j ≤ D) φ_(k+j) b_j = c F t^k` with `S` monic of degree `D`, `F` monic of degree `N = a + D`
and `c` a `σ`-fixed unit, `φ_k = 0` if `N + k < D` and `c⁻¹ φ_k` is monic of degree `N + k − D`
otherwise. Any ring `B` (no commutativity, zero divisors allowed). Non-vacuity:
`scripts/NonVacuity/BoundaryDivision.lean`.
`BoundaryWindow.lean` (checked): the window matrix of (2)/(4) in the same abstract window.
`windowMap φ` is `A_∂ : Σ_k w_k b_k ↦ Σ_k φ_k b_k`; `LeadsAt φ c a` says `φ_k` has leading
coefficient `c` in degree `a + k` (`leadsAt_of_monicDeg` converts the output of
`boundary_division`). `a ≥ 0`: `windowMap_add_low_existsUnique` (every `p` is uniquely
`A_∂ w + r`, `deg r < a`; display (2) bijective). `a = −m < 0` (`φ_k = 0` for `k < m`,
`φ_(m+j)` leading `c` in degree `j`): `windowMap_surjective`, kernel `windowMap_eq_zero_iff`
(`= ⊕_(k<m) w_k B`), cap rows `capRow σ φ r v = A_∂(v t^(r+1))(0)` with
`capRow_single` (`= φ_(k+r+1)(0) σ^(r+1)(b)`) and `capRow_antidiagonal`, and
`windowMap_cap_existsUnique` (for `σ` bijective, `v ↦ (A_∂ v, (G_r v)_(r<m))` is bijective;
display (4)). Non-vacuity: `scripts/NonVacuity/BoundaryWindow.lean`. Next: the concrete
boundary: identify `A_∂(w_k)` of the transported `contentCupKernel`/`contentCapKernel` with such
a `φ`, the recurrence (8) and the norm (7) with the cyclotomic polynomial `a_i`, and the cap rows
of (4) with `capRow`.
`BoundaryAssembly.lean` (checked): the abstract half of `DeformedMackeyBoundary.md` §3 and
`DeformedBoundaryDivision.md` §§4–5. `MackeyBoundary σ L₁ L₀ L₀'` records, as additive maps,
`P` with `P ρ = R_t P`, the direct decomposition `L₀ = F(L₀') ⊕ j(V₀)` with the dot slides
`F(u) t = F(X u) + j(E u)` and `j(f) t = j(f t)`, the extraction `B₁` in corrected coordinates
(`B₁ ρ = ρ̄ B₁`, surjective), and a right-linear boundary `A` with `P z ∈ F(L₀') + j(A(B₁ z))`.
Checked: `recurrence` (8) for `φ_k = A(w_k)`, `A_eq_windowMap`, `norm` (7) for every `k` from
one lift `z₀` of `S(ρ̄) w₀` with `P z₀ = j(c F)` (`σ`-fixed `S`, `c`), `division` (12), and
the window displays `window_pos` ((2), `D ≤ N`) and `window_neg` ((4), `N < D`, `σ` bijective).
Non-vacuity: `scripts/NonVacuity/BoundaryAssembly.lean`. Open (the concrete fields of
`MackeyBoundary` for the global cyclotomic factors): the affine Mackey PBW decomposition after
tensoring with the cyclotomic quotient (`direct`, `Rt_F`, `Rt_j`), the short-coset extraction
(`B₁`, `B₁_ρ`, `B₁_surjective`, `P_split`), `P ρ = R_t P`, and the reverse norm identity (5)
giving `hz₀`; then the cap rows of (4) against `contentCapKernel`.
`BoundaryCosets.lean` (checked): `B₁` and `A_∂` derived from the short-coset decomposition of
`DeformedMackeyBoundary.md` §§2–3. `MackeyCosets σ L₁ L₀ L₀'` keeps `P`, `ρ`, `R_t`, `F`, `j`,
`X`, `E` with `P_ρ`, `Rt_F`, `Rt_j`, `direct`, adds `span` (`L₀ = F(L₀') + j(V₀)`), a short
subgroup `L₁'` with `ρ(L₁') ⊆ L₁'` and `C₀ P(L₁') = 0` (`P_short`: `P(L₁') ⊆ F(L₀')`), a lift
`ℓ : V₁ → L₁` covering `L₁` mod `L₁'`, independent mod `L₁'`, with `ρ ℓ ≡ ℓ ρ̄` and
`ℓ(v b) ≡ ℓ(v) b` mod `L₁'`, and right `B`-actions with `P`, `j` right linear and `F(L₀')`
stable. Checked: `C₀`, `B₁` (coordinate mod `L₁'`, `B₁_ℓ`), `A = C₀ P ℓ`, `B₁_ρ`, `P_split`,
`A_rsmul`, `toMackeyBoundary`, and `norm_of_short`, `window_pos_of_short`,
`window_neg_of_short`, where the norm lift is only needed modulo `L₁'` (`z₀ ≡ ℓ(S)`).
Non-vacuity: `scripts/NonVacuity/BoundaryCosets.lean`. Interface notes for the concrete
instance (checked against the written argument, Lean global factors: `k` purely even, so the
odd deformation parameters vanish, `ρ = ±x₁ ⊗ φ` and `w_k = v_k`): (i) `direct` forces `j`
injective, so `B` must be the content-`β` corner of the cyclotomic quotient (with `σ`
restricted to it), not the whole `heightAlgebra n`; with the whole algebra `e_R ⊗ b` kills the
other content blocks. Correspondingly `L₁ = e_R K₁` and `L₀ = e_R H e_R ⊗ B`. (ii) `F(L₀')` is
the left-oriented crossing summand `ι(R) τ_n ι(R)`; the right-oriented prepend coordinates of
`PrependCoordinates.md` (`qPrependTensorEquiv`) give a different polynomial component with
`E = 0`, which does not match the cap rows `[F̄; E; EX; …]`, so the append-side Mackey
decomposition is needed. (iii) No error was found in the written steps for `C₀ P(L₁') = 0`,
`B₁ ρ = ρ̄ B₁`, the extraction (6) (sign `(−1)^m`, factor `S = ∏(t^(1+p) − x_b^(1+p))²`), the
reverse norm (5) (from `qpIdentity`, dot transport, `G J_L ⊆ J_L`, `J_R G ⊆ J_L`,
`J_L G' ⊆ J_R` and injectivity of right multiplication by `K = G G'`), or the degree count
`deg F − deg S = ⟨h_i, Λ − β⟩`. Open: the concrete `MackeyCosets` fields (construct `P`;
the append-side Mackey decomposition after the cyclotomic quotient; `K`-injectivity).
`ReverseNorm.lean` (checked): the ring-theoretic part of `DeformedBoundaryDivision.md` §§2–3,
with `J_L`, `J_R` left ideals (`Submodule H H`). `injective_of_leading`: an additive map on
`ℕ →₀ V` raising moving degree by `d` with injective top coefficient is injective (the
"largest moving exponent cannot disappear" step for `K = G G'`). `mem_of_mul_mem_of_injective`:
injectivity of `· G G'` mod `J_R` and `J_L G' ⊆ J_R` give `h G ∈ J_L → h ∈ J_R`.
`reverse_norm`: (3) `f T G ≡ f L_left (mod J_L)` and (4) `G f = ε f' G`, `G L_left = L G` give
(5) `G f T ≡ ε f' L (mod J_R)`. Non-vacuity: `scripts/NonVacuity/ReverseNorm.lean`. Open for the
concrete (5): the inputs `J_L G' ⊆ J_R` (reverse chain transport), the right-oriented PBW
expansion of `K` with unit leading coefficient (feeding `injective_of_leading`), and (3), (4)
from `qpIdentity` and intertwiner dot transport.
Stream H restart point: (a) slides: done (above); (b) braid functor half: a three-fold corner `C θ₃(1)` with comparison
`Ind ⋙ Ind ⋙ Ind ≅ T₃ ⊗ -` (copy `heightInductionFunctorComparison`), carrying
`heightLastCrossing_braid_same` to components, then blocks; (c) `GlobalNilpotent` needs
an odd algebra-level BK Lemma 2.1 (none exists in odd-lean yet); not started.

`GlobalCross.lean` defines two-step block induction `globalBlockInduction₂`
with explicit target content and restricts the constructed crossing
`cyclotomicSuperInductionCrossing` (`globalBlockCross`, parity `|i||j|`).
`globalBlockSignedCross` is the Rouquier convention of the even file (`-ψ` for
equal colours). `cyclotomicSuperInductionCrossing_square` transports
`compositionSuperCrossing_square` through the comparison isomorphism, giving
`globalBlockCross_square` and `globalBlockSignedCross_square`, the shape of the
`square` field of `RouquierFamily`. Distinct-colour squares, dot slides and
braids are not yet transported to blocks.

`CyclotomicAction/Global.lean` supplies the content indices and boundary sign
for the global cyclotomic action: `WeightBlocks`, injective `blockSucc`, its
subsingleton fibres, `exists_blockSucc_iff`, `blockSucc_comm`,
`blockLoc_weight`, and `pair_nonpos_of_not_mem`. The convention is
`weight(β) = sum β - Λ`. Empty content is retained. `blockWeight_not_card`
shows why positive-height categories alone do not give weight spaces: already
the singleton contents of two distinct simple roots have different weights.
This ports the index layer, not yet the global superfunctors. Concrete content
projectors and induction support are in `ContentBlocks` and `ContentSupport`.


Branch `research/odd-nondegeneracy`. Rules for this branch: `AGENTS.md`, "Workflow and
evidence". This file is updated in the same push as the results it describes. Status
words: *Lean* means compiled on this branch and covered by full CI; *proposed* means a
written argument in `docs/Nondegeneracy/` that is not checked; *open* means neither.

Target: [BE2] §8 Nondegeneracy Conjecture (`SKM.NondegeneracyConjecture`), i.e.
injectivity of `MatchingBasisChoice.expansion` over the abstract `SYM` (polynomial even
generators, exterior odd generators), for odd and mixed data. No unconditional full nondegeneracy
theorem is claimed. B0 is complete: `nondegeneracy_of_upward_independence` derives
the conjecture from upward independence at every weight; the latter remains open.

Scope: compatible symmetrizable Cartan superdata with finitely many colours and homogeneous
scalars, over a field, followed by integral descent as in the even case. Nonsymmetrizable data
and nonhomogeneous scalars are outside the target.

Route: the super analogue of Webster's proof of the even case (formalized in
categorification-lean): deformed cyclotomic super actions with ELV odd parameters at highest and
lowest weight, the family `Hom(T(-μ₊), W(μ₋))` reaching every weight `μ₋ - μ₊`, detection of the
upward part and of bubble products there, and the reduction of the conjecture to upward
independence. Proposed theorem graph: [GeneralRoute.md](GeneralRoute.md). The product-datum Hom family
must still be fused to the original superdatum. The exact test in
`scripts/Nondegeneracy/nilpotent_hom_fusion.py` refutes zero/zero fusion with
inherited blockwise dots: the necessary odd crossing equation has coefficient
rank 32 and augmented rank 33. The separated zero/nonzero alternative remains
proposed and retains all odd coefficients in one connected reservoir, not in
the invertible probe; its all-content categorical inversion is still open.

`separated_fusion_relations.py` checks zero/nonzero cross-polynomial units in
all colour-parity combinations, including a nonsemisimple probe. Its adjacent
odd affine A1 test includes one reservoir i strand, one probe i strand and one
reservoir j strand: all six labelled shuffles satisfy the two-strand relations
and the two nonzero repeated-colour braid corrections. Both independent
reservoir exterior generators survive. This is an affine corner test, not an
induction/restriction construction or an all-content inversion theorem.
[SeparatedFusion](SeparatedFusion.md) gives the proposed local denominator
argument, the conditional all-height Schur argument and an explicit Lean plan.
The categorical multicolour Hom-sector comparisons and their actual mate
coordinates remain open; no all-content A2 theorem is claimed.
`commute_inverse_square_difference` and `separated_diagonal_crossing` prove
in Lean that `(x-y)/(x²-y²)` has both odd dot slides and square
`(x²+y²)/(x²-y²)²`. The smallest actual nonvacuum rank-one mate was rechecked:
its 72-by-72 matrix has determinant one, with square-zero feedback of rank four.
`klr_cyclotomic.py` builds verified two-colour KKO cyclotomic quotients from
the presentation. `rouq_sig_multicolour_check.py` runs the separated mate checks
on them; partial results are in SeparatedFusion §7. Mutation controls are not
done, so these results are not evidence about crossing data.
[NondegeneracyProof](NondegeneracyProof.md) records the proposed proof with a
status for each step. The claimed reduction of fused inversion to reservoir
closure nilpotence alone has been withdrawn: the all-height residual
identity-summand matrix and its dotted-window comparison remain open.

## Super Rouquier interface

The named projection obligation is
`OddMath.SKM.SuperRouquierLoc.MateProjectionFormula`, in
`OddMath/SKM/RouquierMateProjection.lean`. It equates the two sector projections
of the normalized cup–crossing–cap mate `-q • rouquierMate` with
`C = Σ_r q^r u_{A,r} v_{B,-r-1}` and
`D = -Σ_r q^(r+1) u_{B,-r-1} v_{A,r}`. It is a **Prop definition, not a theorem**.
The inclusions, projections, dotted factor maps and finite nilpotence bounds
are explicit arguments; their content-shifted Hom realization is still open.
The odd specialization uses the raw mate, whereas the even specialization
uses its negative, matching the normalized slide in SeparatedFactorInversion.
`NonVacuity/MateProjectionFormula.lean` checks both parity specializations.
This interface assumes neither an inversion nor a proof of A2.

`OddMath/SKM/RouquierHomContent.lean` defines `contentParity`,
`homContentShift`, the original-weight category `homWeightSector`, and the
content-shifted `homContentPostE`/`homContentPostF` with
`homContentPostAdjunction`. The shift is `p(i) P(β₊)`; its change across a
reservoir `j` edge is `p(i)p(j)` (`homContentShift_add_single`). The Π-action
is the full superfunctor action, and its self-adjunction is derived from the
even Π² comparison. `scripts/NonVacuity/HomContentShift.lean` consumes this
adjunction in the integral parity envelope and checks the nontrivial sign on
its odd comparison map. Finite content is retained separately from weight.
The raising precomposition functor `homContentPreE` has the correct negative
factor weight indices. Its right adjoint comes from the factor's left
adjunction, not from the given right adjunction (see below).

`OddMath/SKM/RouquierShiftedAdjunction.lean` defines
`ShiftedSuperAdjunction F E σ`: a left adjunction `F ⊣ E` whose cup and cap have
parity `σ`. The zigzag on `F` is the identity and the zigzag on `E` is `(-1)^σ`
(the sign of BE Proposition 6.2, (6.6)). `homPreShiftAdjunction` proves
`homPre E ⋙ S ⊣ homPre F` on the full Hom supercategories for any parity-`σ`
shift `S` with a supernatural comparison (`ParityShiftDatum`). The odd sign of
the `E`-zigzag cancels exactly against the super interchange of the cap with
the odd comparison `ζ`. `homContentPreAdjunction` then gives
`homContentPreE ⊣ homContentPreF`, where the lowering precomposition is
shifted by `leftAdjParity D i = p(i)(h_i+1)`, constant along the edge
(`leftAdjParity_edge`). Its input is `RouquierLeftAdjoints T`, the factor's
shifted left adjunctions. `OddMath/SKM/RouquierLeftCupCap.lean` defines the
leftward crossing, cups and caps from the local inverses (`sigL`, `cupN`,
`capN`, `cupL`, `capL`, as in `RouqSl2`), proves they have parity
`p(i)(h_i+1)`, and packages `RouquierFamily.leftCup`/`leftCap`. The super
analogue of Brundan Theorem 4.3 is the named Prop
`RouquierFamily.LeftZigzags`: both zigzags of the leftward cup/cap equal `c`
and `(-1)^σ c` for a unit `c`. It is stated up to `c`, so it does not depend
on a sign normalization; super interchange of the cup with itself forces the
ratio `(-1)^σ` whenever the cup is nonzero. `leftAdjointsOfZigzags` turns it
into `RouquierLeftAdjoints`. `RouquierInverseRelations.lean` ports Brundan
Lemma 3.1 ((3.3), (3.5)–(3.9)): the sign-free inverse-matrix relations among
`sig`, `sigL`, dotted cups/caps, and the bubble values `ccw_self`, `cw_self`.
`RouquierDotSlide.lean` proves the signed iterated dot slide
`powComp_sig`: `X^m σ = s^m σ Y^m - ∑_{j<m} s^(m-j) capD_j cupD_(m-1-j)` with
`s = (-1)^p`, Brundan (3.14) (`cupL_powComp_sig`) and both expansions (3.18).
It also proves the infinite Grassmannian relation for `h ≥ 0` with signs
(`infGrass_nonneg`):
`∑_{j<m} s^(m-j) P_j Q_(m-1-j) + s^m P_(-1) Q_m + ∑_{n≤h} P_(m+n) Q_(-n-1) = 0`.
`infGrass_nonpos` is the `h ≤ 0` case, proved directly without a dual:
`∑_{j<m} s^(m-j) P_j Q_(m-1-j) + P_m Q_(-1) + s^m ∑_{n≤-h} P_(-n-1) Q_(m+n) = 0`.
At every weight the term `P_r Q_(m-1-r)` therefore carries `s^(m-r')`, with
`r'` the clamp of `r` to `[0,m]`. This is a candidate sign normalization for
the super fake bubbles. `RouquierCurl.lean` ports the curl calculus:
`curlG`/`curlEG` (closing the left/right strand of a two-strand map), with
atoms on the closed strand absorbed into the cup or cap without sign and atoms
on the open strand leaving with the Koszul sign of the cup or cap they pass.
It proves the pitchforks `sig_counit_pitchfork`, `unit_sig_pitchfork` (no
sign), Brundan Lemma 4.1 (`curlG_dotted`, `curlEG_dotted`) and the boundary
self-curls: `curlG cupL (capD h) t = -ε` with `ε = 1` at `h = 0` and
`ε = s` for `h > 0` (`curlG_capD_self`), and `curlEG (cupD (-h)) capL t = 1`
for `h ≤ 0` (`curlEG_cupD_self`). The `h ≤ 0` statements are proved directly,
without a dual. `RouquierPitchfork.lean` adds two direct inputs for the
leftward pitchfork calculation: `curlEG_cupD_zero` proves vanishing with
`n < -h` dots on the cup, and `curlEG_double_dotted` proves, for `0 < n ≤ 1-h`
and `t ≫ t = 0`, that the closed double crossing `t ≫ x₁^n ▷ E₂ ≫ t` is zero
below the boundary and `-s^n • 𝟙 E₁` at the boundary. Its ordered expansion is
`powComp_right_tau`; no mirror is used. The same module now defines `capCross`
and proves `unit_capCross_zero`, `dottedUnit_capCross`, and
`dottedUnit_capCross_boundary`. Moving `n` dots past the rightward crossing
contributes `s^n`; multiplied by the double-curl boundary `-s^n`, this gives
`-𝟙` in both parities. Thus the dotted-cup component of the cap-swap is
proved, including undotted vanishing. The low capped-crossing expansion is now
proved by `sig_capL_low`: for `h ≤ 1`, it is `capD 0 ≫ cw (-1)` plus `capD 1`
exactly at `h = 1`, in either parity. `sig_capD_closed` and
`cross_sig_capD_closed` retain the factor `koszulSign p (n*p)` from moving the
open-strand dot power past the rightward crossing. For a square-zero upward
crossing, `cross_sig_capD_zero` vanishes and `cross_sig_capD_one` is `s` times
the undotted right-cap pitchfork, where `s = (-1)^p`. The upward sandwich
`tau_dot_tau_left` itself has coefficient one; the factor `s` comes from
interchange. The mixed braid and full negative-height cap swap are now proved
as recorded above, together with both negative-height cap-pitchfork cases and
the canonical negative-height E triangle. Brundan Lemma 4.2, (4.5)–(4.7),
supplies the decomposition followed. BE Proposition 7.2's full pitchforks use
(6.6), so they cannot be imported as independent inputs to the missing
adjunction triangles.
The odd- and even-parity specializations in `NonVacuity/Pitchfork.lean` assume
local Rouquier data: they are signature and axiom checks, not a constructed
nonzero categorical example. No existing concrete instantiation of the local
inversion data has been supplied here; the cyclotomic global local-inversion
comparison remains open. The canonical E-zigzag scalar is now determined
at every height, as recorded above. **Open:** proving `LeftZigzags` by
establishing the F-zigzag through a mirror into a super horizontal opposite
`HOpS B`. That opposite is a 2-supercategory with the same Koszul signs. A
first analysis found that right mates are anti-multiplicative *with* a sign:
`mate (x ≫ y) = koszulSign |x| |y| • (mate y ≫ mate x)`. Consequently
`mate (x^n) = s^(n choose 2) • (mate x)^n`, and the mirror crossing must be
`s •` (full mate of `t`). The mirror's rightward crossing is then
`s • sig`, its dotted caps and cups are `s^(n choose 2) •` L's, and its
`sigL`, `cupL`, `capL` agree with L's only up to explicit signs, not by `rfl`.
Signed anticomposition, powers, and the dotted-cap comparison are now checked
in `RouquierRightTranspose`. The remaining reflected-data comparisons have
not been checked in Lean; their precise coefficients are in `SignedFTriangle.md`. The
nilHecke square and braid transfer to the mirror. Suggested construction: the
mirror crossing is `(homMateEquiv A₁.hop A₂.hop _ _).symm (s • sig)`, and
mate injectivity comes from `recover (φ ▷ E ≫ counit) = φ`. The next even inputs
are the fake-bubble identities, the inverse-cup
expansions (3.12)–(3.13) (`RouqCurl`), the dotted curls (`RouqDottedCurls`),
pitchforks and `RouqTriangleE`. The dual statements need a super horizontal
opposite with Koszul signs (`RouqLoc.dual`, `RouqLoc.mirror`), which does not
exist yet. The even proof is
`RouqLoc.leftAdjunction` via `RouqPitchfork`, `RouqTriangleE`,
`RouqAdjunction`, `RouqCurl`, `RouqDottedCurls`, `RouqGrass` and
`FakeBubbles` in categorification-lean, about 2500 lines. The
original-datum rational crossings must also be constructed before these
sectors can be assembled into A2. `scripts/NonVacuity/ShiftedAdjunction.lean`
checks the odd comparison on the integral parity envelope and the odd
leftward parity. For the Hom adjunction it is only a signature check.

`OddMath/SKM/RouquierHomContentCoherence.lean` supplies `homParityShiftAdd`,
`homParityShiftCommute` and its compatibility with homogeneous supernatural
transformations. `homContentPostOutAdjunction` puts both postcomposition
adjoints in the output-shift convention via the even β comparison.
`homParityShiftCommute_pi` retains the negative Π self-interchange; the
integral parity-envelope fixture proves that this comparison is not the
identity (`scripts/NonVacuity/HomContentCoherence.lean`). These parity-shift
comparisons are not the missing original-datum multicolour KLR relations.

`OddMath/SKM/RouquierMateSlide.lean` proves
`rouquierMate_normalized_slide`: multiplying the raw cup–crossing–cap mate
by `-q` gives the normalized dot slide, directly from the upward relation.
`mate_slide_projection` then projects this ordered relation along specified
dot-intertwining sector maps. Neither theorem assumes an inverse.
`scripts/NonVacuity/MateSlide.lean` checks the projection on a noncommutative
integral matrix fixture. The construction of the required sector intertwining
maps, not the scalar normalization, remains open.

`OddMath/SKM/RouquierMateSeries.lean` proves the signed ordered finite
expansions `mate_series_probe_source` and `mate_series_probe_target`.
They invert only the probe dot; nilpotence of the reservoir dot kills the
tail. The first expansion has coefficients `q^r`, and the second has
coefficients `-q^(r+1)`, without any exchange of factors. The four integral
matrix fixtures in `scripts/NonVacuity/MateSeries.lean` check both expansions
for both signs with a nonzero square-zero reservoir dot and a coefficient
not commuting with that dot. These are algebraic series tests, not a proof
that the categorical sector coordinates have been constructed.

`OddMath/SKM/RouquierMateCoordinates.lean` proves
`SuperRouquierLoc.MateProjectionFormula.of_coordinates`. It starts from the
upward slide and the cup–crossing–cap composite, uses the two projected
slides, and derives the named projection predicate from explicitly listed
sector dot intertwiners, cap–cup factorizations, ordered power coordinates,
probe-dot inverses and reservoir nilpotence bounds. In particular it does
not assume the projection predicate or any inverse of the coupled mate.
The signature/axiom check is `scripts/NonVacuity/MateCoordinates.lean`;
this check is not a nonvacuum categorical example. The categorical content
of the listed coordinate hypotheses remains open, so this conditional
reduction does not close A2 or supply its all-height negative windows.

`OddMath/SKM/RouquierMateSectors.lean` proves
`SuperRouquierLoc.MateProjectionFormula.of_sectors`. Source sectors
(`SourceSector`: summands `E₁ₛ, F₁ₛ` with even inclusions, a sector
adjunction to which the coupled counit restricts, and a sector dot) and
target sectors (`TargetSector`: projections, unit and dot) realize all
intertwiners, cap–cup factorizations and ordered power coordinates of
`of_coordinates`. The coordinates are the actual dotted sector cups and caps,
with negative indices given by powers of the inverse probe dot (`probeCup`,
`probeCap`). The remaining hypotheses are exactly: the upward slide of the
coupled crossing, inverses of the two probe dots, and nilpotence of the two
reservoir dots. No biproduct completeness of the sectors and no inverse of the
coupled mate are used. Still open: constructing the coupled raising functor of
the Hom family with its post/pre sectors and coupled crossing (needs
`RouquierLeftAdjoints` and the original-datum rational crossing), and proving
its slide. `scripts/NonVacuity/MateSectors.lean` is a signature/axiom check with
self-sector evaluations.

`OddMath/SKM/RouquierFeedbackIdeal.lean` proves whole-matrix nilpotence from
a vanishing multiplicative filtration of two-sided coefficient ideals.
`FeedbackIdealFiltration.matrix_pow_mem` controls all entries of every
power, and `isUnit_of_feedback_filtration` feeds the resulting nilpotence
into `isUnit_of_nilpotent_feedback`. Its concrete integral residue-ring
fixture has nonzero square-zero feedback and noncommuting off-diagonal
blocks (`scripts/NonVacuity/FeedbackIdeal.lean`). Construction of the
categorical closed-coefficient filtration and feedback membership is still
open. [HomSectorCoordinates](HomSectorCoordinates.md) specifies the exact
remaining adjunction, original-datum coherence and coordinate obligations.

`OddMath/SKM/RouquierDotConjugation.lean` proves
`mate_dot_conjugation_source` and `mate_dot_conjugation_target` at arbitrary
length, retaining the finite ordered cap–cup correction terms of
SeparatedFactorInversion (3)–(4). No nilpotence is needed for these identities.
`scripts/NonVacuity/DotConjugation.lean` consumes them at all lengths on
noncommuting integral shear dots, with nonzero corrections for both signs.
Their identification with the categorical negative windows remains open;
these are not assertions that the uncorrected windows are invertible.

`OddMath/SKM/RouquierData.lean` defines `RouquierData`, `RouquierFamily`,
`SuperAdjunction`, `SuperRouquierLoc`, and the homogeneous matrix interfaces
`SuperSumInvTo`/`SuperSumInvFrom`. The ambient `TwoSupercategory` retains
super-interchange; it is not an ordinary bicategory. The common inverse
component has parity `|i|`, and dotted identity component `n` has parity
`n |i|`; these are the explicit parity shifts of the formal direct sums.
`rouquierMate` is the ordered cup–crossing–cap composite. `boundaryPos_eq`
and `boundaryNeg_eq` consume its inverse to obtain the normalized Kronecker
window. These declarations pass the scoped warning-free build; full CI
remains the branch-wide verification gate.

`OddMath/SKM/RouquierHom.lean` constructs the linear parity-preserving
`homPre`/`homPost` functors on full Hom supercategories, their homogeneous
`SuperNatTrans` transformations, and `homSectorInterchange`. Its
`homSector_exchange` theorem retains the Koszul sign for opposite-sector
transformations; two odd transformations anticommute. This is the Hom-sector
generator layer, not multicolour affine coherence or categorical fusion.

`OddMath/SKM/RouquierHomAdjunction.lean` proves `homPostAdjunction` and
`homPreAdjunction`, including both triangles and evenness of all unit/counit
components. Precomposition reverses the two adjoints. The proof uses the even
underlying bicategory only for triangle coherence; the functors and naturality
remain on the full Hom supercategories. Content-dependent parity-shifted
comparisons and the coupled affine action remain to be constructed.

`OddMath/SKM/RouquierBoundary.lean` adds the actual finite dotted-unit
`RouquierBoundary.Coefficients`. `Coefficients.ofVacuumInverse` extracts it
from negative local inversion when the common summand vanishes.
`Coefficients.cap_mem`, `cup_cap`, and `hom_ext` prove the cap parity,
normalized top-coefficient pairing, and boundary detection. The cutoff-two
odd example has an odd cap; no unshifted opposite adjunction is inferred.

`OddMath/SKM/RouquierMate.lean` identifies the ordered `rouquierMate` with
`homMateEquiv`, proves both strand naturality laws, and derives
`rouquierMate_slide` from the upward dot slide without any inversion
hypothesis. Its interface consumer is `SuperRouquierLoc.mate_slide`:
`σ ≫ (x₂ ▷ F₂) - q • ((F₁ ◁ x₁) ≫ σ) = ε₁ ≫ η₂`.
The proof retains odd crossings; only the even prefix and suffix use ordinary
coherence. This is the unprojected categorical recurrence. Identifying its
sector projections with both ordered finite formulas is still missing.

`OddMath/SKM/RouquierSchur.lean` supplies associative block factorization,
`isUnit_of_schur`, and `isUnit_of_nilpotent_feedback`. Nilpotence concerns
the whole feedback operator. This removes the need for a commutative
coefficient determinant in the algebraic lifting step, but does not identify
the actual fused mate or its feedback. A2 remains open at the super analogue
of `RouqCoproduct.rouqSig_eq`, followed by the all-content negative-window and
nilpotent-ideal comparison; see SeparatedFusion §7. No separated-fusion
counterexample is asserted, and no fused inversion is assumed to prove A2.

This is the factor-action interface, including same-colour square, braid,
and local inversion. Multicolour affine relations and distinct-colour mixed
inversion are separate obligations. In particular no construction of a
fused action or theorem A2 is asserted. Detection still requires the bubble
normalization outside the finite inverse window and its comparison with the
connected reservoir coefficients.

## One-strand cyclotomic algebra coordinates

`QuiverHecke/CyclotomicAbsentColour.lean` proves `singlePolynomialEquiv` for
the existing quiver Hecke one-strand endomorphism algebra, including odd
colours. `singleCyclotomicEquiv` identifies its polynomial-ideal quotient
with `AdjoinRoot`; `singleCyclotomicFinEquiv_apply` gives the monic finite
coordinate map as the sum of scalar multiples of descended dot powers.
These are underlying-algebra results over any commutative ring. A super
quotient requires homogeneous polynomials. The superfunctors and adjunction
are constructed below; KKO local inversion remains open.
[ActionLeanPlan.md](ActionLeanPlan.md) places exterior ELV coefficients after
the even-parameter action theorem, and targets the existing
`SKM.SuperRouquierLoc` rather than a second local-data interface.

`QuiverHecke/CyclotomicAction/Quotient.lean` equips the existing finite-support
Hom algebra with a unit for finitely many colours, defines its genuine
two-sided first-dot polynomial ideal, and constructs `CyclotomicAlgebra` and
`cyclotomicMk` at every positive strand number. `cyclotomicMk_generator`
proves that the defining cyclotomic polynomials vanish. This supplies the
underlying quotient algebra; its homogeneous grading is supplied below.
The projectivity and Mackey statements needed for inversion remain open.

`CyclotomicAction/Induction.lean` constructs `appendAlgebra` by actual right
whiskering of affine Hom entries, proves `appendAlgebra_mem_ideal`, and
obtains the descended nonunital algebra map `cyclotomicAppend`. The associated
`cyclotomicInduction` is a genuine induction functor on underlying modules.
These inclusions run from height `n+1` to height `n+2`; the vacuum map remains
separate. The supermodule enhancement is given below. No ordinary
naturality claim is made for odd dots.
`CyclotomicAction/Restriction.lean` adds `cyclotomicRestriction` as truncation
by the unit-image idempotent and proves the underlying module adjunction
`cyclotomicIndResAdjunction`, without a flatness hypothesis. Its unit and
counit are those of the actual descended nonunital map, not assumed maps.
This underlying construction is distinct from the super adjunction below
and does not prove KKO inversion.
`CyclotomicAction/Slides.lean` proves the actual affine signed naturality
`induction_dot_slide`; `induction_dot_slide_odd` specializes it to the minus
sign for an odd new dot and an odd lower morphism. This supplies the corrected
homogeneous intertwiner equation rather than the false unsigned equation.
`CyclotomicAction/Parity.lean` equips affine `Hn` with its parity grading
independently of any integer symmetrizer. The coefficient-support condition
`CyclotomicPolynomialParity` proves homogeneity of the actual first-dot
polynomial generators and, in `cyclotomicIdeal_homogeneous_of_polynomials`,
of the entire two-sided ideal. Right multipliers are decomposed into
homogeneous parts; they are not silently assumed homogeneous.
`CyclotomicAction/SuperQuotient.lean` now descends that parity to the actual
`CyclotomicAlgebra`, with `cyclotomicParity_graded`, homogeneous affine lifts,
and `cyclotomicAppend_parity`. `CyclotomicSupermodules` is the existing
superbimodule category with trivial right scalar algebra. These constructions
do not replace the quotient by a polynomial model or forget its odd part.
`CyclotomicAction/SuperInduction.lean` constructs the actual colour-cut
superbimodule `inductionCorner = B φ(1)` and its balanced-tensor
`cyclotomicSuperInduction`. This is an additive, `k`-linear superfunctor,
including on odd morphisms, using the signed tensor whiskering.
`CyclotomicAction/InductionComposition.lean` constructs `compositionCorner`
with right action through the composite inclusion and proves the even
superbimodule isomorphism `inductionCompositionIso : C eᵢ ⊗_B B eⱼ ≅ C φᵢ(eⱼ)`.
Its forward map is `x ⊗ y ↦ x φᵢ(y)` and its inverse is `z ↦ z ⊗ eⱼ`;
both algebra actions and both parity compatibilities are proved. The scoped
warning-free build and declaration axiom audit pass. This supplies coordinates
for composing two positive-height inductions, not crossing, braid or KKO
inversion relations.
`CyclotomicAction/LastCrossing.lean` constructs the finite matrix sum
`cyclotomicLastCrossing` from the literal last-pair crossing `[i,j] → [j,i]`.
It proves parity `|i||j|`, both colour-cut identities and signed intertwining
`θᵢⱼ(r) τ = (-1)^{|r||i||j|} τ θⱼᵢ(r)` for the two composite inclusions.
Rows are targets, so right multiplication goes from `C θᵢⱼ(1)` to
`C θⱼᵢ(1)`. The scoped warning-free build and declaration axiom audit pass.
`CyclotomicAction/SuperCrossing.lean` now constructs the homogeneous map
`compositionSuperCrossing : compositionCorner i j ⟶ compositionCorner j i`,
with parity `|i||j|` and formula `x ↦ (-1)^{|i||j||x|} x τ` on homogeneous
inputs. Signed left linearity and ordinary right linearity follow from the
proved global intertwiner, not an assumed relation. Its scoped warning-free
build and declaration axiom audit pass. Square, braid and inversion relations
remain separate obligations.
`CyclotomicAction/InductionFunctorComparison.lean` constructs the even natural
isomorphism `inductionFunctorComparison` from successive cyclotomic induction
to tensoring by `compositionCorner`. Its pure-tensor formula is
`x ⊗ (y ⊗ m) ↦ (x φᵢ(y)) ⊗ m`; the inverse uses the existing balanced-tensor
associator and the proved corner isomorphism, with no inverse hypothesis.
`CyclotomicAction/CrossingTransformation.lean` transports
`compositionSuperCrossing` along these comparisons to
`cyclotomicSuperInductionCrossing`, a supernatural transformation between the
two orders of composed induction, homogeneous of parity `|i||j|`.
Signed naturality holds on the full supermodule categories. Both modules pass
the scoped warning-free build and owned-declaration axiom audit. Square,
braid and inversion relations, and the KKO decomposition, remain open.
`CyclotomicAction/SuperRestriction.lean` similarly represents restriction by
`restrictionCorner = φ(1) B`; `cyclotomicSuperRestriction` is additive,
`k`-linear, and parity preserving. The positive-height indexing still leaves
the vacuum step separate; the KKO decomposition is not proved.
`CyclotomicAction/CornerPairing.lean` gives even superbimodule maps
`cornerEvaluation : B e ⊗_A e B → B` and
`cornerCoevaluation : A → e B ⊗_B B e`, together with the two elementary
idempotent triangular identities. These use actual multiplication in the
cyclotomic quotient.
`CyclotomicAction/SuperAdjunctionUnit.lean` constructs the even natural
transformation `cyclotomicSuperUnit`, from the identity to induction followed
by restriction, i.e. each module maps into `e B ⊗_B (B e ⊗_A M)`. Naturality is proved
for odd as well as even module maps; both inserted idempotents have parity
zero.
`CyclotomicAction/SuperAdjunctionCounit.lean` constructs
`cyclotomicSuperCounit` by `(x ⊗ (y ⊗ m)) ↦ (xy)m`. Its naturality proof
accounts for both tensor-whiskering signs and the signed left-linearity of
an odd supermodule map.
`CyclotomicAction/SuperAdjunction.lean` proves both triangular identities and
bundles `cyclotomicSuperIndResAdjunction`. Both directions of its Hom
bijection preserve parity. This is an actual super induction-restriction
adjunction, not only the underlying ordinary adjunction. Remaining action
obligations are the vacuum inclusion, the square, braid and mixed
comparisons for the constructed dot and crossing transformations, and the
projective Mackey/local-inversion theorem with the prescribed parity shifts.

`CyclotomicAction/LastDot.lean` constructs `cyclotomicLastDot` as the image
of the finite diagonal sum of rightmost dots on words ending in the induction
colour. `cyclotomicLastDot_parity` proves parity `D.parity i`, and
`cyclotomicLastDot_corner` proves both unit-image corner identities without
a polynomial-parity hypothesis. `cyclotomicLastDot_comm` proves
`φ(r)c = (-1)^(p |i|) c φ(r)` for every parity-`p` quotient element, using
homogeneous affine lifts. The indexing is height `n+1` to height `n+2`.
`CyclotomicAction/SuperDot.lean` constructs `inductionSuperDot` on this
corner: on homogeneous `x` it is `(-1)^(|x| |i|) x c`, as proved by
`inductionSuperDot_apply`. The concrete last-dot relation gives ordinary
right linearity; the parity sign gives signed left linearity.
`inductionSuperDot_parity` proves degree `|i|`, and balanced-tensor signed
interchange gives `cyclotomicSuperInductionDot`, a `SuperNatTrans` on
`cyclotomicSuperInduction`, homogeneous of degree `|i|`. These declarations
pass the scoped warning-free build. Square, braid, crossing and KKO
comparisons remain open; unsigned right multiplication is not substituted
for the signed-left superbimodule convention.

`CyclotomicAction/ActionSupercategory.lean` packages these supermodule
categories as `cyclotomicActionObject` in the existing `SCat` 2-supercategory,
with bundled target `cyclotomicActionTarget : TwoSCat k`.
`cyclotomicActionInduction` and `cyclotomicActionRestriction` are its
1-morphisms; `cyclotomicActionAdjunction` inhabits the existing
`SKM.SuperAdjunction` and proves both triangles with even unit and counit.
`cyclotomicActionDot_mem` gives the colour parity of its dot 2-endomorphism.
No local inversion or new action interface is assumed. The concrete
positive-height adjunction, dots and crossings above form the action data,
not yet a representation satisfying all defining relations. Vacuum extension
and the parity-shifted Mackey decomposition remain open.

`CyclotomicAction/ContentBlocks.lean` defines `contentIdempotent` as the finite
sum of word identities with a prescribed multiset of colours. Its centrality
uses `hom_eq_zero_of_content_ne`, proved by induction on the presented Hom
space, not a hypothesis about content preservation. The quotient elements
`cyclotomicContentIdempotent` satisfy `_sq`, `_central`, and `_orthogonal`
in `CyclotomicAlgebra`. `wordContent_append` records the colour added by
rightmost strand insertion. These pass a scoped warning-free build and
owned-declaration axiom audit; full CI remains the branch-wide gate.
`contentIdempotent_appendAlgebra` and `cyclotomicContentIdempotent_append`
prove the projector identity for the actual strand-inclusion maps.
`ContentSupport.lean` defines `ContentSupported`, its full subcategory
`CyclotomicContentModules`, and `cyclotomicContentInduction`.
`inductionCorner_content` identifies the left target projector with the right
source projector on the actual corner; `contentSupported_induction` then
uses the balanced tensor relation to prove the content shift `β ↦ {i} + β`.
The full subcategory retains all module morphisms; separate supercategory
instances on this wrapper and the height-zero vacuum extension remain open.

## Proof architecture

| Step | Statement | Status |
| --- | --- | --- |
| Assembly | sorted-boundary independence + source exchange descent + target exchange descent imply the conjecture | Lean: `SKM.nondegeneracy_of_contextual_descent` |
| Sorted boundaries | full upward independence implies independence of every sorted family `(ups u ++ dns r, dns l ++ ups v)`, at every external weight, over full `SYM` | Lean: `WeakMate.sorted_independence` (no action, field, finite-colour or faithfulness hypothesis) |
| Choice independence | expansion injectivity does not depend on the permitted choice of representatives, points and serializers | Lean: `expansion_injective_choice_iff` |
| Target exchange, distinct colours | `TargetExchangeDescent` for `i ≠ j` | Lean: `SKM.distinct_target_exchange_descent` |
| Source exchange, distinct colours | complete adapted families and native coefficient twist | Checked: `distinct_source_exchange_descent` |
| Target exchange, same colour | requires the residual deletion `L ++ Q` | Checked: `same_colour_target_exchange_descent` |
| Source exchange, same colour | requires the residual deletion `L ++ Q` | Checked: `same_colour_source_exchange_descent` |
| B0 headline | upward independence at every weight implies the full conjecture | Checked: `nondegeneracy_of_upward_independence`; also `nondegeneracy_iff_upward_independence` |
| Upward independence | finite observations at fixed weight imply `UpwardIndependence` | Lean: `upward_independence_of_finite_observations` |
| Cyclotomic separation | cofinal colourwise cutoffs jointly detect the full coefficient-extended Hom with fixed spectators; a degree-bound criterion for moving spectators | `cofinal_elv_quotients_with_spectators_detect`, `spectator_images_detect_of_bounds`; moving-family hypotheses remain open |
| Observations | extracted regular-projective evaluation on words including spectators; joint algebraic detection remains an input | `SpectatorEvaluation`, `upwardCoefficientMap_injective_of_spectators`; [SpectatorDetection.md](SpectatorDetection.md) |
| Multicolour deformed action | KKO-type cyclotomic action with ELV odd parameters, even cutoffs at odd colours | proposed: [MulticolourActionTheorem.md](MulticolourActionTheorem.md) |

## Reduction route comparison

[ReductionRoute.md](ReductionRoute.md) compares contextual descent with a graded-dimension
reduction. Contextual descent is now complete, including actual complete source
and target choices and all coefficient columns. `hom_laurentian` already supplies the
finite-dimensionality needed by the alternative field route; the missing super rank recursion
and comparison basis prevent treating the even Orzech argument as an immediate reduction.

`exists_cup_completed_choice` constructs a complete choice from unpaired representatives
and literal cups on a complete residual family, with a sum-label equivalence and exact
layer equations. `exists_choice_with_literal_cups` constructs its inputs from arbitrary
complete choices, with no independence premise. Both orientations with nonempty contexts
are exercised in `CupCompletedChoiceExamples.complete_paired_sector`.
`exists_same_colour_adapted_choices` and `exists_same_colour_adapted_equiv` now
construct simultaneous complete same-colour target choices: a single label
equivalence, literal unpaired terminal crossings, and a common paired embedding
`ℕ × B.Labels` with both cup serializers. Their coefficient comparisons remain open.

## Reservoir-vacuum detection

The separated-sector consumer is now `FusedFixedWeightFamily`, not a family
of moving spectators. Conditional declarations in `ReservoirVacuumDetection`
derive the joint bounded observation identity from composition, connected
reservoir affine coordinates, and the named `NormalizedBubbleFormula` on the
elementary and exterior generators. They then apply bounded ELV separation to
obtain `upwardCoefficientMap_injective` at the same external weight and
`upward_independence_of_fused_fixed_weight_families` for the reduction.
`reservoir_parity_cutoffs_detect` covers arbitrary colourwise even/odd schedules.
`SpectatorEvaluation` remains the one-sector consumer and is not used to
supply the new family's coverage premise.

`ReservoirWeights` constructs cofinal paired cover levels with even probe
level, reservoir parity equal to the prescribed coroot pairing, and exact
level difference. `odd_pairing_invariant` proves invariance under signed root
words. `exists_weights_of_pairing_surjective` realizes the levels in a
pairing-complete lattice; `exists_extended_weights` does so for every datum
in the explicit extension `X × (I → ℤ)`, without changing its Cartan matrix
or parity. `ReservoirWeights.restrictRouquierFamily`, in the
`ReservoirWeightRestriction.lean` module, restricts the actual super
Rouquier factor interface along `μ ↦ (μ,0)`, retaining local inverses and
all parity shifts. Full multicolour action and fused-family construction
remain open.

`QuiverHecke.reservoirWindowCoordinates` in `ReservoirCoordinates.lean`
splits the bounded connected ELV injection over a field and recovers the
whole joint coefficient/PBW window.
`exists_bounded_reservoir_extraction` extends any linear source coordinate
map on that window, without a global finite-quotient automorphism. It does
not identify the regular quotient with the fused vacuum; the latter's
`affine_coordinates` law and normalization comparison remain open.

`ReservoirRegular.lean` constructs the connected quotient's actual cyclic
operators by descending postcomposition. `ReservoirSourceCoordinates.lean`
proves that source coefficient followed by affine action differs from the
joint tensor coordinate by its Koszul diagonal involution, then constructs
`exists_reservoir_source_coordinates` on every C0 window. The involution
preserves bounded windows; it is not asserted to preserve the ELV ideal.
`ReservoirCoverage.lean` supplies `regularVacuumWindow_coordinates` at all
cutoffs, including the zero-window fallback, and
`regularVacuumWindow_covers` for the balanced reservoir schedule.
`exists_regular_vacuum_window` also realizes literal external weight in the
pairing extension. The concrete two-odd consumer is
`scripts/NonVacuity/ReservoirRegularCoordinates.lean`.

`ReservoirFusedVacuum.lean` proves fused-vacuum `affine_coordinates` and
categorical `covers` from a `RegularVacuumIdentification` of the vacuum word
modules with these regular modules (vacuum, affine operators, reservoir
coefficients). `ReservoirFusedBubbles.lean` specializes the first identity of
`SuperRouquierLoc.MateProjectionFormula` to a probe cup and reservoir cap
(`mate_projection_sector_bubble`) and derives `bubbles = reservoir` on all of
`SYM` (`fused_bubbles_eq_reservoir`), the odd bubble being the reservoir's
exterior coefficient (`fused_odd_bubble`).
`upward_independence_of_fused_vacuum_actions` in
`ReservoirFusedDetection.lean` assumes only `FusedVacuumAction` (A0/A1: vacuum
words, regular identification, probe and reservoir coefficient values; A2:
capped mate composite = fused bubble of each generator) and the mate
projection formula. `ReservoirFusedSectors.lean` discharges the mate projection
formula from sector summands through `MateProjectionFormula.of_sectors`, so
`upward_independence_of_fused_sector_actions` assumes only sector summands
with slide, probe inverses and reservoir nilpotence, the vacuum values, the
regular identification and the fused bubble identification. Consumer:
`scripts/NonVacuity/ReservoirFusedDetection.lean`.

`RouquierCoupled.lean` constructs the coupled structure from two separated
factors (`CoupledFactors`: sector decompositions `SectorDecomp` of the coupled
`E₁, F₁, E₂, F₂` into reservoir and probe summands). It builds the diagonal
`coupledAdjunction` with both triangles, the diagonal dots, and the coupled
crossing `coupledCross` as a block matrix on the four summands of `E₁ ≫ E₂`:
factor crossings on the diagonal sectors, the rational position-preserving
cross-sector entries `coupledRationalLeft/Right` (finite series inverting
`y - q x`, nilpotent reservoir and invertible probe; no centrality, odd `q`
allowed), and given sector-swapping blocks intertwining the dots.
`CoupledFactors.slide` proves the coupled upward slide; `sourceSector` and
`targetSector` restrict counits, units and dots as `of_sectors` requires, and
`CoupledFactors.mateProjectionFormula` is the projection formula for the
actual coupled data. `RouquierCoupledSectors.lean` turns this into
`CoupledSectorBubble.toVacuumSectorBubble` and
`upward_independence_of_fused_coupled_actions`. Consumer:
`scripts/NonVacuity/RouquierCoupled.lean`. Remaining inputs of
`FusedCoupledAction`: the family (regular identification), the factor data of
`CoupledFactors` (the sector decompositions of the coupled Hom-family functors
into post/pre summands, sector adjunctions incl. the shifted left adjunctions
of the pre summand, factor dots and diagonal crossings with slides, swap
blocks, probe inverses, reservoir nilpotence), the vacuum values
`probe`/`reservoirValue`/`normalize`, and `fusedBlock`. `RouquierCoupledMate`
proves that a sector projection of the coupled mate is the sector mate of the
corresponding crossing block (`sector_mate_block`, via the transport lemmas
`sectorIn_rouquierMate`/`rouquierMate_sectorOut`), so `fused` reduces to
`fusedBlock`: the probe cup, the sector mate of the rational block
`rationalPR`, and the reservoir cap act as the fused bubble. No `FusedCoupledAction` is
constructed. The quadratic and braid relations of `coupledCross` are not proved
(the projection formula does not use them).

`SKM.reservoir_coefficients_recovered` proves finite triangular inversion of a
specified ordered probe convolution; `reservoir_exterior_recovered` removes a
unit factor from an odd coefficient. The categorical convolution and its
bounded coordinate comparison remain open, as does construction of the fused
family. The connected two-odd examples test the algebraic inputs, not family
existence. See [ReservoirVacuumDetection.md](ReservoirVacuumDetection.md).

## Action review

`CyclotomicAction.SignedMultipliers` checks the signed right-multiplier
composition and a nonzero rational matrix instance: negating both odd
crossings still changes a constant quadratic relation from 1 to -1.
[SignedInductionComparison.md](SignedInductionComparison.md) records the exact
scope. This rules out the uniform-sign, unchanged-parameter assignment, not
an action with a proved directed-sign or parameter comparison. The full
multicolour square and braid comparison remains open. The connected all-odd
`AsymmetricParameters` example has Cartan entries -2,-4 and `Q=u²+v⁴`:
no common crossing-product scalar absorbs the opposite signs of square and
fourth-power dot transport. A valid transported family `Q'=u²-v⁴` and its
conditional signed mixed-square transfer are checked. Thus directed signs
alone with unchanged parameters are insufficient in general; a full
parameter/presentation transport remains necessary.

`CyclotomicAction.Intertwiner` checks the same-colour intertwiners of KKO
(arXiv:1206.5933v2) (8.7)–(8.8) on any signed nilHecke family, hence on two
adjacent equal-colour strands of every word (`oddTwo_block`, `evenTwo_block`).
With the family relations, KKO's `τ_a` is `-εT_j`. Odd colour:
`φ=(v-u)-(v²-u²)T` with `vφ=-φu`, `uφ=-φv`, `φ²=(v-u)²`; the variant `g`
reuses `OddNilHecke.Intertwiner.element` (`g²=-(v²-u²)²(u²+v²)`,
`Tg=T(v-u)(v²-u²)`); far dots and crossings anticommute with `φ` and `g`
(Lemma 8.3, (8.11)–(8.12), (8.15)). Even colour: `φ=1+(v-u)T`, `φ²=1`,
`g²=-(v-u)²`, `Tg=T(v-u)`. The consumer `scripts/NonVacuity/CyclotomicIntertwiner.lean`
uses the all-odd two-colour datum and the polynomial nilHecke representation.
`CyclotomicAction.IntertwinerWords` defines `intertwinerHom l r i j`, KKO's
`g_a e(ν)` from `l++[i,j]++r` to `l++[j,i]++r` (the crossing if `i≠j`, the
variant above if `i=j`), and checks (8.11) for `b=a,a+1`:
`dot_comp_intertwinerHom`, `dot_succ_comp_intertwinerHom`, sign
`(-1)^{|i||j|}`. These are the transports of `x_1` through `g_n⋯g_1` used in
(8.16)–(8.17). `moveHom i l ν` composes them to `g_n⋯g_1 e(i,ν)` (KKO's `Q`,
Proposition 8.4), and `dot_comp_moveHom` is the second identity of (8.13),
`x_{n+1}g_n⋯g_1e(i,ν)=(-1)^{p(i)p(ν)}g_n⋯g_1x_1e(i,ν)`. Far dots pass through
each `g` with sign `(-1)^{p(ν_b)p(ν_a)p(ν_{a+1})}` (`dot_left_comp_intertwinerHom`,
`dot_right_comp_intertwinerHom`), and `dot_mem_comp_moveHom` is the first
identity of (8.13) for dots: `x_b g_n⋯g_1 = (-1)^{p(ν_b)p(i)p(ν)} g_n⋯g_1 x_{b+1}`.
`CyclotomicAction.IntertwinerBalance` moves crossings: `variants_comp_of`
(a morphism intertwining `u,v,T` up to a common sign intertwines both `g`),
`cross_left_comp_intertwinerHom`, `cross_right_comp_intertwinerHom` ((8.12),
sign `(-1)^{p(x)p(y)p(i)p(j)}`) and `cross_left_comp_moveHom`. For crossings of
`R(β)` the first identity of (8.13) is `cross_comp_moveHom` (sign
`(-1)^{p(j)p(c)p(i)p(ν)}`), proved from the three-strand step `meetLeft = meetRight`
(`ψ_{a+1} g_a g_{a+1} = g_a g_{a+1} ψ_a` on `(i,j,c)`). That step is proved for
`i≠j,c` (`meetLeft_eq_of_ne`, braid relation), `i=j=c` (`meetLeft_eq_self`) and
`i=j≠c` (`meetLeft_eq_of_eq_ne`: exact braid on `(i,i,c)` plus dot slides through
`variants_comp_of`); `meetLeft_eq` and `cross_comp_moveHom_of` cover every case but
one. Open: `c=i≠j`,
where the `(i,j,i)` braid correction (`braid_iji`) must cancel against
`cross_cross_ne`; this is the remaining computation (KKO Lemma 8.3, mixed colours).
The braid identity `τ_aφ_{a+1}φ_a=φ_{a+1}φ_aτ_{a+1}` of Lemma 8.3 is checked on
three strands of one colour, for `φ` and for `g`, both parities
(`IsSignedNilHeckeFamily.braid_phiOdd`, `braid_element`, `braid_phiEven`,
`braid_gEven`). Open for KKO Theorem 8.5 (`QP`): the braid identity when the
three colours are not all equal, the composite `g_n⋯g_1` on `(i,ν)`, the map `Q` and the reduction modulo
`R a^Λ(x_2) R^1(β)`.

[ActionReview.md](ActionReview.md) is a proposed source comparison of the seven
steps of the even-cutoff argument. The normality, balanced-ideal, norm and cap-row
repairs survive; the explicit comparison from the super-opposite induction
endomorphisms to the specified upward presentation remains open. Ordinary reversal
for projectivity and super-opposite reversal for natural transformations must not
be identified. No multicolour action is yet claimed in Lean.

`CyclotomicAction.Normality` checks the first-dot normality and inverse
balance equations for even cutoff, the square-zero deformation term and
conjugate square-annihilator, and the odd-cutoff normality and square.
These are ring identities with coefficient commutations and top-coefficient
annihilation explicit, not a constructed normalizing automorphism or a
balanced all-content bimodule. In particular the even inverse-balance dot
is `x+2d`, not `x-2d`. `LocalRelationExamples` checks both balances on
exterior creation/contraction matrices with `x²=1` and `d≠0`, and proves
that using the normalizer instead of its inverse fails. It also constructs
a single directed-sign crossing operator whose constant square is the identity.
Its headline axiom inventory uses only the permitted standard axioms.

[OddCutoffAction.md](OddCutoffAction.md) gives a proposed exterior-translation
reduction for odd cutoffs: `f_i=(x-d_i)C_i(x²)`, with no top-coefficient relation.
The normalizing automorphism acts by parity on coefficients and is involutive;
copying the even-cutoff inverse twist gives the wrong sign. The relative action
extension preserves inversion by triangular dot-row changes. Its unconditional
use still requires the all-content diagram and presentation comparison.

`CyclotomicAction.ExteriorTranslationRelations` proves simultaneous
mixed-dot anticommutation, invariance of arbitrary square-variable mixed
polynomials, and the entire alternating repeated-outer-colour braid
polynomial with a second translated odd middle colour. Its rational
four-dimensional exterior matrices retain a nonzero product of the two
parameters and supply mixed-dot and nonzero braid-correction consumers.
The category equivalence, strand-inclusion compatibility and cyclotomic
quotient descent have not been constructed.

[LowestWeightAction.md](LowestWeightAction.md) records that the proposed
`E=induction`, `-Λ+β` convention is already lowest weight. The opposite orientation
is proposed by signed Chevalley transport into the super-opposite target, reusing
`SKM.chevalleyTwo`. The Hom construction instead reverses one lowest-weight factor
horizontally; it gives two copies of the datum, not their fusion. A nonzero Hom
vacuum and original-datum fusion remain separate requirements.

[ActionLeanPlan.md](ActionLeanPlan.md) orders the proposed construction from
signed induction presentation comparison and simultaneous exterior translation,
through balanced quotients, projectivity, inversion, the action, opposite transport
and the product-datum Hom family. Each module names a consumer and existing
inputs. The next bounded action result is the signed mixed-colour presentation
comparison, not a new abstract action interface.

## Open obligations

1. **Same-colour exchange descent**, source and target. The distinct-colour target proof is
   the template; the equal-colour case must absorb the residual deletion term and its bubble
   corrections.
2. **Distinct-colour source descent**: assemble `SourceExchangeDescent` for `i ≠ j` from the
   adapted-family results above.
3. **The observation interface.** `FiniteUpwardObservations μ t t'` asks for maps into the ELV
   quotient of the coefficient category on the words `t, t'` alone. Over a field it follows from
   upward independence at `μ` (compose the quotient map with the inverse of the coefficient map),
   so it is a restatement of the target, not a weaker statement. An action at lowest weight `-Λ`
   evaluates `E_t 1_μ` only after adding spectator strands `s` with `μ = -Λ + wt(s)`, and `μ` is
   fixed while the cutoff grows. The separation theorem therefore has to be extended to
   cyclotomic quotients with spectators, or the interface restated, before an action can
   discharge it. `SpectatorEvaluation` now states the regular-projective component with
   a specified affine whiskering and bubble lifts on the whole word. Its product law and
   joint detection are still open for an action-derived family. The conditional consumer
   `upward_independence_of_spectators` makes neither of those assertions. Fixed-spectator
   cofinal quotient separation is proved, but does not allow the spectator word to grow
   with the cutoff. The existing quadratic crossing-loss bound fails whenever total
   strand number `n ≥ 3` and cutoff `N ≤ 2n` (`spectator_crossing_bound_obstruction`).
   The next target is a sharper spectator-corner theorem or a fixed-weight reservoir-vacuum
   extraction; neither the failure of this bound nor separate bubble independence decides
   joint detection.
4. **The deformed action.** Independent review of the proposed even-cutoff theorem, in
   particular the balanced maps, the norm audit and the parity conventions of the
   negative-height cap conversion; extension to odd heights at odd colours (the parity of
   `⟨h_i, Λ⟩` is constant on a root-lattice coset when `i` is odd); bubble images at a fixed
   weight with spectators.
5. **Fixed-weight coverage.** Dominant weights are cofinal in each root-lattice coset only in
   finite type, and there odd colours occur only at the short end of `B_n`, never adjacent.
   For general symmetrizable data every weight is `μ₋ - μ₊` with `μ±` dominant, reached by the
   family `Hom(T(-μ₊), W(μ₋))` as in the even case; the super version of that family, and the
   joint detection of the odd bubbles of adjacent odd colours in it, are open. For odd `i`,
   `⟨h_i, μ⟩ mod 2` is constant on root-lattice cosets, so odd cutoffs at odd colours are needed.

## Strict residual serializers
**Strict residual choice interface (checked).** `StrictResidualChoice` rebuilds a complete matching choice using `PointedMatching.ofStrict` on every member. Its `strictResidualLabels` equivalence preserves the exact strict-serializer layers, and `strictResidualChoice_independent` transfers independence by choice invariance. Thus residual independence can be applied to the serializers used in cup completion without identifying them with an unrelated chosen serializer. Contextual same-colour descent is now checked on both sides as recorded below.

`exists_same_colour_cup_rows` now gives complete original, swapped, and residual choices together with the exact evaluated left- and right-cup rows at every dot count and external weight. The unpaired exchange equations are retained. `SameColourCupRowsExamples.complete_cup_rows` checks the interface for a two-colour odd datum over ℚ with both contexts nonempty; its axiom print contains only `propext`, `Classical.choice`, and `Quot.sound`.

## Full contextual target descent

`same_colour_target_exchange_descent` derives independence of the original boundary from independence of its swapped and shortened residual boundaries. The proof kills unpaired coefficients using the actual inverse-crossing formulas modulo the paired output rows, then invokes `pairedExpansion_injective`; both height signs and the zero boundary are included. `target_exchange_descent` combines this with distinct-colour descent and proves the entire `TargetExchangeDescent cs` interface over any commutative coefficient ring admitted by `Sc`. No homogeneity, field, grading, action, or bubble-injectivity hypothesis is added. The concrete two-odd-colour consumer `SameColourTargetFrameExamples.all_target_exchanges` and both headline axiom prints use only the three permitted axioms. `source_exchange_descent` now proves the corresponding full `SourceExchangeDescent cs`.

`SourceFrozenSwap.ren` and `crit` preserve strand renaming and critical IDs. `SourceIdRelabel` now transports validity, full states, cap renamings, and critical lists through injective ID maps fixing fresh IDs; `reducedData_iff` preserves all reducedness data. A cap-containing consumer moves ID zero and checks the actual transports. `SourceCrossState.start_cross` identifies the actual initial-crossing state with the frozen transposition and initial-ID swap, retaining its cap-renamed history in `cross_run`. `SourceCrossAttachment.attach` supplies strict pointed representatives, actual count equivalences and literal initial-crossing serializers. `exists_adapted_pointed_pair` covers both crossing orientations. The complete source choices and coefficient descent use this transport as described in `SourceContextualSorting.md`.

`SourceCapState.start_cap` now identifies the exact initial-cap state, including the reversed frozen endpoints, surviving strand ID and fresh counter. `cap_matching`, `cap_strict`, `cap_layers`, `ren_cap` and `crit_cap` give validity, strictness, layer orientation and full suffix transport. The nonempty-context two-colour consumer checks these identities. `SourceCapAttachment` supplies the residual comparison by inserting the frozen pair and shifting fresh IDs by four. `attach` constructs actual cap-adapted pointed representatives, `cap_family_complete` proves coverage of every paired source class from a complete residual family, and `labelEquiv`/`attach_layers` provide the full count bijection and literal serializer compatibility. The fresh-cup and later-cap consumers check both creation and subsequent ID joins. `SourceCompletedChoice` now assembles the cap and unpaired sectors. `exists_source_same_colour_adapted_equiv` supplies complete choices, the full label equivalence and paired embedding with literal cap serializers on both sides; residual serializers are exactly `PointedMatching.ofStrict` on `B.members`. `exists_source_adapted_distinct_colour_choices` gives complete distinct-colour choices and both initial-crossing cases. These constructions add no independence hypotheses. `distinct_source_exchange_descent` now proves the distinct-colour source branch using these actual complete choices and `distinct_source_adapted_independent`, with the native full-SYM crossing twist. It requires only swapped-boundary independence. `SameColourSourceFrame.kernel_supported_paired` eliminates the unpaired kernel using the actual inverse crossing. `PairedSourceUpwardColumns`, `PairedSourceCupColumns` and `PairedSourceDetection` prove all-height paired detection, retaining inverse-block corrections and negative-height low-cup components. `source_cap_downward_triangular` converts the actual downward-dot serializer to upward-dot columns with a unit leading coefficient and the odd-bubble correction; `pairedExpansion_injective` retains this correction. `same_colour_source_exchange_descent` and `source_exchange_descent` conclude source descent over arbitrary permitted commutative coefficient rings, without field, grading or homogeneity assumptions. The two-odd-colour consumer `SameColourSourceFrameExamples.all_source_exchanges` and its nonempty-context full-SYM column use only the permitted axioms.

## Upward-to-oriented reduction

`SKM.nondegeneracy_of_upward_independence` in `UpwardNondegeneracyReduction.lean` combines `WeakMate.sorted_independence` with both proved contextual exchange descents. Its only independence premise is `WeakMate.UpwardIndependence cs`, at every weight over full abstract `SYM`. `nondegeneracy_iff_upward_independence` supplies the converse. No field, finite-colour, symmetrizer, grading or coefficient-homogeneity restriction is added by the reduction. The concrete two-odd-colour consumer is `UpwardNondegeneracyReductionExamples.two_odd_colour_reduction`. Both headline axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`. This closes B0, not the action or upward-detection obligations needed to establish its premise. The source and target sorting notes record the checked status as well as the mathematical formulas.

## Next targets

**Actual paired target columns (checked).** `SameColourTargetFrame` attaches the complete adapted choices to finite principal columns at every local height, retaining arbitrary abstract `SYM` inputs and both boundary contexts. `positive_column` and `nonpositive_column` identify their expansions with actual postcomposition by the same-colour crossing. `PairedTargetCapColumns` constructs the normalized low-cap columns. `targetPositiveColumns_detect` and `targetNonpositiveColumns_detect` prove finite coefficient detection by the actual unit pivots, with both inverse-block and dot-slide corrections included. `SameColourTargetFrameExamples` checks positive and negative local heights in a two-colour odd datum with nonempty contexts and residual labels. Full target and source descent and B0 are now checked as described above.

`SameColourTargetFrame.pairedExpansion_injective` proves all-height independence of the actual paired sector from swapped and residual independence. Its positive-height proof uses the actual low cap outputs; its nonpositive-height proof needs only swapped independence. `plcW_comp_at` supplies composition through a propositionally equal contextual boundary. The axiom print uses only `propext`, `Classical.choice`, and `Quot.sound`.

These statements were proved by the methods recorded in the linked notes but are not yet on
this branch:

- all-height paired target coefficient columns; source crossing state and point transport;
  contextual source-cap families (complete same-colour target adapted choices are now in Lean)
  ([ContextualSorting.md](ContextualSorting.md), [SourceContextualSorting.md](SourceContextualSorting.md));
- bounded ELV coefficient recovery with locally triangular inversion, and nilpotence of the
  coefficient dot ideal ([UpwardSeparation.md](UpwardSeparation.md));
- odd Frobenius resolvent identities beyond `FrobeniusResolvent`, and the first separated-sector
  chart lemmas ([SpectralCompensation.md](SpectralCompensation.md));
- the parity involution on the coefficient basis and the source/target `β` placement identity;
  the negative-height cap-row conversion ([MulticolourCyclotomicAction.md](MulticolourCyclotomicAction.md)).

## Mathematical guardrails

- Abstract `SYM` has a distinct exterior generator for each odd colour. Spectator strands do
  not show that categorical bubbles realize those generators.
- Signed choice transitions lower crossing/open-dot complexity; closure transport adds dots at
  fixed crossings. Do not conflate the two orders.
- Right coefficient extension uses `d*p`, not `p*d`.
- Inverting an even ELV constant kills the odd parameter of that factor
  (`CyclotomicExteriorObstruction`); separate nilpotent factors are not excluded.
- Squared-dot spectral blocks preserve parity; odd-dot scalar eigenblock compression is not a
  multiplicative coefficient detector.
- The odd intertwiner has norm `-(y²-x²)²(x²+y²)`; generic transport needs both difference and
  sum units.
- At even cutoffs the cyclotomic element is normal, not central: `ν(x) = x - 2d`, and right
  multiplication uses `ν⁻¹(x) = x + 2d`. KKO's centrality step does not apply verbatim.
- [ELV] Theorem 4.5 supplies the rank-one deformed action with odd coefficients and
  Proposition 4.7 its bubble values; the universal-equivalence part of that proof uses rank-one
  nondegeneracy and must not be used circularly.
- The isomeric Heisenberg action is reduced (odd bubble zero) and cannot detect exterior
  coefficients by itself.
- The two-colour connected degree-two model has `δ_i δ_j ≠ 0` but `(reverse crossing)·δ_i δ_j = 0`,
  so joint detection of crossings and bubble products is a separate requirement.
- Finite Python models in `scripts/Nondegeneracy/` test particular instances; none is a proof of
  a general statement.

## Notes

[PROGRESS.md](PROGRESS.md) (status board), [OrientedReduction.md](OrientedReduction.md),
[MatchingChoiceTransition.md](MatchingChoiceTransition.md), [UpwardSeparation.md](UpwardSeparation.md),
[MulticolourActionTheorem.md](MulticolourActionTheorem.md),
[MulticolourCyclotomicAction.md](MulticolourCyclotomicAction.md),
[SpectralCompensation.md](SpectralCompensation.md), [CoupledBubbleEvaluation.md](CoupledBubbleEvaluation.md),
[OddUnfurling.md](OddUnfurling.md), [RewritingAlternative.md](RewritingAlternative.md).

### Vacuum strand inclusion

`CyclotomicAction/Vacuum.lean` supplies `vacuumAppend`, the nonunital algebra map
from `Hn D Sc 0` to `CyclotomicAlgebra D Sc a 0` obtained by adding the first
strand and applying the existing height-one quotient map. `vacuumAppend_one`
and `vacuumAppend_scalar` identify its unit and scalar images with the
single-colour cut; the cuts are idempotent, mutually orthogonal, and act as
units on the corresponding images. `vacuumAppend_parity` and
`vacuumColourCut_parity` give the homogeneous-parameter parity formulas.
This closes the algebra-map boundary at height zero; vacuum superinduction
and the categorical inversion relations are not asserted here.

`CyclotomicAction/VacuumExamples.lean` proves that the vacuum unit and the
scalar two have nonzero images for the rational odd rank-one datum and
zero cyclotomic polynomial. The proof reduces the defining ideal to zero
and uses affine normal-form independence; it is not a positive-degree
monic or finite-dimensional cyclotomic nonvanishing theorem. The scalar
two also lies in the even quotient component. Both vacuum modules pass
targeted warning-as-error builds and an owned-declaration axiom audit.

### Three-strand cyclotomic braid

`CyclotomicAction/Braid.lean` defines the first-pair and last-pair crossing
matrices on the actual `w ++ [i,j,c]` corners. `tripleMatrix_mul` proves that
multiplication of these finite families is reversed pointwise composition.
`affineTriple_braid` and `cyclotomicTriple_braid` prove the uncorrected braid
when the outside colours differ or all three colours coincide, with arbitrary
old words and arbitrary colour parities. These are concrete algebra identities,
not yet the braid between three composed superinduction functors. The latter
still requires comparison with the balanced-tensor associators.
`CyclotomicAction/BraidCorrection.lean` supplies the separate repeated-outside-
colour polynomial relation: `affineTriple_braid_correction` and
`cyclotomicTriple_braid_correction`. Its explicit dot polynomial retains
`(-1)^(|i|(|j|+s))` in every divided-difference term. Both braid cases now hold
in the actual quotient; neither statement assumes a categorical representation.

`BraidOperators.lean` proves the homogeneous degrees of both triple crossing
matrices and carries both quotient identities to signed operators on the
existing graded regular module. `cyclotomicSignedTriple_braid` has no
additional sign. `cyclotomicSignedTriple_braid_correction` retains the
factor `(-1)^(|i||j|)` on signed multiplication by the explicit correction.
No parity restriction on the three colours is imposed. These regular-module
operator identities still do not identify triple induction associators.

### Equal-colour crossing square

`CyclotomicAction/Square.lean` identifies the associator-defined last crossing
with its positioned-word diagram. `cyclotomicLastCrossing_square` proves
square-zero in the concrete quotient. `compositionSuperCrossing_square` proves
square-zero for the actual signed superbimodule map on the composition corner;
it is not merely a statement about an unsigned multiplier. No local inversion
or projectivity is used or concluded.

`CyclotomicAction/Comparison.lean` transports this identity through the existing
even balanced-tensor isomorphism. `inductionCrossingApp_square` concerns the
actual composed superinduction functors; `cyclotomicSuperInductionCrossing_vcomp_app`
shows that every parity component of the supernatural vertical square is zero.

### Mixed quadratic polynomial

`CyclotomicAction/MixedComparison.lean` defines `wordQuadratic` by the specified
`t` and `s` coefficients and the two actual positioned dots.
`cyclotomicLastCrossing_mixed` identifies the product of opposite crossings
with its image in the concrete quotient, for both connected and disconnected
colours. `compositionSuperCrossing_mixed_apply` proves the resulting identity
on every homogeneous element of the actual composition superbimodule. Its
factor is `(-1)^(|i||j|)`, independent of input parity; dropping it would give
the unchanged-parameter error. This is an upward quadratic comparison, not
the mixed induction–restriction Mackey isomorphism.

`ParameterTransport.lean` constructs `parameterTwist`, an involutive
transformation of valid even scalar families, and proves preservation of
homogeneous support. Its monomial sign exponent is
`|i||j| + |i|⌊p/2⌋ + |j|⌊q/2⌋`; the support conditions exclude odd powers
of an odd dot. `oddRight_iterate_even` proves the half-exponent sign for
all even powers of a signed odd multiplier. These coefficient statements
are not by themselves compatibility of all categorical generators.

`ConcreteRelationExamples.lean` checks this coefficient family on the
all-odd datum `[[2,-2],[-4,2]]`, recovers the transported leading units,
and proves the quadratic-minus-quartic identity in the actual affine and
cyclotomic algebras. It checks the minus sign on the actual composition
superbimodule. The repeated-colour polynomial is the last dot minus the
first dot, and the corresponding affine matrix braid is proved. These
are relation consumers, not nonvanishing or local-inversion theorems.

## Parity-compatible probe reachability

[ProbeReachability.md](ProbeReachability.md) separates the proved weight
choice from the remaining categorical vacuum construction. Specializing
`exists_regular_vacuum_window D Sc μ t t' d`, together with `probe_even`,
already gives every original weight an even probe cutoff and a cofinal
reservoir cutoff of the required parity, with exact extended difference
`(μ,0)` and injective regular ELV coordinates. No finite-type or original
pairing-surjectivity assumption is used. The extension retains coroot-kernel
coordinates as well as the prescribed pairings.

`restrictRouquierFamily` restricts the supplied factor interface, not a
constructed full fused action. The remaining regular-vacuum obligation is
to construct the actual `FusedVacuumWords` and the maps and three identities
of `RegularVacuumIdentification` for the same balanced cutoffs. The
`FusedCoupledAction.family` field assumes these data; its sector fields
still require the vacuum values, normalization and fused bubble block.
Thus A3's parity-compatible arithmetic and algebraic regular windows are
closed, while full-action restriction, regular-vacuum identification and
the actual bubble comparisons remain open.

[RegularVacuumComparison.md](RegularVacuumComparison.md) gives a proposed
module-level derivation: contract the defining representable induction
tensor by `b ⊗ m ↦ b ≫ J_i(m)`, with inverse `h ↦ h ⊗ 1`, and take the
source-word component. A content-zero-supported Hom vacuum kills every
probe term by the corner equation `e_0 B_i^probe e_β = 0`, not by numerical
weight arithmetic. The contraction gives the three coordinate identities
for these defining tensor maps. Still missing is the identification of the
connected ELV factor's induction bimodules and signed dots/crossings with
these representable maps, together with the content-supported Hom vacuum
and fusion's upward-block comparison. This is a written derivation, not a
new Lean theorem or a construction of `RegularVacuumIdentification`.
The normalized bubble inverse-block comparison remains separate.

## Finite contextual colour witnesses

`FiniteColourRelations.lean` proves `mem_finiteColourIdeal` for the actual
`(pres D Sc).ideal a b`, not a free syntax surrogate. The proof inducts on
its `Submodule.span` of `Presentation.IdealGen` and joins finite supports
under addition. Each witnessed contextual generator records the defining
relation or interchange law, both whiskering words, and finite linear
pre/post compositions. Its colour set includes the vertices of every
supported diagram, so a cup followed by a cap is not reduced to the empty
external boundary. `eq_finiteColourIdeal` applies this witness to equality
in the presented Hom via `Presentation.lin_eq_iff`.

`FiniteColourRelationsExamples.lean` instantiates the fifth positive inverse
matrix relation at the simple-root weight, with zero labels. Both external
words are empty, while its defining summand has a decorated cup and cap of
colour `i`; the consumer gives a finite contextual witness containing `i`.
This is only finite support of a derivation. The next step is restriction
of each supported contextual generator to a finite colour subtype while
retaining the same weight group X and restricted datum/scalars, including
its regions and interchange signs. No faithful embedding of the full
infinite-colour presented Hom or nondegeneracy follows yet.

## Signed vacuum recovery interface

`SwappedVacuumRecovery.lean` formalizes the recovery half of
`SwappedNondegeneracy.md` §4 and its composition with §§5–6, conditional on one
explicit interface. `SwappedVacuumEvaluation D Sc cs μ t t' d` packages exactly
what the recovery uses at one weight, word pair and degree bound:

- source and target actions on `V → W` respecting source composition, and a vacuum;
- a raw coefficient action `SYM →ₐ End V`;
- an algebra automorphism `θ` of `SYM` preserving the coefficient-weight filtration
  (`PreservesCoefficientWeight`), with source-placed `bubAt (betaSYM a)` acting as the
  raw action of `θ a`;
- an ideal `K` contained in `ExtendedAtLeast bound` with `d < bound`;
- a placement isomorphism `σ` of the coefficient-extended Hom space preserving the
  degree-`d` window;
- a coordinate map `W → Hom/K` with the literal evaluation
  `coord(act(α f)(raw(b) vac)) = q_K(σ(b ⊗ f))` for every raw coefficient `b`.

Checked: `coefficientSubstitution` (θ on the coefficient factor) with
`coefficientSubstitution_source`; `sourceCoefficientHom_mem_extendedAtMost`;
`coefficientSubstitution_mem_extendedAtMost`; `ker_windowQuotient` (the window injects
into `Hom/K` by disjointness); over a field `windowSplitting` (a left inverse `L_d`),
`recover = q ∘ θ⁻¹ ∘ σ⁻¹ ∘ incl ∘ L_d ∘ coord`, `recover_coordinates`,
`toBoundedCyclicRecovery` (at every cutoff),
`upwardCoefficientMap_injective_of_vacuum_evaluations` and the conditional field theorem
`nondegeneracy_of_vacuum_evaluations`: vacuum evaluations at every equal-weight upward
pair, weight and degree imply `NondegeneracyConjecture cs`. The two-odd-colour consumer
`scripts/NonVacuity/SwappedVacuumRecovery.lean` instantiates both statements over `ℚ`.

**Quotient match.** The recovered identity holds before any quotient: `recover` returns
the bounded coefficient Hom itself, then applies `ELVRelationSpan` at cutoff
`d + 2·choose(|t|,2) + 1` for every colour. `ELVRelationSpan` is the two-sided span of
the ELV coefficient ideal together with the first-strand cyclotomic polynomials
(`elvCyclotomic` at odd, `evenCyclotomic` at even colours), which is the standard
first-boundary quotient of the written proof. There is no mismatch. The transformed
last-boundary ideal `K` of §4 enters only through `ideal_le`.

**Bubble normalization match.** `SwappedVacuumBubbles.md` §2 defines the normalized
bubbles via the Lean generators `etaP`, `bubL`, `bubLs`, `oddBubble`, `betaGen` and
`betaDGen`, including the `c_μ⁻¹` factors, so they are `betaSYM cs μ`; the
nonpositive-height case in `SwappedVacuumNonpositiveBubbles.md` uses the same
generators. The interface places them by `bubAt D Sc μ (upWord t)` at region weight `μ`,
the placement used by `BoundedCyclicRecovery`. There is no mismatch.

Open, in this line: (a) instantiate `θ` as the written triangular bubble substitution and
prove `PreservesCoefficientWeight`; (b) instantiate `σ` as the ordered-source sign
`(-1)^{|a||f|}` and prove window preservation; (c) the finite-colour passage: the
interface is stated for the datum itself, while the written proof constructs evaluations
for finite colour restrictions, so a comparison of `upwardCoefficientMap` under
`Datum.restrictColours` is still needed for arbitrary colour sets; (d) construct the
evaluations from the swapped action. `UpwardModuleAction.toSwappedVacuumEvaluation`
(checked) takes the source and target actions from an `UpwardModuleAction` on the
sectors `V t → V t'`, so (d) reduces to the vacuum data of §4 for that action.

### Triangular bubble substitution (item (a))

Checked (`OddMath/SKM/BubbleSubstitution.lean`): for any family `u_i` of power series
with constant term one and scalars `s_i`, `substitutionHom` sends the generating series
`G_i(z) = 1 + Σ e_(i,n) z^(n+1)` to `G_i(-z) u_i(z)` and `δ_i` to `s_i δ_i`; given
`u_i w_i = 1` and `s_i t_i = 1`, `substitutionEquiv` is an automorphism of `SYM` whose
inverse is the substitution by `w_i(-z)` and `t_i` (`polynomialSubstitution_comp`:
`w(-z) u(z) = 1` makes the polynomial substitutions inverse). The weight filtration is
multiplicative (`coefficientAtMost_mul`), the generators are basis vectors of their
weights (`e_eq_coefficientBasis`, `delta_eq_coefficientBasis`), and
`preservesWeight_of_generators` reduces weight preservation of an algebra endomorphism to
its generators. Every substitution preserves the filtration
(`substitutionHom_mem_coefficientAtMost`): `e_(i,n)` goes to a combination of `1` and
`e_(i,m)`, `m ≤ n`. `probeSubstitution M N` is the written θ of §4 (odd:
`C_i(z) ↦ C_i(-z)(1+z)^(-M_i)`, `δ_i ↦ (-1)^(N_i+1) δ_i`; even:
`E_i(z) ↦ E_i(-z)(1-z)^(-M_i)`; `M_i = P_i/2` at odd and `P_i` at even colours); it and
its inverse preserve the filtration, which is `PreservesCoefficientWeight` for the
interface (`scripts/NonVacuity/BubbleSubstitution.lean`). The identification of `M`, `N`
with the probe and reservoir levels of the constructed action belongs to item (d).

### Placement sign (item (b))

Checked in `PlacementSign.lean`: `placementSign D Sc t t'`, the linear involution of the
coefficient-extended Hom space that is diagonal in `extensionBasis` with sign
`(-1)^{|a|·par i}` on `coefficientBasis a ⊗ nf i`, where `|a|` is the size of the
exterior part of `a` (the parity of the basis coefficient, `coefficientBasis_mem_parity`)
and `par i` is `NFIdx.par` (the parity of the normal form, `NFIdx.nf_mem_parity`). Proved:
`placementSign_symm` (involution), `placementSign_sourceCoefficientHom` (the Koszul sign
on each tensor basis vector), and preservation of both `ExtendedAtMost d`
(`placementSign_mem_extendedAtMost`, the `placement_bounded` field) and
`ExtendedAtLeast s`. The consumer `scripts/NonVacuity/PlacementSign.lean` computes the
sign `-1` for one odd exterior coefficient against one dot on an odd strand. The sign
is fixed on the basis; identifying it with the sign produced by the swapped evaluation on
general homogeneous `b ⊗ f` belongs to item (d).

### Finite-colour detection of class relations (item (c), first step)

`FiniteColourClassDetection.lean` (checked) proves `sum_cl_eq_zero_restrict`:
if `∑ cₘ • cl D Sc μ s t (lsₘ) = 0` in the full-colour presentation, there is a finite
`J₁` such that for every `J ⊇ J₁`, all restricted words `s', t'` and layer lists `ls'ₘ`
over `J` that include onto `s, t, lsₘ`, the same relation
`∑ cₘ • cl (D.restrictColours J) (Sc.restrictColours D J) μ s' t' (ls'ₘ) = 0` holds.
`J₁` depends only on the full-colour relation. The proof uses the free representative
`clLin` (`lin_clLin`, `linear_clLin`), `finiteColourIdeal_mono`, the descent
`supported_ideal_lift_at`, injectivity of the inclusion of free diagrams
(`letter_injective`, `shape_injective`, `inclusion_layer_injective`, `diagram_injective`,
`linear_injective`) and reflection of well-formedness (`chain_of_map`, `chain_map_iff`).
No presented-level functor or faithfulness statement is used.

### Finite-colour detection of upward injectivity (item (c), checked)

`OddMath/SKM/FiniteColourBubbles.lean` writes the bubble generators as formal sums of
layer lists (`etaPS`, `epsPS`, `bubLS`, `bubRS`, `oddBubbleS`, `genS`) whose value `evS`
is the generator, and proves that colour inclusion `pushS J` carries the formal sums of
`D.restrictColours J` onto those of `D` (`pushS_genS`). Words in the coefficient
generators give `wordS` with `evS_wordS` (the value is `betaSYM` of the word product)
and `pushS_wordS`. `symRestrict D J k : SYM (D.restrictColours J) k →ₐ SYM D k` sends
generators to generators (`symRestrict_ι`), and word products span `SYM`
(`span_wordProd`). `evS_eq_zero_restrict` is the formal-sum form of
`sum_cl_eq_zero_restrict`.

`OddMath/QuiverHecke/FiniteColourUpward.lean`: positioned generators commute with maps
of colours (`pl_map`, `tgt_map`); normal-form indices pass between `J` and `D`
(`NFIdx.push`, `NFIdx.lift`, `push_lift`, `gens_lift`). `termS` is a formal sum whose
value is `bubAt (betaSYM (word)) ≫ alpha (x^l ψ_w)` (`evS_termS_nf`), compatible with
`pushS` (`pushS_termS`), so `upwardCoefficientMap` of a finite combination of word
products times normal forms is `evS` of one formal sum (`upwardCoefficientMap_list`),
and every coefficient-extended morphism is such a combination (`exists_list_eq`).
`homInclude` (on the normal-form basis, `homInclude_nf`) and `coefficientInclude`
(`symRestrict ⊗ homInclude` through `sourceTensorEquiv`, `coefficientInclude_source`)
include coefficient-extended Hom spaces of a restriction.

**Theorem** `upwardCoefficientMap_injective_of_restrictColours`: if
`upwardCoefficientMap` of `D.restrictColours J` is injective at every finite `J` and
all restricted words `tJ`, `t'J` including onto `t`, `t'`, it is injective for `D` at
`t`, `t'`. Proof: a vanishing image is `evS` of a formal sum; detection gives `J₁`;
enlarge it to contain the colours of `t`, `t'` and of the generator words; lift words and
indices to `J`; the restricted image vanishes, so the restricted element is zero, and
`coefficientInclude` maps it onto the original. No restriction functor between presented
categories and no independence of the restricted coefficient basis is used.
Consumer: `scripts/NonVacuity/FiniteColourUpward.lean`.

### Finite-colour reduction of the conjecture (item (c), checked)

`OddMath/QuiverHecke/FiniteColourNondegeneracy.lean` composes the detection theorem with
`upward_independence_of_coefficientMap` and `SKM.nondegeneracy_of_upward_independence`.
`wt_ups_restrictColours` shows that colour inclusion preserves the weight of upward words,
so the equal-weight condition passes to restrictions.

* `nondegeneracy_of_restrictColours_upward`: if `upwardCoefficientMap` of
  `D.restrictColours J` is injective for every finite `J`, every equal-weight pair of
  restricted upward words and every external weight, then `NondegeneracyConjecture cs`.
  Commutative ground ring; no field, grading, homogeneity or independence premise.
* `nondegeneracy_of_finiteColour_upward`: the same with the hypothesis stated for every
  datum with a finite colour set (same weight lattice and ground ring).
* `nondegeneracy_of_restrictColours_vacuum_evaluations`: over a field, a
  `SwappedVacuumEvaluation` at every finite restriction, equal-weight word pair, external
  weight and degree bound implies the conjecture for `D`.

Consumer: `scripts/NonVacuity/FiniteColourNondegeneracy.lean` (a datum with colour set `ℕ`).
Thus item (c) is closed: the remaining obligation of the vacuum-recovery chain is item (d),
the construction of the vacuum evaluations for finitely many colours. The converse direction
(the conjecture for `D` implies upward injectivity of the restrictions) is not proved and is
not needed.

Remaining for (c): express each extended basis vector's image under
`upwardCoefficientMap` as a scalar multiple of one class `cl μ (upWord t) (upWord t') N`
whose scalar and layer list are compatible with `Datum.restrictColours` (the bubble
generators, `bubAt`, `betaSYM` on ordered generator products, and `alpha` via `alpha_cl`),
lift extended basis indices to `J`, and combine with `sum_cl_eq_zero_restrict` to deduce
injectivity of `upwardCoefficientMap` for `D` from injectivity for all finite restrictions.

### Vacuum block (item (d), interface checked)

`SwappedVacuumBlock.lean` fixes the schedule of `SwappedNondegeneracy.md` §2 and states
the vacuum data of §4 as one structure on an upward module action. Schedule (checked):
`vacuumCutoff t d = N₀ = d + 2·C(|t|,2) + 1`; `probeLevel = Pᵢ = 2N₀ + 2·max(hᵢ(μ),0)`;
`reservoirLevel = Nᵢ = 2N₀ + |hᵢ(μ)|`; `probeExponent = Pᵢ/2` at odd and `Pᵢ` at even
colours; `probeLevel_even`, `probeLevel_sub_reservoirLevel` (`Pᵢ - Nᵢ = hᵢ(μ)`),
`vacuumCutoff_le_reservoirLevel` (`Nᵢ ≥ N₀`), `vacuumCutoff_sub_choose`
(`N₀ - 2·C(|t|,2) = d + 1`); `vacuumSubstitution = probeSubstitution probeExponent
reservoirLevel` is θ, with `vacuumSubstitution_weight`.

`SwappedVacuumBlock D Sc cs μ t t' d` (the hypotheses supplied by the swapped and ELV
factor actions) has fields:

- `A : UpwardModuleAction D Sc μ` (the swapped action on Hom sectors at weight `μ`);
- `vacuum : A.V t` and `raw : SYM →ₐ End (A.V t)` (raw reservoir coefficients);
- `bubbles_eq : A.bubbles cs t a = raw (θ a)`: (A16);
- `ideal` with `ideal_le : ideal ≤ ExtendedAtLeast (N₀ - 2·C(|t|,2))`: the transformed
  last-boundary ideal `K_(N,T)` and its bound from `SwappedVacuumCoordinates.md` §6;
- `coordinate : A.V t' → Hom/K` and `evaluation : coord(act(α f)(raw(θ a) vac)) =
  q_K(σ(coefficientSubstitution θ (a ⊗ f)))`: (A18), with σ = `placementSign`.

Proved downstream: `evaluation_raw` (the form for raw coefficients `b = θ a`),
`toSwappedVacuumEvaluation` (bound `d + 1`, placement `placementSign`), and the
conditional field theorem `nondegeneracy_of_vacuum_blocks`: blocks at every equal-weight
upward pair, `μ` and `d` imply `NondegeneracyConjecture cs`. Consumer:
`scripts/NonVacuity/SwappedVacuumBlock.lean` (schedule values at `h = -3`, the
conditional theorems over `ℚ`).

Remaining for (d): construct a block. `A` is the output of the swapped-action assembly
(currently under an explicit left-mate-invertibility input, see the (A9) paragraph);
`raw`, `vacuum`, `ideal`, `coordinate` come from the ELV factor at probe levels `Pᵢ` and
reservoir levels `Nᵢ`; `bubbles_eq` is `NormalizedBubbleFormula` at this schedule, and
`evaluation` is the vacuum computation of §4 with the identification of the swapped
evaluation sign with `placementSign` on homogeneous `b ⊗ f`.

### Vacuum bubbles from the right-bubble moments (checked)

`SwappedVacuumBubbleSeries.lean` proves the last step of both bubble notes ((15) of
`SwappedVacuumNonpositiveBubbles.md` §5, and its positive-height analogue): the field
`bubbles_eq` of `SwappedVacuumBlock` follows from the moment formulas (12) and (14).

- `VacuumSeries.substitutedSeries u i = G_i(-z)·u_i(z)` (its coefficients are the
  generator images of `θ`: `coeff_succ_substitutedSeries`), and
  `VacuumSeries.momentSeries w i = w_i(z)·G_i(-z)⁻¹`, inverse to it when `u w = 1`
  (`substitutedSeries_mul_momentSeries`). With `w = probeSeriesInv M` the moment series
  is `(1-z)^(M_i)/E_i(-z)` at even and `(1+z)^(M_i)/C_i(-z)` at odd colours.
- `VacuumMoments cs A t raw M N` (Prop structure): `c_(μ,i)·bubRs(s)` (even) and
  `c_(μ,i)·bubRs(2s)` (odd), acting on `V t`, equal `raw` of the coefficients of the
  moment series, and `oddBubble` acts as `raw((-1)^(N_i+1) δ_i)`.
- `VacuumMoments.bubbles_eq`: then `A.bubbles cs t a = raw (probeSubstitution M N a)`
  for all `a`; `vacuum_bubbles_eq` is the case `M = probeExponent`, `N = reservoirLevel`,
  i.e. the field `SwappedVacuumBlock.bubbles_eq`. Proof: Brundan–Ellis (1.19)/(5.4) as
  `beta_h`, `betaD_h` (hold in the presentation), `Sym.e_h_rel`, uniqueness of left
  inverses of a series with constant term one (`eq_of_sum_mul_eq_zero`), `SYM.hom_ext`.

The moment formula is uniform in the height. At even colours of height zero (principal
inverse `j = s⁻¹`, corrected entry `a = (y-x)⁻¹` of (A6)) the leftward-cup moments are
`m_l = -[z^l] E(-z)/(1-z)^P` (the sign `-q` sits on the leftward cup only) and the
right moments `m'_l` carry no sign, so `B = 1 - Σ m_l z^l`, `B' = 1 + Σ m'_l z^l` satisfy
the infinite Grassmannian relation `B·B' = 1` with `B' = (1-z)^P/E(-z)`, as in
`even`; moving the sign to the other orientation breaks it at order `z²`. Hence
`vacuumSubstitution` is unchanged and `β(e_r) = (-1)^r [z^r] B = e_r +` lower.

Remaining: derive the moment formulas from generator images of the swapped action
(slide (2), inverse column (3) and the probe/reservoir polynomials of
`SwappedVacuumBubbles.md`; extreme inverse row/cap and the principal inverse of the
nonpositive note). Consumer: `scripts/NonVacuity/SwappedVacuumBubbleSeries.lean`.

### The vacuum evaluation from the tensor basis (checked)

`SwappedVacuumBasisEvaluation.lean` reduces the field `evaluation` (A18) of
`SwappedVacuumBlock` to the tensor basis `coefficientBasis a ⊗ nf i`.

- `basisKoszulSign k a i = (-1)^(|a||i|)`; this is the sign `placementSign` puts on the
  basis vector (`placementSign_sourceCoefficientHom`), i.e. the source-placement sign
  `(-1)^(|b||z|) z b a = b z a` of `SwappedVacuumCoordinates.md` (2)–(3), §7.
- `vacuum_evaluation_raw_of_basis`: if `coordK(act(α nf_i)(raw b_a · vac))` is
  `(-1)^(|a||i|)` times the class of `b_a ⊗ nf_i` for every basis pair, then
  `coordK(act(α f)(raw b · vac)) = q_K(σ(b ⊗ f))` for all `b`, `f` (both sides are
  bilinear: `vacuumEvaluationBilin`, `placedCoefficientBilin`, `LinearMap.ext_basis`).
- `vacuum_evaluation_of_basis`: the same for `raw (θ a)`, in the form of the field.
- `SwappedVacuumBlock.ofMoments`: a vacuum block from an upward module action, a vacuum,
  `raw`, `VacuumMoments` at the schedule, the ideal with `ideal_le`, the coordinates and
  the basis values.

Remaining: the basis values themselves (`SwappedVacuumCoordinates.md` §§2–7) from
generator images of the swapped action. Consumer:
`scripts/NonVacuity/SwappedVacuumBasisEvaluation.lean`.

### The vacuum basis values from a natural corner evaluation (checked)

`SwappedVacuumCornerEvaluation.lean` derives the basis values above
(`SwappedVacuumCoordinates.md` §§2–7) from an explicit interface for the part of the
swapped action not yet assembled.

- `VacuumCornerEvaluation D Sc A s raw vacuum` (the open input, stated as a structure):
  submodules `K t` of `coefficientObj s ⟶ coefficientObj t` (the transformed ideal of §5),
  linear maps `ev t : A.V t → (s ⟶ t) ⧸ K t` (evaluation at the reservoir corner pulled
  back through `U` of §4), the generator square `ev_layer` (if `ev v = [y]`, then a
  generating layer `L` applied to `v` evaluates to `[y ≫ (1 ⊗ L)]`, no sign), and
  `ev_vacuum : ev s (raw a · vac) = [a ⊗ 1]` (§3).
- `coefficientHom_one_comp`: `(1 ⊗ f) ≫ (b ⊗ g) = b ⊗ (f ≫ g)` for every `g` (the even
  unit coefficient gives Koszul sign `1` against each homogeneous diagram).
- `VacuumCornerEvaluation.ev_act`: the square for every affine morphism, by induction
  over layers (`hom_induction_layers`).
- `sourceCoefficientHom_id_comp`: `(a ⊗ 1) ≫ (1 ⊗ f) = σ(a ⊗ f)`, via
  `reservoirSourceOrder_source` (`placementSign = reservoirSourceOrder`).
- `VacuumCornerEvaluation.vacuum_evaluation`: (7),
  `ev(act(α f)(raw a · vac)) = [σ(a ⊗ f)]`; `basis_values`: the hypothesis of
  `SwappedVacuumBlock.ofMoments`.
- `SwappedVacuumBlock.ofCornerEvaluation`: a vacuum block from `VacuumMoments`, a corner
  evaluation and `ideal_le` for `K t'`.

Remaining inputs, all in `VacuumCornerEvaluation`: `ev_layer` from the word values of
§2 (`V_t(M) = B e_ν(t) ⊗ M`, dot ↦ `R_x`, crossing ↦ `ε_ij R_τ`) and `U` of §4 together
with the closure of the §5 ideal; `ev_vacuum` from the coefficient action of §3. Not
yet connected to the abstract `SwappedAssembly` layer representation, which is not yet
specialized to the reservoir corner. Consumer:
`scripts/NonVacuity/SwappedVacuumCornerEvaluation.lean` (includes the quotient by the
whole Hom space as an instance of the structure).

### The right-bubble moments from the left-bubble series (checked)

`SwappedVacuumAdjunctionBubbles.lean` reduces `VacuumMoments` to the left bubbles, the
composites of the leftward cup (with the sign `-q` of the corrected equal-colour crossing
entry) and the rightward cap with dots, as given by the `homContent` adjunction images
(`ProbeReservoir.cupImage`, `ProbeReservoir.capImage`).

- `AdjunctionBubbleSeries cs A t raw M N` (the open input, stated as a structure), on the
  source sector `A.V t` of an upward action: `left_even`,
  `closedAct(c⁻¹ · bubLs(s)) = raw [z^s] G_i(-z) u_i(z)` with `u = SYM.probeSeries M`,
  i.e. `B_i(z) = E_i(-z)/(1-z)^(P_i)`; `left_odd`, the same for `bubLs(2s)`, i.e.
  `C_i(-z)/(1+z)^(M_i)`; `oddBubble`, the odd bubble acts as `(-1)^(N_i+1) δ_i`.
- `eq_of_sum_mul_eq_zero_left`: right inverses of a series with constant term one are
  unique (no commutativity needed).
- `AdjunctionBubbleSeries.right_even`, `right_odd`: the normalized right bubbles act as
  the coefficients of `B'_i = B_i⁻¹ = (1-z)^(P_i)/E_i(-z)` (resp. `(1+z)^(M_i)/C_i(-z)`),
  by the infinite Grassmannian relations `SKM.eq_5_5`, `SKM.eq_5_6`, which hold in the
  presented 2-category and so under `closedAct`. `B'` is derived, not assumed.
- `AdjunctionBubbleSeries.vacuumMoments`, `bubbles_eq`: `VacuumMoments` and (A16).

No hypothesis on the swapped action beyond `AdjunctionBubbleSeries` is needed: the closed
bubbles act through `closedAct`, which is part of every `UpwardModuleAction`. Remaining
input: the three fields, for every `s` (including the low-degree fake bubbles of (2.15),
(2.16)), at the action built from the generator images, evaluated on the probe and
reservoir summands. Consumer: `scripts/NonVacuity/SwappedVacuumAdjunctionBubbles.lean`
(includes the zero source sector as an instance of the structure).

### End-to-end conditional theorem (checked)

`SwappedConditionalNondegeneracy.lean` composes the swapped action, the bubble series and the
corner evaluation into one statement of the conjecture. A `SwappedVacuumObservation B D Sc cs
μ t t' d` (in a target 2-supercategory `B` in the universe of `k`) bundles exactly the open
inputs:

1. `P : ProbeReservoir k B D Sc`: the probe and reservoir Rouquier families with their
   multicolour relations and the probe's shifted left adjunctions (F1–F2).
2. `c`, `L` and `relations : P.SwappedRelationData c L`: the entrywise identities of the
   swapped generators (`quad`, `slide`, `braid`, `zigzag`, `sigma`, `leftward`,
   `windowZero`, `supernatural`); with `Gs`, `Ys` these give the swapped action
   `A = relations.upwardModuleAction Gs Ys μ`.
3. `vacuum`, `raw`: the vacuum vector and the raw reservoir coefficient action on `A.V t`.
4. `bubbles : AdjunctionBubbleSeries cs A t raw (probeExponent D μ t d)
   (reservoirLevel D μ t d)`: the left-bubble series at the schedule of §2.
5. `corner : VacuumCornerEvaluation D Sc A t raw vacuum` (`ev_layer`, `ev_vacuum`).
6. `ideal_le`: the §6 weight bound `corner.K t' ≤ ExtendedAtLeast … (N₀ - 2·C(|t|,2))`.

Checked:

- `SwappedVacuumObservation.toSwappedVacuumBlock` (moments from
  `AdjunctionBubbleSeries.vacuumMoments`, (A18) from `SwappedVacuumBlock.ofCornerEvaluation`).
- `nondegeneracy_of_swapped_vacuum_observations`: observations for every equal-weight
  upward word pair, `μ` and `d` give `SKM.NondegeneracyConjecture cs` over a field, via
  `nondegeneracy_of_vacuum_blocks`.
- `nondegeneracy_of_restrictColours_swapped_vacuum_observations`: the same from
  observations for the finite restrictions of `D` (arbitrary colour set), via
  `nondegeneracy_of_restrictColours_vacuum_evaluations`.

Consumer: `scripts/NonVacuity/SwappedConditionalNondegeneracy.lean`.

Glue not yet available (open):

- Factor actions as probe and reservoir (checked): universes as above (the swapped
  assembly takes `B : Type uB` with `BicategoryStruct.{w, v} B`). The Π-structure on Hom
  categories is supplied by `Π-𝔖ℭ𝔞𝔱`:
  - `SKM.RouquierFamily.toPiSCat`, `SKM.RouquierMulticolour.toPiSCat`
    (`OddMath/SKM/RouquierPiSCat.lean`): a super Rouquier family in `𝔖ℭ𝔞𝔱` whose weight
    spaces carry Π-structures is one in `Π-𝔖ℭ𝔞𝔱`, with the same data; multicolour relations
    transfer (`rouquierPower_piSCat` compares the vertical powers).
  - `CyclotomicAction.fullPiSupercategory`, `productPiSupercategory`,
    `heightContentSupported_piObj` (the content idempotent is even, so `Π` preserves
    content support), `globalWeightSpacePi`, `globalPiRouquierFamily`
    (`CyclotomicAction/PiWeightSpaces.lean`).
  - `globalProbeReservoir` and `nondegeneracy_of_global_factor_observations`
    (`GlobalFactorNondegeneracy.lean`): the probe and reservoir are
    `globalPiRouquierFamily` at `(aP, ΛP)`, `(aR, ΛR)`, the probe's left adjunctions are
    `RouquierFamily.leftAdjoints`. The `ProbeReservoir` obligation becomes: local inversion
    `GlobalLocalInversion` under `CyclotomicDegreeMatch D a Λ` (each `aᵢ` monic of degree
    `⟨hᵢ, Λ⟩`; local inversion is false without it), and `SKM.RouquierMulticolour` of the two
    families `globalRouquierFamily` (open: quadZero, quadNe, slides, braid, braidEq, invNe for
    distinct colours of the cyclotomic factors). The observations must have
    `O.P = globalProbeReservoir …`; the other observation fields are unchanged.
- `AdjunctionBubbleSeries` is not derivable from `SwappedRelationData`: the relation
  identities constrain only the generator relations, while the series fixes the values of
  the closed left bubbles (leftward cup with the sign `-q`, then the cap with dots) against
  the raw coefficient action, with the contents `G_i` and exponents `P_i`, `N_i` of the
  probe and reservoir summands, including the fake bubbles of (2.15)/(2.16). These values
  are a computation in the concrete cyclotomic factors (their `homContent` adjunction
  images on the summands), so the series stays an explicit hypothesis until the factors
  are instantiated.
- `ev_layer` and `ev_vacuum` are not derivable from the abstract `ProbeReservoir`: they need
  the corner model of `SwappedVacuumCoordinates.md` §§2–5 (the map `U`, the signed Hom-corner
  evaluation and the ideal `K_N`) for the specific factors.

Layer glue (checked, `SwappedVacuum/LayerAction.lean`):

- `LayerRep.toLocal_functor_map_layer`: the functor of a layer representation sends a single
  layer to its layer map, transported along the boundary equalities.
- `SwappedObligations.upwardModuleAction_act_layer`: the upward action of the affine layer
  `alpha (diag (ofLayer L hv))` is `Q.act ((label D μ).layer L)`, transported along
  `(label D μ).dom_eq`, `cod_eq`.
- `ProbeReservoir.SwappedRelationData.upwardModuleAction_act_layer`: for the swapped action
  this is `P.layerMap (P.swappedGens c L) ((label D μ).layer L')`. So `ev_layer` is a
  statement about the swapped layer matrices of the labelled layers, entry by entry.

Transformed ideal and the §6 bound (checked, `SwappedVacuum/TransformedIdeal.lean`):

- `TransformedGenerator cutoff T`, `TransformedIdeal cutoff T s t`: the ideal `K_(N,T)` of
  `SwappedVacuumCoordinates.md` §5, i.e. the two-sided span of `J_N`
  (`elvCoefficientIdeal`), the coefficients in `T`, and the last-position polynomials (4)
  `transformedCyclotomic v i N = Σ_j (-1)^(p(i) binom(j,2)) c_(i,j) ⊗ y_last^j` in the words
  `v ++ [i]` (`c_(i,j)` = `factorCoefficient`, the literal monic factor coefficients).
- `lastBoundaryPolynomial_mem_score`, `transformedIdeal_le_extendedAtLeast`: bound (5) when
  `N₀ ≤ N_i` and every coefficient in `T` has weight `≥ N₀`;
  `transformedIdeal_quotient_injective_on_extendedAtMost`: detection (6).
- `transformedIdeal_le_vacuumWindow`: at the reservoir levels this is the `ideal_le` field of
  `SwappedVacuumObservation`. So `ideal_le` follows from `corner.K t' ≤ TransformedIdeal …`.
  The identity `K = U⁻¹(I_N)`, which needs the map `U` of §4, remains open.

The written vacuum-recovery argument (schedule `P_i - N_i = h_i(μ)`, bubble series, §6
bound) was checked against these interfaces; no discrepancy was found.

### Reflection factor of the half-turn `U` (checked)

`OddMath/QuiverHecke/HalfTurn/Mirror.lean` formalizes the first factor of the map `U` of
`SwappedVacuumCoordinates.md` §4: the reflection of the quiver Hecke supercategory
`pres D Sc` in a vertical axis, with the same parameters.

- `mirrorSig D : SigMirror (sig D) (sig D)` reverses words; `mirrorWeight D` is `1` on dots and
  `-(-1)^{|i||j|}` on the crossing of `i` and `j`.
- `mirror_rel D Sc r` (every defining relation is killed). Images: quadEq ↦ quadEq,
  quadZero(i,j) ↦ quadZero(j,i), quadNe(i,j) ↦ quadNe(j,i), slideL ↔ slideR, slideLEq ↔
  slideREq (coefficient 1); braid(i,j,m) ↦ `z_ij z_im z_jm` braid(m,j,i);
  braidEq(i,j) ↦ `(-1)^{|i|}` braidEq(i,j). The quadNe and braidEq cases use the interchange
  of dot blocks on distinct strands (`dotDiag_swap`, `diag_dots_swap`,
  `braidEq_dots_three`) and the reindexings `(p,q) ↦ (q,p)`, `s ↦ p-1-s`, `s ↦ dn-1-s`;
  the Koszul signs vanish on the support of `s_ij` and because `dn_ij` is even for odd `i`.
- `mirrorFunctor D Sc`, with `mirrorFunctor_obj` (words reversed) and `mirrorFunctor_diag`.

Consumer: `scripts/NonVacuity/QuiverHeckeMirror.lean`. Next: the super flip
`pres D Sc ⥤ SOp (pres D (parameterTwist D Sc))` (second factor of `U`), the composite `U`,
and the identification of the corner ideal `U⁻¹(I_N)` with `TransformedIdeal`.

### Super-flip factor of the half-turn `U` (checked)

`OddMath/QuiverHecke/HalfTurn/SuperFlip.lean` formalizes the second factor of `U`
(`SwappedVacuumCoordinates.md` §4): the reflection in a horizontal axis, a contravariant
superfunctor `flipFunctor D Sc : (pres D Sc).Presented ⥤ SOp k (pres D (parameterTwist D Sc)).Presented`.

- Words are kept; dots are fixed; the crossing `Eᵢ Eⱼ → Eⱼ Eᵢ` goes to `flipWeight` times the
  crossing `Eⱼ Eᵢ → Eᵢ Eⱼ`, `flipWeight (cross i j) = -(-1)^{|i||j|} ε_ij` with `ε_ii = -1`,
  `ε_ij = 1` (`i ≠ j`). A normal-form diagram goes to its reversed layers times `flipC`, the
  Koszul sign of the reversal times the weights (`flip_mkD`, `flipC_append`,
  `flipC_replicate_dot`: `n` dots on an `i`-strand give `(-1)^{|i|⌊n/2⌋}`).
- Target parameters `parameterTwist D Sc`: `t_ij ↦ (-1)^{|i||j|} t_ij`, `s_ij^{pq} ↦
  (-1)^{|i||j| + |i|⌊p/2⌋ + |j|⌊q/2⌋} s_ij^{pq}` (`i ≠ j`).
- `flip_rel D Sc r`: every defining relation (BE2 Def. 1.5, upward part) is killed. Images and
  constants: quadEq ↦ quadEq (`(-1)^{|i|}`), quadZero, quadNe ↦ same (`(-1)^{|i||j|}`),
  slideL(i,j) ↔ slideR(j,i) (`(-1)^{|i||j|}` times the crossing weight), slideLEq ↔ slideREq (1),
  braid(i,j,m) ↦ braid(m,j,i) (`flipC` of the left side), braidEq ↦ braidEq
  (`(-1)^{|i|(|j|+1)}`). The braidEq case uses `diag_dots_reverse_three` (reversal of three dot
  blocks on `i j i`) and `parity_half_add` (`⌊x/2⌋ + ⌊r/2⌋ ≡ 1 + ⌊n/2⌋` when `x + r + 1 = n` is
  even), applied with `n = dn_ij` and with `n = p` on the support of `s_ij^{pq}`.

Consumer: `scripts/NonVacuity/QuiverHeckeSuperFlip.lean`. Next: the composite `U` of
`mirrorFunctor` and `flipFunctor` (crossing weight `ε_ij`), and the identification of the corner
ideal `U⁻¹(I_N)` with `TransformedIdeal`.

### The half-turn `U` (checked)

`OddMath/QuiverHecke/HalfTurn/Composite.lean` composes the two reflections into the map `U` of
`SwappedVacuumCoordinates.md` §4:
`halfTurnFunctor D Sc = mirrorFunctor D Sc ⋙ flipFunctor D Sc :
(pres D Sc).Presented ⥤ SOp k (pres D (parameterTwist D Sc)).Presented`.

- `halfTurnLD (u, g, v) = (v^rev, g, u^rev)` (dot at position `r` ↦ position `n+1-r`, crossing
  at `r` ↦ crossing at `n-r`); `halfTurnL ls` = the half-turned layers in reverse order
  (`flipL_map_mirrorLD`).
- `halfTurnWeight`: `1` on dots, `ε_ij` on the crossing of `i` and `j` (`ε_ii = -1`);
  `mirrorWeight_mul_flipWeight`: the two reflection weights `-(-1)^{|i||j|}` and
  `-(-1)^{|i||j|}ε_ij` multiply to `ε_ij`.
- `halfTurnC ls`: the weights times the Koszul signs of the reversal (super-opposite product
  `U(f;g) = (-1)^{|f||g|} U(f)U(g)`); `mirror_prod_mul_flipC`.
- `halfTurn_mkD`: `U(mkD ls) = halfTurnC ls • mkD (halfTurnL ls)` (retyped along
  `halfTurn_obj : t ↦ t^rev`); generator table `halfTurn_dot`, `halfTurn_cross` (§4 table, no
  coefficients yet).

Consumer: `scripts/NonVacuity/QuiverHeckeHalfTurn.lean`. Next: `U` on the coefficient-extended
Hom spaces (`U(a ⊗ f) = a ⊗ U(f)`), and the identification of the corner ideal `U⁻¹(I_N)`
with `TransformedIdeal`.

### Append-side PBW basis (checked) and the left-oriented Mackey summand (proposed)

`OddMath/QuiverHecke/AppendParabolic.lean`, `OddMath/QuiverHecke/AppendBasis.lean`: the mirror of
the prepend input basis (`AppendCoordinates.md` §§1–2). `appendPermutation h (v, u) = u⁻¹ (v × 1)`
for `h : n + 1 = m` is bijective with additive length; `appendBasis D Sc : Basis (AppendIdx i s t)`
of `Hom(s ++ [i], t)` with `appendBasis_apply`, `appendElt_eq_comp`
(`(nf ▷ 1_i) ≫ last-strand dots ≫ moving crossings`) and `appendElt_approx`. Next
(`AppendCoordinates.md` §§3–4, proposed): the right-oriented affine coordinate equivalence along
`appendAlgebra` (mirror of `prependCoordinateEquiv`), its balanced tensor descent, and the
left-oriented correction (2) giving `direct`, `span`, `Rt_F`, `Rt_j` of `MackeyCosets` with
`F(L₀') = ψ(B) τ_n ψ(B)` and `X` a signed exponent shift.

Checked: `OddMath/QuiverHecke/CyclotomicAction/AppendCoordinates.lean`, the matrix layer of
the append expansion. `appendPBWTerm i u m b = c_u · x_last^m · appendAlgebra b` with its
right old-algebra law and corner membership; `appendPBWTerm_single` (entry formula),
`inductionLastDot_eq_dotE`, `appendPBWTerm_old_nf` (a term with a single old normal form
coefficient is the matrix entry of `appendElt`) and `append_single_expansion` (every matrix
entry with appended source is a finite sum of PBW terms, coefficients from `appendBasis`).
Checked: `OddMath/QuiverHecke/CyclotomicAction/AppendEquivalence.lean`,
`appendCoordinateEquiv i n : ((AppendShuffleAt n × ℕ) →₀ Hn n) ≃ₗ[k] Corner(appendAlgebra)`,
the forward map the finite sum of `appendPBWCorner`, inverse the entrywise assembly
`appendCoefficients`, both respecting the right old-algebra action
(`appendCoordinateEquiv_right`, `_symm_right`). Checked: `AppendTensorCoordinates.lean`, `appendTensorEquiv`, the balanced
descent to any unital left old-algebra module. Checked: `QuiverHecke/AppendShuffleRuns.lean`:
an append shuffle is determined by `j = u⁻¹(n)`, `u⁻¹ = runPerm n j = s_j ⋯ s_(n-1)`
(`runPerm_val`), `canWord (n+1) u⁻¹ = [j, …, n-1]` (`canWord_appendRun`,
`exists_canWord_eq_range'`), and `appendRunEquiv : Fin (n+1) ≃ AppendShuffle` (via
`card_appendShuffle = n + 1`). Since `cw` reverses words, the moving crossings `c_j` first
cross the last two strands and then the old strands only: `c_j = c'_j τ_n` (algebra order).
Checked: `CyclotomicAction/AppendLeftCrossing.lean`. `appendShuffleHom_castSucc` (entry
form) and `appendShuffleElement_castSucc_mul_corner`: on the two-sided corner,
`c_j ψ(ψ(1)) = ψ(c'_j) τ` for `j ≤ n`, where `c_j` moves the appended strand of
`Hn (n+2)` to position `j`, `c'_j` is the same moving crossing in `Hn (n+1)` and `τ` is
`affineLastCrossing i i n`; with `single_cl_congr`, `cw_range'_succ`,
`appendAlgebra_appendAlgebra_one_eq_sum`, `single_mul_affineLastCrossing`.

Correction to the proposed §4 of `AppendCoordinates.md` (domain only): the crossing
coordinates of `F` live in `e'B`, `e' = ψ'(1)` (old words ending in the appended
colour), not in `B`; `F(u)` only depends on `e'u`. The decomposition is of the two-sided
corner `ψ(1) A ψ(1) = ⊕_(j<n,m) c_j x^m ψ(e'B) ⊕ ⊕_m x^m ψ(B)`.

Next: the dot slide (1) for `τ` and the assembly of `F`, `direct`, `span`.

Consumer: `scripts/NonVacuity/QuiverHeckeHalfTurn.lean`.

### The half-turn on coefficient-extended Homs and `U(K_N) ⊆ I_N` (checked)

`OddMath/QuiverHecke/HalfTurn/CornerIdeal.lean` (`SwappedVacuumCoordinates.md` §§4–5):

- `htPres s t : Hom(s, t) →ₗ Hom(t^rev, s^rev)` (the half-turn on Hom spaces, linear);
  `htPres_diag_mkD`, `htPres_id`, and `htPres_diag_comp`: `U(f ≫ g) = (-1)^{|f||g|} U(g) ≫ U(f)`
  for normal-form diagrams.
- `htCoef s t` on coefficient-extended Homs, `htCoef_sourceCoefficientHom`:
  `U(a ⊗ f) = a ⊗ U(f)`, no coefficient sign.
- `htCoef_sandwich`: for homogeneous `α`, `γ` (`CoefParity`) and any `β`,
  `U(α⊗A ≫ γ⊗B ≫ β⊗C) = ± α⊗U(C) ≫ γ⊗U(B) ≫ β⊗U(A)` with an explicit sign. The coefficients
  keep their places, so no supercommutativity of `SYM` is used.
- `htPres_lastDotPower`: `U(y_last^j) = (-1)^{p(i) C(j,2)} y_first^j` on `v ++ [i]`.
- `coefParity_factorCoefficient`: `c_{i,j}` has parity `(N + j) p(i)`;
  `elvCoefficientIdeal_le_homogeneousSpan`: `J_N` is spanned by its homogeneous elements.
- `coef_induction`: coefficient-extended Homs are spanned by `α ⊗ mkD ls` with `α` homogeneous.
- **`htCoef_transformedIdeal_le`**: `(TransformedIdeal D Sc cutoff ∅ s t).map (htCoef s t) ≤
  ELVRelationSpan D (parameterTwist D Sc) cutoff t^rev s^rev`. Generators `J_N` go to themselves;
  the transformed polynomial (4) of colour `i` goes to `±` the first-strand cyclotomic
  (`elvCyclotomic` for odd `i`, `evenCyclotomic` for even `i`), with the sandwich sign
  `N p(i)(|A|+|C|) + |α|(|A|+|C|) + |A||C|` independent of the power `j`
  (`htCoef_cyclotomic_term`, `cyclotomic_sign_identity`).

Consumer: `scripts/NonVacuity/QuiverHeckeHalfTurnIdeal.lean`.

Open obligations for §5: the reverse inclusion `I_N ⊆ U(K_N)` (by the same computation run
from the twisted side, or `U` being an involution up to the parameter twist); `T ≠ ∅` (needs
`T` mapped into the coefficient ideal or carried as extra coefficient generators on the ELV
side); and bijectivity of `htCoef` (inverse half-turn from `parameterTwist`), which would turn
the inclusion into the identification `U(K_N) = I_N`.
