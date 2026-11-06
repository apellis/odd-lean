# Brundan–Wang–Webster parameters for the odd/mixed presentation

This note plans the Phase 2 extension of the parameter shape. The target generality is
[Brundan–Wang–Webster, arXiv:2505.22929v2](https://arxiv.org/pdf/2505.22929v2), §2.2
and Theorem 5.6. It records the enlarged presentation, its parity constraints, the change
of basis question and the parts of the proof that must be redone. The parameter structure,
the comparison map and (H) are in `OddMath/SKM/BWWScalars.lean` (§4). The statement-level gap is listed in `Phase2Plan.md`, "Comparison with
BWW Theorem 5.6".

Notation. We write `dᵢⱼ = -aᵢⱼ` (the Lean `D.d i j`), `dᵢ` for the symmetrizer
(`sy.d i`), and `u`, `v` for dots on the `i`- and `j`-strand. A dot on an `i`-strand
has degree `2dᵢ` and parity `|i|`. The base ring `k` is purely even and has 2 invertible.

## 1. The two parameter shapes

**BE2 (current `Scalars`).** For `i ≠ j` with `dᵢⱼ ≠ 0`,

    Qᵢⱼ(u, v) = tᵢⱼ u^{dᵢⱼ} + tⱼᵢ v^{dⱼᵢ} + Σ_{0<p<dᵢⱼ, 0<q<dⱼᵢ} sᵢⱼ^{pq} u^p v^q,

and `Qᵢⱼ = tᵢⱼ` when `dᵢⱼ = 0`. Every interior monomial carries dots on both strands.

**BWW.** For `i ≠ j`, with `k = ⊕_{n≥0} kₙ` graded,

    Qᵢⱼ(u, v) = tᵢⱼ u^{dᵢⱼ} + tⱼᵢ v^{dⱼᵢ} + Σ_{0≤r<dᵢⱼ, 0≤s<dⱼᵢ} tᵢⱼ;ᵣₛ u^r v^s,

with `tᵢⱼ ∈ k₀ˣ`, `tᵢⱼ;ᵣₛ = tⱼᵢ;ₛᵣ`, and `tᵢⱼ;ᵣₛ` homogeneous of degree
`2dᵢdᵢⱼ - 2dᵢr - 2dⱼs ≥ 0`. The new monomials are those with `r = 0` or `s = 0`:
the **pure terms** `u^r` and `v^s`, and the constant term.

The coefficient degree of `tᵢⱼ;ᵣₛ` is strictly positive whenever `r = 0` or `s = 0`. This
holds because `dᵢdᵢⱼ = dⱼdⱼᵢ` by symmetrizability, so the degree is `2dⱼ(dⱼᵢ - s) > 0`
for `r = 0`, and similarly for `s = 0`. Consequently:

- **(H) Homogeneous BWW parameters have no pure terms.** For `k = k₀` they are exactly
  the current homogeneous `Scalars`. Phase 1 statements are therefore unaffected, and the
  comparison map below is an equivalence on homogeneous parameters.
- In the Rees family `ReesParameters.scalars`, every pure coefficient carries a
  positive power of `h`. In a truncation `k[h]/(h^N)` it is nilpotent and central.

The BE2 leading terms are the corner case of the same coefficient function. Put
`cᵢⱼ(dᵢⱼ, 0) = tᵢⱼ`, `cᵢⱼ(0, dⱼᵢ) = tⱼᵢ` and `cᵢⱼ(p, q) = sᵢⱼ^{pq}` in the interior.
Then the braid correction in `Presentation.lean` (`braidEq`) is one formula:

    Σ_{p,q} cᵢⱼ(p, q) Σ_{s<p} ± u₁^s v^q u₃^{p-1-s}.

The `tᵢⱼ` sum is its `q = 0, p = dᵢⱼ` term, and the `tⱼᵢ` term contributes nothing
(`p = 0`). The quadratic relation is the sum of `cᵢⱼ(p, q) v^q u^p`. So the presentation
needs only one generic coefficient function supported on the box `[0, dᵢⱼ] × [0, dⱼᵢ]`.

## 2. Parity constraints for odd colours

Each relation must be even. The monomial `u^p v^q` has parity `p|i| + q|j|`. So
`cᵢⱼ(p, q) = 0` unless `p|i|` and `q|j|` are even. This is BE2's (1.6) condition
`sᵢⱼ^{pq} = 0` for `p|i|` odd, together with its mirror through `s_symm`, extended to
`p = 0` and `q = 0`.

- For odd `i`, `dᵢⱼ` is even (`Datum.even_d_of_odd`), so the leading term `u^{dᵢⱼ}` is
  allowed. The allowed pure terms in `u` are `u^r` with `r` even.
- The constant term (`r = s = 0`) is allowed for every parity.
- When `i` and `j` are both odd, all allowed exponents are even. Reordering the dots
  `v^q u^p` therefore costs no sign, and the pure terms have dots on one strand only.
- The sign `ζ(|i|(|j| + s))` in the `braidEq` correction comes from moving an `i`-dot
  across the `j`-strand. The `v^q` factor does not change this sign. The formula is
  expected to hold uniformly in `q`, including `q = 0`. Check this first, against the
  relation-level derivation in `SKM/Rho/Braid.lean` and `QuiverHecke/Realization/BraidEq.lean`.

No other constraint appears. In particular, nothing new is needed for 2 to be invertible.

## 3. Can a change of basis absorb the pure terms?

**Not in general.** The only degree-preserving changes of generators available are:

- rescaling crossings and dots by units, which rescales `cᵢⱼ` monomial by monomial and
  creates no new support;
- for an even colour `i`, the shift `xᵢ ↦ xᵢ + aᵢ` by a central scalar `aᵢ ∈ k_{2dᵢ}`.

The shift preserves the nilHecke and dot-slide relations. It replaces `Qᵢⱼ(u, v)` by
`Qᵢⱼ(u + aᵢ, v + aⱼ)`, and it changes the bubble parameters (`CScalars`) by a
triangular substitution.

A shift has one parameter per even colour. It can cancel the coefficient of `u^{dᵢⱼ-1}`
in one chosen `Qᵢⱼ`, but it cannot cancel the pure terms of degree `≤ dᵢⱼ - 2`, or those of
two different neighbours `j`. Odd colours admit no shift at all, since the base is purely
even and `aᵢ` would have to be odd. So the enlarged shape is a genuine extension, and the
proof has to carry the pure terms.

## 4. Encoding

Following the maintainer's choice, the encoding is a separate structure with a
comparison map, so that the Phase 1 statements are untouched.

- `BWWScalars D k`: the units `t` as in `Scalars`, and a coefficient function
  `c : I → I → ℕ → ℕ → k` on the box with
  - `c i j p q = c j i q p`;
  - the parity vanishing of §2;
  - the corner values `c i j (dᵢⱼ) 0 = tᵢⱼ`;
  - vanishing outside the box and on the remaining box edges;
  - `two_isUnit`.
- `Scalars.toBWW : Scalars D k → BWWScalars D k`, with zero pure terms.
- A presentation `presBWW D Sc'` whose `quadNe` and `braidEq` relations are the single
  sums of §1. The lemma `presBWW_toBWW` identifies `presBWW D Sc.toBWW` with `pres D Sc`,
  relation by relation (the extra summands are zero).
- `BWWScalars.Homogeneous` and `GradedHomogeneous`, and a proof of (H):
  `Homogeneous Sc' → ∃ Sc, Sc' = Sc.toBWW`.

Done in `OddMath/SKM/BWWScalars.lean`: `BWWScalars` (with `c` zero on the diagonal `i = j`,
and `Qᵢⱼ = c i j 0 0 = tᵢⱼ` when `dᵢⱼ = 0`), `ScalarData.toBWW` with
`toBWW_c_of_interior` and `toBWW_homogeneous_iff`, `BWWScalars.toScalars`, and (H) as
`BWWScalars.Homogeneous.toScalars_toBWW` and `Homogeneous.exists_eq_toBWW`. Here
`Homogeneous` is (1.31) on every monomial below the corners. `GradedHomogeneous` and
`presBWW` remain.

Generalize only where the comparison forces it. The relation-level lemmas below are
restated once for the generic coefficient sum. The current `Ioo 0 × Ioo 0` sums are
then rewritten through `presBWW_toBWW`, not edited file by file.

## 5. What must be redone

Counts are for the import closure of `nondegeneracy_of_symmetrizer`
(`VacuumRouteSwappedRightNegative.lean`). That closure has 102 modules that unfold
`Qᵢⱼ`, through `Sc.s` or the `Finset.Ioo 0 (D.dn …)` sums. Across them, about 226
declarations mention `Sc.s` directly. They fall into three kinds.

1. **Formal re-indexing (most of the count).** These are sums over `Ioo 0 dᵢⱼ × Ioo 0 dⱼᵢ`
   whose proof uses only membership in the box:
   - grading (`SKM/Grading`, `QuiverHecke/Grading`, `CoefficientGrading`);
   - parity (`Scalars.parity_of_ne_zero` and about 70 uses);
   - presentation transport (`ScalarChange`, `PsiDescent`, `PsiCrossings`, `Rho/*`);
   - the polynomial action formulas;
   - the universal parameter ring (`UniversalPolynomialParameters`,
     `UniversalParameterFields`).

   With one generic sum lemma these become a rewrite each. The universal ring must
   adjoin the pure variables, as BWW's generic ring does.
2. **Uses of `p > 0` or `q > 0` (about 30 sites in 19 modules).** These are the bubble
   slides (`BubbleSlide*`, `Lemma32`, `Lemma33`, `Lemma33Rot`) and the ELV leading-term
   files. The bubble-slide formulas for distinct colours involve `Qᵢⱼ` only through
   its coefficients. Pure terms add summands with dots on one strand. These must be
   re-derived, but BWW's §2 bubble slides hold for general `Q`, so no new mathematics
   is expected.
3. **Uses of `Qᵢⱼ(u, 0) = tᵢⱼ u^{dᵢⱼ}` (substantive).** Example: the invertibility of
   distinct mixed mates (`SwappedAssembly/Sigma/MixedEntry`, `MixedEntrySourceUnits`,
   `ProbeMixedRelations`). These write `Qᵢⱼ` as `tᵢⱼ u^{dᵢⱼ}` plus a multiple of `v`.
   With pure terms, `Qᵢⱼ(u, 0) = tᵢⱼ u^{dᵢⱼ} + Σ_{r<dᵢⱼ} cᵢⱼ(r, 0) u^r` is no longer a
   unit times a monomial.

   In the Rees route every `cᵢⱼ(r, 0)` has positive coefficient degree. So the extra
   terms lie in level ≥ 1 of the coefficient-degree ideals already used for the
   reservoir windows (`ReservoirWindowIdeal`, `CoefficientIdeal`). An isomorphism that
   is perturbed by morphisms in `h·Hom` remains an isomorphism when `h` is central and
   nilpotent: `A + hB = A(1 + A⁻¹hB)`.

   One generic perturbation lemma therefore handles every such site. Each site must
   still state its ideal to include the coefficient-positive terms, and not only the
   multiples of `v`. About 5–10 declarations are of this kind.

**Not affected:**
- the same-colour relations and the leading units `tᵢⱼ`;
- the cyclotomic quotient data;
- `CScalars`, apart from the transport of §3, which is not used;
- every Phase 1 theorem, by (H).

**Also needed:** the all-even comparison with BWW Theorem 5.6. This means matching
BWW's `Qᵢⱼ` and normalization conventions with BE2's in the even specialization.
That item already belongs to the Phase 2 completion criterion; the enlarged shape
only changes which statement is compared.

## 6. Estimate

- Generic coefficient sum, `BWWScalars`, comparison map and (H): 2–3 PRs.
- Kind 1 rewrites, batched by directory: about 6–8 PRs.
- Kind 2 re-derivations: about 3–5 PRs.
- Kind 3, with one perturbation lemma and the restated ideals: about 2–3 PRs.
- Rees and truncated Rees assembly for `BWWScalars`, and the all-even comparison:
  about 3–4 PRs.

The total is about 16–23 PRs beyond the completion of `TruncatedReesNondegeneracy` for
the current `Scalars`. No step is expected to need a new idea. The risk is concentrated in
kind 3: an invertibility argument that relies on the exact monomial `Qᵢⱼ(u, 0)` outside
the Rees setting, where the perturbation is not nilpotent. Such an argument would need
the graded or filtered form of the statement before it can be reused.
