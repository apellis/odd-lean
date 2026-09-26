# odd-lean

A Lean 4 / Mathlib formalization of odd symmetric functions, the odd nilHecke algebra and the odd
Littlewood–Richardson rule, together with machine-checked errata to the source papers.

Sources (numbering refers to these arXiv versions):

- **[EK]** A. P. Ellis, M. Khovanov, *The Hopf algebra of odd symmetric functions*,
  arXiv:1107.5610v2.
- **[EKL]** A. P. Ellis, M. Khovanov, A. D. Lauda, *The odd nilHecke algebra and its
  diagrammatics*, arXiv:1111.1320v1.
- **[E]** A. P. Ellis, *The odd Littlewood–Richardson rule*, arXiv:1111.3932v1.
- **[EQ]** A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2
  (in progress).

The library builds with no `sorry` and no added axioms; the axiom closures of the results contain
only `propext`, `Classical.choice` and `Quot.sound`.

## Status

**[EK], [EKL] and [E] are formalized in full**, with the carve-outs listed below. Every theorem,
proposition, lemma, corollary, displayed equation, worked example and precise remark of the three
papers is a Lean theorem about the library's objects, or, where the printed statement is false, the
printed statement is refuted in Lean and the corrected statement is proved. The false statements, misprints and proof gaps are
listed in [ERRATA.md](ERRATA.md), each with the declarations that refute and correct it. Signs and
conventions are taken exactly as printed; every corrected statement is a separate declaration.

Names below are in `OddMath.Frontier` unless they start with `Diagrams.`, which are in `OddMath`.
Files named `*Audit.lean` restate headline results and print their axioms; `*Controls.lean` and
`OddMath/Tests/*` contain finite checks.

### [EK]

Modules `EK*` (with `ErrataChecksEK*`). Scope and carve-outs:

- Ground ring: [EK] works over an arbitrary commutative ring k. §2.1 (the form, the radical, the
  q-bialgebra Λ′) is formalized for every k and q; from §2.2 on (q = −1) results are proved over ℤ
  and transported to every k (`EKOverK*`, `EKGeneralQBaseChange`, `EKFinalBaseChange`). Where a
  statement needs 2 ≠ 0 in k, or characteristic 0 (§3.2, formalized over every ℚ-algebra), the
  exact hypothesis is proved; see [ERRATA.md](ERRATA.md).
- §2.4: NΛ_q and QΛ_q are realized as Λ′ and the free module on compositions with the quantum
  quasi-shuffle product, in perfect duality; QΛ_q is proved to be a q-bialgebra.
- Omitted: the numerical data tables of the appendix (§5) are not a target. Most of their entries
  are nonetheless checked (the §5.1 tables, the §5.2 table at q = −1 in degree 6, the general-q table
  in degrees ≤ 4, and the Gram determinants in degrees ≤ 6); the factorization of the degree-7 Gram
  determinant is not. The general statements of §5.2 (nondegeneracy over ℚ(q), the degree (5.1)–(5.2)
  and the leading coefficient) are proved in every degree. The intermediate counts in
  Examples 4.4–4.7 are not restated beyond the RSK correspondences themselves.

### [EKL]

Modules for §2 (`EKLSectionTwo*`, `OddSchubertAction`, `CenterCorrected`, `OwlGeneral`, `SchubertBasis`,
…), §§3–4 (`ZeroHecke`, `OnhReflection`, `StrandCrossing`, `Thick*`, `ShuffleLemma`, `Staircase*`,
`MonomialReversal`), §5 (`Cyclotomic*`, `OddGrassmannSchur`, `OddSymmetricLimit`), §6
(`OnhStructure*`, `Categorification`, `GradedK0*`, `QuantumSl2Plus`, `OddCategorification*`,
`OddBialgebra*`, `OddCyclotomicAction*`), ranks 0 and 1 (`SmallRank*`), and `EKLMisc*`, `EKLGaps*`.
Scope:

- Every rank a ≥ 0: statements in rank a = n + 2 live on `NilHeckeAction.Presented n`; ranks 0 and 1
  are covered separately in `SmallRank*`. Coefficients are in ℤ.
- Diagrams are interpreted as elements of the odd nilHecke ring, which acts faithfully on the odd
  polynomial ring; thick calculus is proved in the ring. The diagrammatic presentation itself
  (relations (2.7)–(2.10) and the equivalence with `Presented n`) is in `Diagrams.OddNilHecke`, built
  on [string-diagrams-lean](https://github.com/apellis/string-diagrams-lean).
- §6: K_0 is the Grothendieck group of finitely generated graded projective modules, presented by
  graded idempotent matrices up to Murray–von Neumann equivalence (`GradedK0`). Induction and
  restriction are constructed on all graded idempotents; they give the q-bialgebra structure on
  K_0(ONH) (with braiding parameter q^{-2}) and the U_q(sl_2) action on K_0(ONH^N), identified with
  the integral form of V(N). F is realized as restriction along ONH_a^N → ONH_{a+1}^N followed by a
  grading shift; the odd two-step flag bimodules enter through the corresponding relation in
  OPol_a, not as separately constructed bimodules. The Morita equivalences are equivalences of
  module categories (ungraded, as in the paper); the classification of indecomposable graded
  projectives is stated in the idempotent-matrix model.
- The open question in the corrected form of Lemma 2.18 (whether the conclusion holds for reduced
  words outside the class for which it is proved) is recorded in [ERRATA.md](ERRATA.md).

### [E]

Modules `OddLR*` (with `ErrataChecksE`). Scope:

- Every number of variables N ≥ 0, including the plactic algebra on the infinite alphabet.
- The classical theory of §4.1 is formalized in the q = 1 specialization of [EK]'s Λ, with Schur
  functions defined by Kostka inversion; there is no separate comparison with a Mathlib ring of
  symmetric functions (none exists at the pinned Mathlib).
- Polytopes and cones (§4.3) are over ℝ; lattice-point statements over ℤ.

### [EQ] (partial)

The differential `d(x_i) = x_i²`, `d(∂_i) = 1` is constructed intrinsically on the diagrammatic
category, as the derivation induced by a local derivation compatible with the defining relations,
over any commutative ring; it is then transported to `Presented n` (rank `n+2`). Indices start at
`0`, and `{m} = m mod 2`.

- Compatibility of `δ(dot) = x²`, `δ(crossing) = 1` with the relations:
  `Diagrams.OddNilHecke.compatible`.
- `d(x_i) = x_i²`, `d(∂_i) = 1`, Leibniz (2.3), `d² = 0`, `d` odd: `Diagrams.OddNilHecke.d_x`,
  `d_ψ`, `d_mul_of_mem`, `d_d`, `deriv_mem_homDeg`; on `Presented n`: `Diagrams.OddNilHecke.dONH_dot`, `dONH_crossing`,
  `dONH_mul`, `dONH_dONH`, `dONH_mem_parity`.
- Prop 3.3, intrinsic variant: the ansatz (3.7) is compatible iff `a = 1`, `b = c = 0` (over ℤ):
  `Diagrams.OddNilHecke.ansatz_compatible_iff`. Prop 3.3 as printed concerns the differential induced
  from a dg module `OPol_n(α)`; the formalized statement instead characterizes the local ansatz by
  compatibility with the defining relations. Its linear constraints coincide with (3.9)–(3.10) after
  substituting (3.8).
- Lemma 3.4, (3.13): `Diagrams.OddNilHecke.d_longest`, `dONH_DElem`.
- Lemma 3.5, (3.16) and (3.17): `Diagrams.OddNilHecke.d_idem`, `d_staircase`, `dONH_eqIdempotent`.

## Building

Requires [elan](https://github.com/leanprover/elan). Toolchain `leanprover/lean4:v4.19.0` and Mathlib
`c44e0c8ee63ca166450922a373c7409c5d26b00b` are pinned. The diagrammatic modules depend on
string-diagrams-lean at a pinned revision (see `lakefile.lean`).

```sh
lake exe cache get
lake build
```

## Models used

The code and proofs were produced with AI models under human direction and checked by Lean:

- GPT-6 Astra
- Muse Spark 1.3
- Claude Opus 5.5

## License

Released under the Apache License 2.0; see [`LICENSE`](LICENSE).
