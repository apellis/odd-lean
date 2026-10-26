# Reservoir closure and the missing identity summands

## Scope and verdict

This audits `NondegeneracyProof.md` at commit
`7e4fbdce5b745357ed761d1d49436f46d0ad02a1`, particularly §5.4.
**The claimed reduction of fused inversion to Lemma β is not established.**
There are two different issues:

* The correctly typed reservoir closure has strictly positive degree. Under
  bounded grading support and a homogeneous factor action, its nilpotence
  has a general proof, given below. No cancellation of fake degree-zero
  bubbles is needed for this closure.
* The diagonal factors in the displayed two-by-two matrix are not invertible
  maps between the displayed objects at nonzero heights. Their inverses
  contain identity-summand rows and columns. Nilpotence of reservoir closures
  does not dispose of those rows and columns. The even reference explicitly
  retains them and proves a separate partial-fraction matrix invertible.

The new general argument below is **proposed for formalization**, not a new
Lean theorem or a proof of the full fusion construction. Statements described
as checked refer to the existing declarations cited explicitly. The precise
remaining obstruction is the all-height residual identity-summand matrix,
including its super shifts and its comparison with the fused dotted windows.

## 1. Types before inverses

Use right-to-left composition. Put `X = EF 1_λ`, `Y = FE 1_λ`, and suppress
but do not discard grading and parity shifts. In the draft's Rouquier
convention the augmented isomorphisms have shapes

```
h ≥ 0:  ρ₊ = [σ; v₀; …; v_(h−1)] : X → Y ⊕ P,
h ≤ 0:  ρ₋ = [σ, u₀, …, u_(−h−1)] : X ⊕ N → Y.
```

Here `P` and `N` are sums of shifted identities, with respectively `h` and
`−h` summands. In both cases the closure needs the **principal inverse
block** `r : Y → X`:

```
h ≥ 0: r = ρ₊⁻¹ ∘ in_Y,
h ≤ 0: r = pr_X ∘ ρ₋⁻¹.
```

It does not need, and cannot compose with, the full inverse without these
inclusions/projections. Depending on crossing normalization `r` differs
from the named leftward crossing by a sign; this does not affect degree or
nilpotence. The scalar closure is

```
β_(s,r) = v_s ∘ r ∘ u_r : 1_λ → 1_λ.
```

The letter `r` used both as inverse block and as dot index in the draft
should be disambiguated in any formal statement.

Inverse equations immediately give both low-window annihilations:

* `h ≥ 0`: `v_s ∘ r = 0` for `0 ≤ s < h`;
* `h ≤ 0`: `r ∘ u_r = 0` for `0 ≤ r < −h`.

At height zero these windows are empty. These are already checked as
`SuperRouquierLoc.sigL_capD` and `cupD_sigL` in
`OddMath/SKM/RouquierInverseRelations.lean`. They hold irrespective of the
other factor's height. They do **not** say that the principal inverse block
is an inverse to `σ`: its products with `σ` have identity-summand correction
terms.

## 2. A general reservoir nilpotence proof

### Hypotheses

Fix a colour with positive symmetrizer `d`, any integer height `h`, and a
homogeneous graded super action of its Rouquier data. Require:

1. The cups, caps and dots have the BE grading; the augmented Rouquier map
   is a degree-zero isomorphism after the specified shifts.
2. The algebra `C = End(1_λ)` has bounded-above integer grading support.
   Finite dimension over a field implies this, but local finiteness of each
   degree alone does not. No nonnegative-grading hypothesis is necessary.
3. For the feedback application, closures act on the reservoir component
   and supercommute with homogeneous probe operators, with the stated
   Koszul signs. A module realization must identify this action, not merely
   identify the underlying vector spaces.

### Degree and proof

BE, arXiv:1701.04133v2, §1, degree table following (1.31), gives
`deg u_r = d(1+h)+2dr` and `deg v_s = d(1−h)+2ds`.
The principal inverse block has degree zero, because it is the corresponding
block of the inverse of a homogeneous isomorphism of shifted objects.
Consequently

```
deg β_(s,r) = 2d(r+s+1) > 0.
```

This is independent of the sign of `h` and of colour parity. In the library
these input degrees are `gsum_etaL`, `gsum_epsL`, and `gsum_lcrossL` in
`OddMath/SKM/Grading.lean`. The last is the formal leftward generator's
statement; identifying a factor's inverse block with its degree-zero image
remains part of the homogeneous action hypothesis.

Choose an upper support bound `M` for `C`. Every product of `N` closures
has degree at least `2dN`, and therefore vanishes whenever `2dN > M`.
This proves **joint** nilpotence of the closures, not merely separate
nilpotence. Negative degrees elsewhere in the algebra do not invalidate
this product argument. For a finite feedback sum whose other factors are
probe operators, move the reservoir closures together using super
interchange. Each term in its `N`th power has such a vanishing reservoir
product; the intervening signs cannot change zero. Thus that *specified*
feedback is nilpotent.

A suitable future Lean target is
`SuperRouquierLoc.reservoirClosure_products_eq_zero_of_degree_bound`, with
an evaluated graded action and an explicit support bound. It should conclude
vanishing of products of closures, avoiding an unnecessary ordinary-centre
interface. This is a suggested declaration name, not an existing one.

### What this does and does not prove

This proves the needed reservoir nilpotence assertion **under the above
explicit graded hypotheses**. It does not prove those hypotheses for the
proposed deformed cyclotomic action, nor identify the true all-height Schur
feedback with the draft's expression. In particular H1–H3 as written do not
explicitly include a homogeneous action or finite-dimensional identity
endomorphism algebra. The probe need not be graded for this argument; the
reservoir and its closures do.

The finite-dimensionality needed here can come from a finite-dimensional
reservoir algebra. KLR algebras generally have negative-degree crossings,
so they must not be called nonnegatively graded merely because dots and
coefficient generators have positive degrees. A homogeneous positive-degree
element in a finite-dimensional integer-graded algebra is still nilpotent.
An unbounded polynomial coefficient ring or an exterior algebra on
infinitely many generators is not finite-dimensional; one needs a finite
coefficient window or an explicit substitute bound.

## 3. Centre and radical: two corrections

In a super setting homogeneous endomorphisms of the identity supercommute.
They need not belong to the **ordinary** centre of the underlying algebra.
For example, in an exterior algebra on two odd generators over a field of
characteristic different from two, either generator anticommutes with the
other and is not ordinarily central. The correct module-theoretic target
is the supercentre, with its multiplication and parity specified.

The draft's equivalence between radical membership and vanishing degree-zero
component is false even for ordinary commutative finite-dimensional graded
algebras: `K[ε]/(ε²)` concentrated in degree zero has nonzero radical element
`ε` with nonzero degree-zero component. A repaired implication sufficient
here is the positive-degree product proof of §2. No converse is required.
If a radical formulation is desired, first specify the associative
supercentral algebra and prove that the homogeneous closures generate a
nilpotent ideal. Reordering homogeneous generators shows that finitely many
nilpotent supercentral generators generate a nilpotent ideal. One must not
apply the even `endIdCommRing` instance to all super endomorphisms.

## 4. What the even Schur proof actually does

The inspected reference is
`Categorification/TwoRep/RouqCoproduct.lean`, with supporting
`RouqCoproductBubbles.lean`. It does not invert the two bare factor crossings.

* `RouqLoc.cupD_sigL_capD_isNilpotent` proves the even analogue of the
  closure assertion from nilpotent dots and Rouquier relations, without a
  finite-dimensional graded-action assumption. Its preceding identity
  `cupD_sigL_capD` expands a closure into a boundary closure and products
  of oppositely oriented bubbles. `cw_ccw_isNilpotent` handles the latter;
  low-window vanishings handle positive/negative heights and the zero-height
  boundary is treated separately. This is a stronger even reference, not
  an already proved super theorem.
* `isIso_lift_of_schur` retains the signed-height index sets `Pos h` and
  `Neg h`. It proves the large principal block unipotent modulo nilpotent
  closed diagrams, **then** requires invertibility of a residual matrix
  `schurPos`.
* `schur_const_eq` identifies that residual matrix with `crtMatrix`, not
  with an identity matrix. `isIso_lift_teleporter` invokes
  `crtMatrix_exists_inv`; it uses pairwise distinct spectral parameters and
  the identity `sum h⁺ = N + sum h⁻` for total height `N ≥ 0`.
* The residual rows are indexed by `Pos h`, and columns by
  `Fin N ⊕ Neg h`. Even if total height is zero, these sets need not be
  empty: opposite nonzero factor heights leave a genuine square residual
  matrix. Its invertibility is not a consequence of nilpotent β entries.

For two factors with nonnegative heights the fused dotted window is
`0,…,h_A+h_B−1`, not the disjoint union of the two separate low windows
without a proved change of coordinates. For opposite signs one must also
retain the negative-height cup columns. For negative total height a dual
construction is required, with the super-opposite signs checked explicitly.
Thus §5.4's phrase “extended by the dotted caps/cups of the fused height” is
not a definition of invertible diagonal blocks. The cited associative Schur
lemma is correct but its unit hypotheses have not been supplied.

**Local repair versus open work.** Correcting the inverse-block notation and
proving the reservoir degree bound are local repairs. Supplying the actual
all-height residual matrix is additional fusion mathematics already visible
in the even blueprint; the reservoir lemma alone cannot complete A2-b.
No alternative construction or claim of its invertibility is made here.

## 5. Other claims requiring correction or qualification

* **KKO coefficient scope.** KKO-I, arXiv:1206.5933v2, §4 starts with a
  nonnegatively graded commutative coefficient ring with two invertible.
  Section 7.1 allows homogeneous cyclotomic coefficients, with odd-index
  coefficients zero at odd colours; Theorem 9.6 uses these data. Therefore
  “over a field with undeformed homogeneous polynomials” is too narrow a
  description of that theorem. Odd *super* coefficients remain outside
  this cited setup. Section 7.2 gives finite generation over the coefficient
  ring, not unconditional finite dimension over the ground field.
* **Probe scope.** Invertibility of every dot is an additional hypothesis.
  The first cyclotomic relation with unit constant term directly treats
  the first dot; it does not by itself prove that all dots on all contents
  have only the proposed nonzero spectrum. KKO-I Lemma 7.3 propagates
  polynomial annihilators, not the asserted unipotent spectrum.
* **Homogeneity scope.** §1 states arbitrary admissible parameters, whereas
  the grading argument requires homogeneous parameters, as in BE (1.31)
  and `GeneralRoute.md`. A passage from the homogeneous case to every
  admissible parameter choice is not supplied by that argument.
* **Braid proof, even case.** The proposed gauge can contain cross-colour
  `Q` factors. Their inverses are not supplied by the displayed localization
  at equal-colour differences alone. A comparison in a larger fraction
  algebra, followed by injectivity back into the smaller algebra, could
  repair that particular issue, but must be stated and proved. It is not
  justified by the sentence that the gauge is invertible there.
* **Super matrix algebra.** Odd interchanges are not ordinary even matrix
  units in `L ⊗ Mat_P(K)` without parity shifts on the summands and a
  multiplication comparison. Naturality alone does not construct that
  algebra homomorphism. The odd braid comparison remains open.
* **Cross-sector mixed mates.** An invertible upward map does not have an
  invertible arbitrary partial mate simply by adjunction. The claimed
  interchange-times-polynomial description must be derived with actual
  tensor-factor supports and signed mate rules. This is not a counterexample
  to b1, but its stated bookkeeping caveat is a genuine proof obligation,
  not something deferred solely to Lean engineering.

The conditional detection theorem and the known spanning/reduction results
are not refuted by these findings. No full nondegeneracy proof follows from
the audited draft, and no finite-degree sweep is used in this audit.
