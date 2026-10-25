# Upward independence and the oriented reduction

The intended statement is: independence of the full upward SKM family over
the abstract algebra `SYM`, for every upward boundary and every weight,
implies independence of the oriented decorated matching family for every
boundary, weight, and permitted choice of representatives. This concerns
Brundan–Ellis, *Super Kac–Moody 2-categories*, §8. Ordinary quiver-Hecke
independence, or independence after specializing bubbles, is insufficient.

This implication is **not yet a Lean theorem**. The new theorem
`OddMath.SKM.OrientedReduction.eq_zero_of_crossing_dot_coefficients`
checks the last finite coefficient argument. It does not assume oriented
independence in a structure field or pretend to construct a closure map.

## What the coefficient theorem proves

Let `A` be the labels consisting of a matching and its complete strand-dot
vector. Give a label its crossing count `c` and total open-dot count `d`.
After identifying the selected output labels with `A`, let `entry i j p`
be the coefficient at output label `i` obtained from input coefficient `p`
at label `j`. The theorem assumes exactly these four conditions:

1. `entry i j p = 0` if `c(j) < c(i)`.
2. At equal crossing counts it is zero if `d(j) > d(i)`.
3. At equal crossing and dot counts it is zero unless `i = j`.
4. The diagonal map reflects zero.

If a finitely supported input has every output coefficient zero, the input
is zero. The input and output coefficient objects can even be different
additive commutative monoids. No coefficient multiplication or positivity
of a coefficient grading is used.

The proof assumes a nonzero finite input, chooses greatest crossing count,
then least dot count among those labels, and reads that one output row.
Every other supported input contributes zero. Its nonzero diagonal
coefficient contradicts the output equation. This avoids constructing an
inverse, normalizing an infinite series, or repeatedly removing terms.

The nonvacuity consumer has two distinct equal-rank labels with opposite
integer coefficients and a lower-crossing input with 100 dots. Its
off-diagonal entries include both lower-crossing errors and positive-dot
corrections. Every theorem hypothesis is discharged. Thus forgetting the
individual matching/dot labels or imposing a global bound on error dots
would weaken an aspect that the consumer exercises.

## Applying it to sorted closure

The proposed [sorted-closure formula](SortedClosure.md) is

\[
 \epsilon_{w,m}\,\tau_w X^{n(m)}
       \rho_R^+(\Theta^{|g_{w,m}|}(p))
 \quad+\quad\text{terms with fewer crossings}.
\]

Here the pairing determines the upward permutation `w`, `n` is the
bijection on full dot vectors induced by moving downward sinks to the
right closing word, and `rho_R` has only nonnegative dot exponents with
constant coefficient the identity. The formula implies conditions 1–4:

- Reduced-word corrections have fewer crossings, regardless of their
  dot counts or bubble coefficients.
- At unchanged crossing count transport only adds dots.
- An added nonzero vector of natural-number dot counts strictly increases
  their total. Consequently equal total counts force the zero added
  vector, and the pairing and full dot vector are unchanged.
- The diagonal is `p ↦ ε Θ^parity(p)`, an additive automorphism of `SYM`.

In particular the argument works with exterior generators and zero
divisors in `SYM`; it is not a scalar leading-monomial argument. It needs
neither invertibility of bubble coefficients nor surjectivity of `rho_R`.

Full upward independence turns a vanishing evaluated closure into the
output equations of the theorem. The closing operation need not be
injective to make this inference: a zero input morphism always has zero
closure. What matters is the comparison on **formal input labels**.

## Remaining constructions

The four coefficient estimates follow from the displayed formula, but the
formula has not been constructed in the native Lean presentation. Its
remaining content must not be replaced by assumptions called
"triangularity" or "closure compatibility" and then reported as the
desired implication.

1. For an adapted strict family, construct the finite equality between
   its literal right closure and the specified upward wiring, using the
   four pitchfork identities, right zigzags, dot slides, and signed
   interchange listed in `SortedClosure.md`. The geometric sweep there
   is a proposed proof of this equality, not a compiled rewrite sequence.
   `MatchingBending.lean` only preserves undecorated pairing classes; it
   does not supply this evaluated equality. Inverse bending an arbitrary
   upward diagram can introduce extra extrema, so strictness cannot be
   obtained by asserting that inverse bending preserves it.
2. Construct full-`SYM` transport, including products of exterior
   generators, its finite support, and its constant coefficient. Only
   the source coefficient moved past the whole original decorated
   diagram receives that diagram's parity involution; the resulting
   bubble is then transported across the right closing word.
3. Construct the source and target contextual sorting maps of
   `SourceContextualSorting.md` and `ContextualSorting.md`, with native
   evaluation intertwiners. Their principal-block and remainder pivots
   then reduce arbitrary boundaries to sorted ones by induction on
   boundary length followed by orientation inversions.

Choice independence, previously a fourth obligation, is now proved by
`MatchingBasisChoice.expansion_injective_choice_iff` in
`MatchingChoiceTransition.lean`. It includes the signed transition and
native evaluation identity. Its lower-dot triangular order differs from
the positive-dot closure order above. The related generic surjectivity
theorem in `MatchingChoiceCoefficients.lean` supports the weakly reduced
inverse-mate route below.

There is no additional algebraic obstruction at the final coefficient
detection step. The remaining difficulty is realizing these diagrammatic
comparisons with the correct local weights, signs, and complete `SYM`
coefficients. The source and target sorting arguments require the
induction hypothesis for all choices at smaller boundaries; one globally
compatible family is not needed.

## Evaluated right-closure steps now checked

`OddMath/SKM/RightClosure.lean` constructs the literal closure on arbitrary
sorted boundaries as both `rightClosureL` (layers) and `rightClosure`
(a linear map on actual SKM morphisms). Its source region is exactly
`wt D μ (ups r)`. `rightClosure_cl` identifies the linear map with the
literal cup/middle/cap list; `sChain_rightClosureL` checks its boundaries.

Three elementary formulas are proved in the quotient presentation, without
upward independence:

- `cl_rightClosure_sigma`: `R(σ_ij)=τ_ij` for every pair of colors, including
  equal odd colors. The proof applies the actual pitchfork at the shifted
  local weight, interchanges an even cup, and cancels a right zigzag.
- `cl_rightClosure_pair`: a right cap-cup with arbitrary one-strand upward
  decorations `A,B` closes to `A` on the right upward strand followed by
  `B` on the left upward strand. In particular this gives
  `R(e_a;H_m)=Y^a;X^m` in the chronological convention of
  `ElementaryClosure.md`. The two decorations are not silently commuted.
- `cl_rightClosure_downward_cap`: closing a cap with `n` dots on its
  downward leg gives `(-1)^(|i| floor(n/2))` times the upward dot power.
  For two odd dots the sign is minus; there is no square-zero conclusion.
  The supporting `cl_rightClosure_cap` treats arbitrary upward cap
  decorations.

`scripts/NonVacuity/RightClosure.lean` applies these results to a concrete
two-color odd datum over `ℚ`, including both distinct and repeated colors,
odd decorations on both resulting strands, and the two-downward-dot sign.
These native calculations discharge local pieces of item 1 above. They do
not yet construct the finite global sweep or the full-SYM transport of
item 2.

Two word-level extensions are now checked in the same module:

- `cl_rightClosure_pairBlocks` treats arbitrary nested cap/cup words and
  arbitrary decorations on each word. The elementary pair theorem is its
  specialization.
- `partialRightMateL` bends a source prefix and a target suffix of any
  layer block. `cl_rightClosure_partialMate` proves that the literal right
  closure recovers that block exactly. The proof is a finite sequence of
  two even block interchanges and two word zigzags. It allows different
  closing words and arbitrary unbent contexts, and does not assume that
  the partial mate is strictly reduced.

This suggests a route around the geometric sweep: use literal partial
mates of reduced upward wirings as a weakly reduced matching family, then
transfer independence to a strict family. Extra extrema prevent simply
calling these representatives strictly reduced. A rigorous version still
needs to realize them in the `TMove` matching syntax, prove weak reducedness
and the pairing/dot-label bijections, and extend the choice comparison to
such a weakly reduced family. The evaluated contraction itself is now
proved; these combinatorial statements are not supplied by it.

The source-prefix half of that combinatorial bridge is now implemented in
`RightMateMatchings.lean`. Iterating literal cup attachment defines
`cupPrefixMatching`, preserves `IsMatching₂` and weak `Reduced₂`, preserves
crossing count, and gives an identity-on-endpoint-numbers strand
equivalence. The associated decorated moves preserve every dot count;
distinguished heights and positions both increase by the prefix length.
`dLay_cupPrefix` identifies the resulting actual decorated layers with
the ordinary cup-prefix layers, and `cl_rightClosure_cupPrefix` recovers
the original evaluated block. No coefficient transport is needed for
this source-prefix-only contraction. The right-target cap attachment is
the remaining half of the partial-mate matching construction.

`RightClosureCoefficients.lean` now supplies native linear maps for that
source-prefix operation. `capPrefixMap_cupPrefixMap` proves an explicit
left inverse on every SKM morphism, and `cupPrefixMap_bubAt` proves exact
compatibility with every rightmost closed coefficient. This applies to
full `SYM`, including inhomogeneous coefficients and ordered products of
distinct exterior generators. The proof expands into ordinary diagrams
only to apply even cup interchange; it assumes no coefficient
independence. Its consumer uses a sum containing a single exterior
generator, a product of two distinct exterior generators, and a polynomial
generator. The right-target operation still needs the nonconstant
one-strand bubble transport.

## Verification

The library theorem is in `OddMath/SKM/OrientedReduction.lean`; its concrete
consumer and axiom prints are in
`scripts/NonVacuity/OrientedReduction.lean`. Scoped compilation is separate
from full CI evidence and does not certify the unimplemented constructions
above.

### Prescribed constant coefficient in full-SYM transport

`PositiveDotTransport.lean` now proves
`betaSYM_exists_positiveDotExpansion`: for every full-SYM coefficient `p`
and every upward color `j`, its left placement is its right placement with
**the same coefficient `p`**, plus a finite sum of strictly positive dot powers
with full-SYM coefficients. The auxiliary `positiveDotExpansion` has domain
`({n : ℕ // 0 < n} →₀ SYM D k)`, so positivity and finiteness are literal.
No upward independence, field, finite-color condition, or specialization of
`t_ij` is assumed.

The proof constructs the actual positive-dot filtration on morphisms.
Composition adds filtration lower bounds and retains super-interchange
signs. Raw bubbles have leading scalar `t_ij`; the defining shift of
`c_(lambda,i)` cancels it for normalized SYM generators. The exterior
generators slide exactly. Free-algebra induction then handles arbitrary
sums and ordered products; finite coefficient extraction uses the existing
range theorem for beta, only for finitely many correction bubbles.

This is a native one-strand coefficient transport theorem, not yet the
complete oriented independence implication. A uniform homogeneous degree
bound for repeated slides is not in this theorem: the last range-lifting
step selects arbitrary preimages of correction bubbles. The rank-one
fixed-weight action strategy must separately retain graded coefficient
lifts or prove the source-level homogeneous formula. The closure route still
needs repeated transport and its evaluation identity for the chosen weak
inverse-mate family, followed by the finite triangular detector.

### Repeated upward-word coefficients

`UpwardWordTransport.betaSYM_exists_positiveWordExpansion` strengthens the
one-strand result to an arbitrary upward word and arbitrary left context.
The error is a finite vector indexed by `PositiveWordDots`: literal nonempty
lists of upward dot layers satisfying the actual boundary chain. Every term
is evaluated as that dot diagram followed by a full rightmost SYM coefficient.
The zero-dot coefficient remains exactly `p`. The proof transports each
one-strand positive error through the remaining suffix and prepends its
positive dots, so the positivity assertion survives every step. The consumer
uses three upward strands, a repeated odd color, a downward left context,
and an inhomogeneous coefficient containing a product of distinct odd generators.
The native repeated-word theorem does not yet assert the entire weak-mate
closure coefficient identity or canonical decorated-label estimates.

### Full coefficients of literal weak mates

`ClosureCoefficientExpansion.rightClosure_partialMate_betaSYM_expansion`
now proves the actual closure identity for an arbitrary layer diagram `A`:
close its literal partial right mate with rightmost coefficient `beta(p)`;
the result is `A` followed by the same rightmost coefficient `beta(p)`,
plus `A` followed by a finite combination of nonempty upward-dot diagrams
and full coefficients. Both cup and cap blocks may be nonempty. The identity
assumes only the actual boundary chain of `A`; it uses no reducedness or
independence premise. Its consumer bends and closes a two-color crossing,
with both blocks nonempty and an inhomogeneous exterior-product coefficient.

The structural lemma `rightClosure_bubAt` holds for every actual morphism
and every closed coefficient. It identifies the intermediate coefficient
region immediately before the appended upward suffix, using interchange
with the even cap block. Applying the repeated-word theorem then supplies
the exact diagonal coefficient `p` and positive-dot errors.

The remaining reduction task is combinatorial and coefficient-level:
identify the complete weak inverse-mate family with the native matching
and decorated APIs, and translate these nonempty dot corrections into the
finite labelled triangular expansion consumed by the upward-independence
detector. The resulting formal implication is still not asserted here.
