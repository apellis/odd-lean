# Fixed-weight rank-one separation from deformed cyclotomic actions

This is a source-level argument over a field of characteristic different
from two, using the established one-odd-colour action. It is not a Lean
implementation or a multicolour nondegeneracy proof. It explains why the
rank-one part need not be reconstructed through separated invertible-dot
factors.

## Published inputs and normalization

Use Ebert–Lauda–Vera, *Derived superequivalences for spin symmetric groups
and odd sl2-categorifications*, [arXiv:2203.14153v2](https://arxiv.org/abs/2203.14153).

1. Theorem 4.5 constructs a genuine action on deformed cyclotomic odd
   nilHecke quotients with the odd coefficient retained. Its same-colour
   inversion proof uses (4.16): P(yt)=P(y)(t-2d). The induced Mackey map A
   satisfies only a lower-polynomial-degree defect estimate, not exact
   twisted linearity.
2. The coordinate calculation (4.17) in the proof of Proposition 4.7
   evaluates the vacuum fake bubbles as the coefficients c_i. The
   universal-equivalence conclusion of that proposition is unnecessary
   here; its proof cites existing rank-one nondegeneracy, so we do not use
   that equivalence as an independent nondegeneracy input.
3. Theorem 5.9 with k=ell=m and Remark 5.10 give an A_N-basis
   x_1^(a_1)...x_s^(a_s) tau_w of the s-strand cyclotomic quotient, with
   0<=a_j<=N-j and w in S_s. Here s denotes strand count; the theorem's
   letter m has been renamed to avoid confusion below.

The coefficient algebra is

\[
 A_N=k[\chi_1,\ldots,\chi_{\lfloor N/2\rfloor}]\otimes\Lambda(d)
 /(d\chi_{N/2}\text{ when }N\text{ is even}).
\]

In the standard normalization matched to the ELV action, the vacuum map sends d to the actual
odd bubble and e_r to chi_r. One can check the convention directly from
the trace selecting x^(N-1): in the reservoir notation delta=-d its moment
series is (1-delta t)/(sum_r chi_r t^(2r)). Native `Beta.betaD_h` multiplies
the even moments by (-1)^r, giving the usual complete-symmetric series
1/(sum_r (-1)^r chi_r z^r), hence e_r maps to chi_r. The corresponding
`Beta.betaD_dh` formula sends d h_r to d times the image of h_r.

The source field hypothesis is retained. No automatic extension to every
commutative ground ring is inferred from its graded-dimension arguments.

## Finite relation at a fixed weight

Fix an integer weight lambda and m upward strands. Consider a finite
purported relation

\[
 \sum_{a,w}x^a\tau_w\,\beta_\lambda(p_{a,w})=0.
\]

The p_(a,w) belong to the one-colour coefficient algebra
k[e_1,e_2,...] tensor Lambda(d). Let D bound all individual tail dot
exponents appearing in this finite relation. Give dots and d degree one,
and e_r degree 2r; let W bound the coefficient weights of all monomials in
all p_(a,w). Inhomogeneous coefficients are split into their finitely many
homogeneous pieces. Set H=max(D,W).

Choose N of the same parity as lambda, large enough that

\[
 N>W,\qquad N\geq-\lambda,\qquad
 N\geq\lambda+2(m+H).
\]

Put k=(N+lambda)/2. The object E^k of the lowest-weight vacuum has weight
lambda, so the given relation acts on this object. Its m-strand upward
target is the regular cyclotomic module on k+m strands. In particular,
a zero natural transformation gives a zero cyclotomic algebra element.

## Why the growing number of head strands is harmless

Slide each closed coefficient across the k existing head strands back
to the vacuum. The normalized same-colour bubble-slide formulas have
constant dot term equal to the original coefficient, and every correction
has positive head dot degree. The odd generator slides exactly, with only
the prescribed super sign. Iterating the slides introduces no head
crossings.

The number of summands can grow with k, but their dot degrees cannot grow
without bound. Each generator slide is homogeneous in the positive
half-grading used above. Thus every resulting term satisfies

\[
 \text{total head dot degree}+\text{remaining coefficient weight}
 =\text{original coefficient weight}\leq W.
\]

Since coefficient weights are nonnegative, every head exponent is at most
W, uniformly in k. This degree argument is a mathematical refinement of
the positive-dot slide statement; it is not yet packaged as a native Lean
bound. On each homogeneous monomial, the zero-head coefficient is the original
monomial times its prescribed unit super sign. For an inhomogeneous p this
need not be one scalar multiplying all of p: the map can include the parity
automorphism d |-> -d. It is an injective diagonal map on the coefficient
monomial basis.

The smallest cyclotomic rectangle bound on the k+m strands is

\[
 N-(k+m)=(N-\lambda)/2-m\geq H.
\]

Consequently every head and tail monomial obtained above already lies
inside the published PBW rectangle. No cyclotomic reduction can turn a
positive-head correction into a zero-head term. The tail permutation
fixes the first k positions; no extra permutations are introduced.

## Extracting the coefficient

Take the cyclotomic PBW coordinates with all first k exponents zero and
with permutation equal to the chosen tail permutation. The positive-head
corrections vanish under this coordinate projection. For each tail label,
the remaining coordinate is the vacuum specialization of p_(a,w) composed
with that injective diagonal sign map.

That specialization is injective on coefficient weight at most W. The
first omitted even generator has weight greater than N; for even N the
extra exterior relation d chi_(N/2) has weight N+1. Since N>W, neither can
produce a relation in this window. The ordinary polynomial/exterior
monomial basis of A_N therefore forces every p_(a,w) to vanish.

This yields rank-one upward independence at the fixed weight, given the
published action and PBW basis and the normalized homogeneous slide
identities. It does not assume that a generic endomorphism evaluation is
faithful, that an invertible dot detects d, or that a variable-vacuum
statement alone proves fixed-weight independence.

## Remaining implementation and general-Cartan tasks

The source uses its standard parameter normalization. For arbitrary native
`CScalars`, the rescaling comparison with that source action must still be
constructed; finite checks in the standard normalization do not establish
that comparison. The source-to-native action bridge and the uniform weighted
slide statement remain to be formalized if this argument is imported into
Lean. The repository's positive-dot slide work addresses the latter's
algebraic triangularity. For more than one colour, the key additional
requirement is a coherent deformed cyclotomic action with independently
realized colour coefficients. The rank-one proof does not supply that
mixed-colour categorical construction.

There are also root-system and bound issues beyond rank one. In a fixed
root coset, one cannot assume that moving the vacuum while adding more
head strands gives dominant cyclotomic cutoffs cofinal in every simple
root direction for arbitrary affine or indefinite Cartan data. Moreover,
a general quadratic-in-strand-count cyclotomic bound cannot automatically
handle head length growing linearly with cutoff. The exact rank-one
rectangle is what makes the inequality above work. Highest/lowest tensor
products and Webster-style constructions therefore remain separate,
useful general-Cartan strategies.
