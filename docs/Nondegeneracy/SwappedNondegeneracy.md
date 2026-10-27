# Nondegeneracy by bounded swapped Hom observations

**Status: full written proof, proposed until checked in Lean.** This is the
canonical theorem-and-proof entrypoint for the swapped Hom construction.
The factor construction, conditional action assembly and bounded detecting
family below compose to a written proof under the hypotheses stated here.
They have not been composed into a Lean proof of nondegeneracy. Older
conditional notes retain their local hypotheses and historical boundaries;
those boundaries are discharged here by the linked constructions, not by
assuming a detecting action exists.

## 1. The theorem and its scope

Let k be a purely even field with 2 invertible. Let D be a compatible
symmetrizable Cartan superdatum with colour set I, weight group X, roots
alpha_i and coroots h_i, and positive integral symmetrizers d_i. The colour
set may be infinite. Let Sc be admissible homogeneous quiver-Hecke
parameters for D: retain their symmetry and prescribed leading units,
the single constant polynomial at disconnected colours, and the separate
odd-exponent support condition

    Q_ij[u^r v^s] != 0  =>  p_i r = p_j s = 0 in Z/2.

Supply cs : CScalars Sc. Explicitly these are units c_(lambda;i) satisfying

    c_(lambda+alpha_j;i) = t_ij c_(lambda;i).

This is the structure in [MoreGenerators.lean](../../OddMath/SKM/MoreGenerators.lean).
It is a hypothesis, not a claim that every Sc on every weight realization
admits such units. In particular no existence assertion is made for
arbitrary collapsed root/weight data.

**Theorem (written).** Under exactly these hypotheses,
`OddMath.SKM.NondegeneracyConjecture cs` holds: for every pair of oriented
words a,b with equal weight, every external weight mu in X, and every
complete unique choice F of reduced matching representatives and
distinguished points, the decorated family has unique finite SYM
coefficients. Equivalently, its expansion map is bijective. The precise
notion of choice and expansion is that of
[Nondegeneracy.lean](../../OddMath/SKM/Nondegeneracy.lean).

There is no finite-type, disconnectedness, distinct-colour, or purely-even
colour restriction. Repeated colours and connected mixed data are included.
The field and symmetrizability hypotheses belong to this proof; this is not
an arbitrary-ground-ring nondegeneracy theorem. No factor-existence,
fused-action, vacuum-identification or recovery predicate is an additional
hypothesis of this final written statement.

## 2. Fix the observation before constructing the factors

First take a finite alphabet J, retaining the entire weight group X.
Fix mu, upward words t,t', and a joint coefficient/affine PBW bound d >= 0.
Following [SwappedDetectingFamily, §1](SwappedDetectingFamily.md#1-quantifiers-and-an-explicit-dependency-order), set

    N0 = d + 2 choose(length(t),2) + 1,     m = N0,
    H_i = h_i(mu),                         h_i = -H_i,
    P_i = 2m + 2 max(-h_i,0),
    N_i = 2m + max(h_i,0) + max(-h_i,0).

Thus P_i is positive and even, N_i >= 2m >= N0, and P_i-N_i=H_i.
The schedule is balanced at **-mu**, not mu. In the pairing extension put

    Xhat = X x (J -> Z),
    alphahat_i = (alpha_i,0),   hhat_i(x,z) = h_i(x)+z_i,
    LambdaP = (0,P),           LambdaR = (-mu,P).

Their pairings are P_i,N_i and LambdaP-LambdaR=(mu,0). As explained in
[ProbeReachability, original weights](ProbeReachability.md#original-weights-extended-weights-and-cover-labels),
the first coordinate preserves even weights in the common coroot kernel.
No quotient of X and no faithful inclusion of presented categories is
required. Extend the supplied units by

    chat_((x,z);i) = c_(x;i).

The shift law holds since alphahat_j=(alpha_j,0). Restriction along
x -> (x,0) therefore retains both the original heights and cs.

Form the full reservoir coefficient algebra A_N. At odd i keep the
independent exterior generator delta_i and all chi_(i,r), including the
relation delta_i chi_(i,N_i/2)=0 when N_i is positive even. At even colours
keep the elementary generators through N_i. Take the super tensor product
of these colour algebras, not an identification of their odd generators.
For every positive-degree even coefficient generator c_a set

    T = (c_a^N0 : all a),     Abar = A_N/T.

Each coefficient weight w_a is positive, so N0 w_a >= N0. Use this **one**
homogeneous quotient on the whole content tower. It is finite-dimensional
and has an augmentation to k; its unit survives. An empty generator list
means T=0. These assertions and the exact quotient/kernel specialization
are proved in [DeformedReservoirBound, §§1–2](DeformedReservoirBound.md#1-hypotheses-and-an-explicit-coefficient-quotient).

## 3. Construct the full factors and the swapped action

The factor input is constructed, rather than postulated:
[DeformedActionAssembly, §§2–6](DeformedActionAssembly.md#2-deformed-equality-93)
identifies the distinct-colour quotient kernel and prescribed mate, constructs
the all-supermodule target, and assembles the full presentation action.
Its same-colour input is the full-ELV top-row, boundary-division and
all-height matrix chain, not the short top-row cokernel alone:
[DeformedCyclotomicTopRow](DeformedCyclotomicTopRow.md),
[DeformedMackeyBoundary](DeformedMackeyBoundary.md),
[DeformedBoundaryDivision](DeformedBoundaryDivision.md),
[DeformedRouquierMatrix](DeformedRouquierMatrix.md), and
[DeformedMatrixComparison](DeformedMatrixComparison.md).
The corrected mixed braid is supplied by [DeformedMixedBraid](DeformedMixedBraid.md).
In these factors E is induction, F restriction, the dot is signed right
multiplication, and crossings are R_tau at unequal colours and -R_tau at
equal colours. The algebra parameters are **parameterTwist Sc**; the action
parameters are **Sc**. The transport and its mixed quadratic calculation
are [DeformedActionAssembly, §6](DeformedActionAssembly.md#6-global-relations-and-the-underlying-presentation-action).
The standard factor grading and its transported adjunction are given in
[§7](DeformedActionAssembly.md#7-transport-to-the-standard-integer-grading)
and [DeformedGradedAction](DeformedGradedAction.md).

Specialize the probe algebra polynomial to (u^2-1)^(P_i/2) at odd i and
(u-1)^P_i at even i. Its **signed action dot** D satisfies
(D^2+1)^(P_i/2)=0 in the odd case. Unit constant terms make the adjacent
probe dots invertible. Its content-zero algebra is T_0=k, already at the
needed weight; no nonzero positive-content probe module is assumed.
Use its inverse-defined normalized left adjunction, not a freely chosen
gauge. These choices are detailed in
[SwappedDetectingFamily, §2](SwappedDetectingFamily.md#2-probe-support-and-closure-exponents-are-not-cutoffs).

The reservoir is the preceding full factor specialized to Abar. Exact
balanced tensor comparisons preserve its maps and both inverse identities.
[DeformedReservoirBound, §§3–5](DeformedReservoirBound.md#3-finite-dimension-at-every-fixed-content)
gives finite integer support at each content c, an upper bound M_c, and
positive closure degree 2d_i(r+s+1). Only now choose

    q_c = 1 + max(0,M_c),       2d_i q_c > M_c.

The analogous maximum of support widths handles a specified finite window
of shifted kernels. This q_c is a terminating-series length, **not** a
cyclotomic cutoff. No support estimate feeds back into P,N or T. Products
of sufficiently many positive closures vanish; componentwise inverses
assemble even if their lengths vary over an infinite weight fibre.

These constructions supply F1–F4 of
[SwappedActionAssembly, §1](SwappedActionAssembly.md#1-fixed-factors-and-literal-weight-categories).
Its categories are the super-enriched products of SFun_k(T_b,W_c) with
weight LambdaP-LambdaR-alpha(b)+alpha(c). Raising is the sum of pre probe
induction and parity-shifted post reservoir induction. The prescribed
crossings and rational inverses are locally finite by
[§2](SwappedActionAssembly.md#2-prescribed-upward-maps-and-local-finiteness).
The [relation dictionary in §3](SwappedActionAssembly.md#3-exact-relation-dictionary),
[whole same-colour inverses in §4](SwappedActionAssembly.md#4-same-colour-inverse-generators-including-height-zero),
and [distinct-colour assembly in §5](SwappedActionAssembly.md#5-distinct-colour-inverses-and-the-conditional-action-theorem)
verify the full presentation. In particular the mixed blocks of s_ij are
U_ji and V_ij. Whole augmented matrices supply all inverse products,
including height zero; principal-block identities alone would not suffice.
Thus the conditional assembly theorem applies with all its inputs supplied.
This is a parity-superaction; an integer grading on the specialized probe
or on the fused action is neither asserted nor needed.

## 4. Evaluate the vacuum and recover the bounded coefficient

At (b,c)=(0,0) set V(M)=Abar tensor_k M and put zero in all other
components. A pre raising step from probe content zero lands in an absent
negative-content component and vanishes. Only the all-reservoir path
survives, with no remaining parity shift.
[SwappedActionAssembly, §6](SwappedActionAssembly.md#6-surviving-vacuum-blocks-are-forced-by-the-construction)
constructs the balanced contractions and evaluation maps:

    V_t(M) = (Bbar_content(t) e_reverse(t)) tensor_k M,
    evaluation(phi_b ; phi_c) = (-1)^(|b||c|) b c.

Use the finite-support direct sum of these word-Hom spaces as cyclic
modules, with identity cyclic vectors and chronological postcomposition.
Source composition is associativity, not an extra action axiom. Let coordK
project to the chosen source row, evaluate at k and the idempotent, and
apply the signed affine inverse. Its quotient ideal is the transformed
last-boundary ideal K_(N,T), not the standard first-boundary ideal.
[SwappedVacuumCoordinates, §6](SwappedVacuumCoordinates.md#6-transfer-of-detection-by-the-actual-ideal-bound)
proves

    K_(N,T)(t,t') <= ExtendedAtLeast(N0-2 choose(length(t),2)).

Therefore q_K is injective on F_d=ExtendedAtMost(t,t',d). The estimate
includes the full coefficient quotient, all exterior monomials, the top
ELV relations and T; it uses no flatness assertion.

The all-height normalized bubble calculation in
[SwappedActionAssembly, (A16)](SwappedActionAssembly.md#all-height-normalized-bubble-corollary)
combines [SwappedVacuumBubbles](SwappedVacuumBubbles.md) and
[SwappedVacuumNonpositiveBubbles](SwappedVacuumNonpositiveBubbles.md).
The factors c_(mu;i) and their inverses cancel in the normalized bubbles;
no additional choice of cs is made. On the untruncated coefficient algebra
it gives the triangular substitution theta:

    odd:  C_i(z) -> C_i(-z)/(1+z)^(P_i/2),
          delta_i -> (-1)^(N_i+1) delta_i;
    even: E_i(z) -> E_i(-z)/(1-z)^P_i.

Its inverse sends C_i(z) to (1-z)^(P_i/2) C_i(-z), E_i(z) to
(1+z)^P_i E_i(-z), and delta_i to the same signed delta_i. Both preserve
parity and the bounded coefficient-weight filtration. They need not
descend to the finite ELV or truncation ideal. Define the reservoir action
on the cyclic module as raw coefficient action composed with theta; it
then equals the source-placed normalized bubble action.

Write x=sourceCoefficientHom a f. The equivalence sourceTensorEquiv itself
identifies a tensor f with x **without a sign**. The ordered source
placement and affine composition introduce the separate involution

    sigma(a tensor f) = (-1)^(|a||f|) a tensor f.

The evaluation and recovery square is
[SwappedActionAssembly, (A18)](SwappedActionAssembly.md#bounded-vacuum-corollary-and-its-separate-consumer),
with its cyclic realization in
[SwappedDetectingFamily, §3](SwappedDetectingFamily.md#3-bounded-coefficient-survival-and-literal-evaluation):

    coordK(act(alpha(f))(reservoir(a)(vacuum(t)))) = q_K(sigma theta(x)),
    recover = q_first o theta^-1 o sigma o inclusion(F_d) o L_d o coordK.

Here L_d is a k-linear left inverse of q_K restricted to F_d, extended
linearly to its quotient target; q_first is the standard untruncated ELV
quotient map. Such a splitting exists over the field k. Since theta and
sigma preserve F_d and commute, L_d cancels q_K on the displayed image,
sigma^2=1, and theta^-1 theta=1. Consequently

    recover(act(alpha(f))(reservoir(a)(vacuum(t)))) = q_first(x)
    whenever x is in F_d.

Linearity extends this identity to the bounded PBW span. Recovery need not
be natural, coefficient-linear, or injective. Neither theta nor sigma is
being asserted to define an automorphism of a finite quotient.

## 5. Detection and arbitrary oriented boundaries

The same strict inequality d+2 choose(length(t),2)<N0 makes q_first
injective on F_d. If a nonzero x in this window had zero upward image,
its observation and recovered class would be zero, contradicting this
injectivity. Every coefficient-affine combination belongs to some F_d.
Hence the upward coefficient map is injective for finite J, at every mu
and every word pair. This is the bounded consumer argument, with its
existence premise supplied by §§2–4, as concluded in
[SwappedDetectingFamily, §4](SwappedDetectingFamily.md#4-detection-boundary-cases-and-finite-witnesses).
Degree zero still evaluates identities and crossing-only elements; there
is no extension that assigns them zero recovery. Empty J gives Abar=k.
Nonzero word modules, when needed for a nonzero coefficient, follow from
this detection argument rather than entering as hypotheses.

For arbitrary I, suppose a nonzero finite coefficient-affine combination
has zero upward image. A zero equality in the presented category has a
finite contextual derivation. Choose finite J containing all colours in
that derivation, including cups/caps that create and remove colours, and
all colours of the tested coefficients. Keep the whole X. By
[SwappedActionAssembly, §8](SwappedActionAssembly.md#8-finite-derivations-suffice-for-arbitrary-colour-detection)
the same derivation is valid in this finite presentation. Coefficient
inclusion under enlargement is split by the augmentation of extra colour
factors; the affine presentation at its fixed content is unchanged. Thus
the tested coefficient stays nonzero. The observation constructed for this
J annihilates the derivation but detects the coefficient, a contradiction.
No faithful finite-colour inclusion of full SKM categories, arbitrary-Hom
base change, or global infinite-colour Hom action has been used.

Finally upward coefficient injectivity gives independence for every
upward matching choice, and source/target descent and inverse mates give
independence for every oriented boundary. Surjectivity is the established
spanning result, so the expansions have unique finite coefficients. This
proves the theorem. The precise formal reductions are recorded below. ∎

## 6. What is formalized, and what remains

The existing Lean reductions are conditional, not implementations of the
constructed detecting models:

* `OddMath.QuiverHecke.upwardCoefficientMap_injective_of_bounded_cyclic_recovery`
  in `BoundedCyclicRecovery.lean` takes, for each d, cutoffs with a common
  strict lower bound and a `BoundedCyclicRecovery` at the selected pair.
  This separate consumer is not included in this documentation tree's Lean
  sources. Its statement is the conditional implication used in §5, not
  a theorem that the required cyclic data exist.
* `OddMath.QuiverHecke.upward_independence_of_coefficientMap` in
  [UpwardMatchingIndependence.lean](../../OddMath/QuiverHecke/UpwardMatchingIndependence.lean)
  takes coefficient-map injectivity at every equal-weight upward pair and
  external weight and yields `WeakMate.UpwardIndependence cs`.
* `OddMath.SKM.nondegeneracy_of_upward_independence` in
  [UpwardNondegeneracyReduction.lean](../../OddMath/SKM/UpwardNondegeneracyReduction.lean)
  takes that upward independence and yields `NondegeneracyConjecture cs`.

The unfinished Lean realization comprises the full-ELV factor action,
the full swapped presentation action and its whole inverses, the vacuum,
normalized bubble and bounded recovery constructions, and the final
composition with finite-witness passage. Existing formalized algebraic
and mate-comparison results are inputs to this work, not a formalization
of the complete written proof above. No new source hypothesis or detecting
model premise is left in the written theorem; its Lean construction remains
unfinished.
