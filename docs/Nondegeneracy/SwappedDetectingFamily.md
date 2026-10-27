# Cofinal bounded observations for the swapped action

**Status: proposed written construction, not a Lean theorem.** Working from
the full deformed factor inputs of `SwappedActionAssembly.md` F1, this note
chooses its remaining data and constructs a detecting observation for each
fixed finite-colour word pair and bound. It does not assume a fused model,
a nonzero word module, or an injective recovery map. The existence and
implementation of the full factor inputs remain a separate claim boundary;
the short cyclotomic top-row identification alone is not that existence theorem.

The mathematical setting is a symmetrizable Cartan superdatum with positive
integral symmetrizers, admissible homogeneous parameters, and a purely even
field k with 2 invertible. Both parities and repeated colours are allowed.
The presentation is Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Definition 1.5, (1.7)–(1.14), as used in
`SwappedActionAssembly.md`. The factor input is the full-ELV extension of the
cyclotomic construction of Kang–Kashiwara–Oh, *Supercategorification of quantum
Kac–Moody algebras*, arXiv:1206.5933v2, §7.1 and the diagram (9.5)
comparison, as specified in `DeformedActionAssembly.md`,
`DeformedMixedBraid.md`, and `DeformedGradedAction.md`. We use those precise
factor models and their specialization maps, not an arbitrary action with
the same weight labels. All assertions below are relative to these factor
inputs; no new source lemma or coefficient-flatness assertion is invoked.

## 1. Quantifiers and an explicit dependency order

Fix a finite alphabet J, retaining the whole original weight group X,
external weight mu, words t,t', and d in the nonnegative integers. Put

    B = d + 2 choose(length(t),2),   N0 = B+1,   m = N0.

For finitely many observations at the same mu replace B by their maximum.
An independently prescribed cutoff lower bound K is met by taking
m=max(N0,K) instead; everything below is unchanged. In particular
N0 is positive even when d=0 and the words are empty. The observation is
fixed before any action or cutoff is chosen. At each i in J write

    H_i = h_i(mu),    h_i = -H_i,
    P_i = 2m + 2 max(-h_i,0),
    N_i = 2m + max(h_i,0) + max(-h_i,0).

Then P_i is positive and even, N_i >= 2m >= N0, and P_i-N_i=H_i.
This is the schedule of `ProbeReachability.md` applied to **-mu**.
In the pairing extension Xhat=X x (J -> Z), choose literally

    LambdaP = (0,P),    LambdaR = (-mu,P).

Their pairings are P_i,N_i and LambdaP-LambdaR=(mu,0). Thus dominance and
weight equality hold simultaneously, including the original coroot-kernel
coordinate. No Chevalley operation, change of E/F, or nonnegative root
expression for mu is used. Odd reservoir levels retain the parity dictated
by H_i; they are not silently replaced by odd cutoffs.

Construct the full reservoir coefficient algebra A_N at these N_i. At odd
i it has chi_(i,1),...,chi_(i,floor(N_i/2)) and delta_i, with the exact
relation delta_i chi_(i,N_i/2)=0 when N_i is positive even. At even i retain
its elementary generators through N_i. Tensor the colour algebras in the
super sense; distinct exterior generators are not identified. This is the
coefficient algebra of `DeformedReservoirBound.md`, not a free exterior
replacement of its positive-even-cutoff quotient.

For **every** positive-degree even coefficient generator c_a of A_N set

    L_a = N0,    T = (c_a^L_a : all a),    Abar = A_N/T.

An empty generator list means T=0. Each coefficient weight w_a is a
positive integer, so L_a w_a >= N0. The quotient is homogeneous for both
integer degree and parity and finite-dimensional. Use this one Abar for
**every content** of the reservoir tower. Neither changing content nor
checking another local relation changes T. The augmentation to k survives
all defining relations and truncations, so Abar is nonzero and 1 survives.

The choices are thus

    (J,mu,t,t',d) -> N0 -> (P,N,LambdaP,LambdaR)
                  -> A_N -> (T,Abar) -> factor towers -> support bounds.

The coefficient algebra necessarily depends on the reservoir cutoffs; what
is chosen first is the required coefficient survival threshold N0, not a
fictitious fixed finite coefficient list independent of N. No later support
bound feeds back into this diagram.

## 2. Probe support and closure exponents are not cutoffs

Specialize the probe factor at odd i to algebra polynomial
(u^2-1)^(P_i/2), and at even i to (u-1)^P_i. Its signed odd dot x satisfies
(x^2+1)^(P_i/2)=0; confusing this signed operator with the algebra generator
would change the specialization. The unit constant terms give invertible
adjacent probe dots, as in `InvertibleDotProbe.md`. At even colours the dot
has unit spectrum. These polynomials need not be integer homogeneous; only
parity homogeneity of the probe is required. Reservoir integer grading is
retained independently. Use the factor's inverse-defined left cups/caps
and the normalized left adjunction of `SignedFTriangle.md` and
`HomSectorTransport.md`, not a newly chosen adjunction gauge.

The selected probe content is **zero**, not a large content to be reached
by induction. Its algebra is T_0=k; the reservoir height-zero algebra is
W_0=Abar. The nonzero object k of T_0 is already at weight -LambdaP.
The Hom sector (b,c)=(0,0) has external weight
LambdaP-LambdaR=(mu,0). This supplies reachability of the required probe
object without asserting that arbitrary positive probe contents are
nonzero. In particular there is no inequality forcing probe content to grow
with a nilpotence exponent. Positive contents needed for the full action
are included with their presented algebras, including any zero ones.

After these choices, `DeformedReservoirBound.md` gives finite integer
support for each reservoir algebra Bbar_c. Choose an integer upper bound
M_c for that support, using M_c=0 if the algebra vanishes. For closures of
colour i at this fixed content choose the independent series exponent

    q_c = 1 + max(0,M_c).

Since d_i>=1, it satisfies **2 d_i q_c > M_c**. Products of q_c positive
closures, even with different colours, have degree at least 2q_c and vanish.
This is the inequality sometimes written 2 d_i N > M_beta: its N is a
*geometric-series length*, not the cyclotomic cutoff N_i or the detection
lower bound N0. Identifying these three integers would introduce a circular
and unnecessary requirement.

M_c may depend on every reservoir cutoff and every truncation power. If a
specified component is indexed by probe content b as well, its reservoir
content c may depend on b. None of this matters: c, the factor presentations,
and their degrees are fixed before q_c is chosen. Probe maps have no role
in the positive reservoir degree estimate. They contribute the prescribed
Koszul signs, not extra reservoir degrees. The same q_c kills dot powers
whose degrees exceed M_c. For a specified finite collection of shifted
kernels or modules, use instead 1 plus the maximum of their nonnegative
degree widths and the required algebra upper bounds. A positive-degree
endomorphism iterated this many times leaves its support. Finite parity
matrices do not alter these reservoir degree estimates.

All finite height windows and finite sector paths are formed from the
already fixed weights, contents and words. Take the maximum of the preceding
exponents over any such finite collection. This does not enlarge a factor
cutoff or create further contents. Rational inverses terminate in powers of
the reservoir variable; higher powers are endomorphisms at the same content,
not additional induction steps. On the whole product weight category use
the componentwise inverse, whose exponent may vary with c, exactly as in
`SwappedActionAssembly.md` §2. There is no uniform bound over an infinite
weight fibre and no need for one. These choices supply F2–F4 from the given
factor construction, including the closure bounds used in its whole
inverses. The conditional assembly therefore supplies the full finite-colour
parity-superaction, without another assumption about fused relations.

## 3. Bounded coefficient survival and literal evaluation

Let F_d be the joint coefficient/affine PBW window of
`SwappedVacuumCoordinates.md`. Its signed reversal identifies the actual
word-Hom corner with the quotient by K_(N,T), not with the standard
first-boundary ideal. Every transformed cyclotomic generator has score at
least N_i, every coefficient relation has weight at least N0+1, and each
truncation generator has weight L_a w_a >= N0. Consequently

    K_(N,T)(t,t') <= ExtendedAtLeast(N0-2 choose(length(t),2)).

Since d+2 choose(length(t),2)<N0, q_K is injective on F_d. This proves
survival in the full coefficient quotient, not just in a polynomial
subalgebra: all cross-colour exterior monomials and the exact top ELV
relations are included in the estimate. In particular bounded coefficient
survival alone follows by taking the empty word. The proof uses the actual
ideal estimate of that note, not flatness under T.

Define the vacuum functor by V(M)=Abar tensor_k M at (0,0), zero elsewhere.
It is nonzero since V(k)=Abar and its unit survives. Every pre raising step
decreases probe content and vanishes on this vacuum; post raising steps
leave probe content zero. Thus only the all-reservoir path survives, with
no parity shift left over. For a displayed word s its value is literally

    V_s(M) = (Bbar_content(s) e_reverse(s)) tensor_k M.

Multiplication and insertion of the corner idempotent give the two inverse
balanced tensor maps. Evaluation of a homogeneous signed module map at that
idempotent gives its corner value; chronological composition contributes
(-1)^(|b||c|). These are the explicit contractions and signed evaluations
in `SwappedActionAssembly.md` (A10)–(A11), not a separately assumed vacuum
identification.

Use the finite-support direct sum of these actual word-Hom spaces for the
cyclic modules, with identity cyclic vector and chronological
postcomposition action. Source endomorphisms act by the same composition,
so the source-composition law is associativity in the constructed action.
For the selected source row t and target t', let coordK be its projection,
evaluation at k and the idempotent, followed by the signed affine inverse.

The two bubble notes give, for all height signs, the substitution theta

    odd:  C_i(z) -> C_i(-z)/(1+z)^(P_i/2),
          delta_i -> (-1)^(N_i+1) delta_i;
    even: E_i(z) -> E_i(-z)/(1-z)^P_i.

It and its triangular inverse preserve F_d and parity on the untruncated
coefficient algebra. They need not preserve J_N or T. Define the normalized
reservoir action on the cyclic module by raw coefficient action composed
with theta. This is an algebra map and equals the source-placed betaSYM
bubble action, by the all-height formulas and the source placement sign.
It is not the unmodified raw-coefficient action.

Write sigma(a tensor f)=(-1)^(|a||f|) a tensor f. Choose a k-linear left
inverse L_d of q_K restricted to F_d, and put

    recover = q_first theta^-1 sigma inclusion(F_d) L_d coordK.

The signed evaluation formula gives q_K(sigma(theta(a) tensor f)) before
extraction. Hence, on the bounded source-coefficient window,

    recover(act(alpha(f))(reservoir(a)(vacuum(t))))
        = q_first(sourceCoefficientHom a f).

The displayed tensor a tensor f is identified with sourceCoefficientHom a f
through sourceTensorEquiv. Source placement followed by affine composition
has the specified Koszul sign; this is the sigma corrected in (A18). Theta
commutes with
sigma, so their inverses cancel in this order. This constructs recovery
only at the chosen pair and degree, over k. It does not assert injectivity
of recover or extend a field-linear splitting to an arbitrary commutative
ring. The resulting data have exactly the roles of
`BoundedCyclicRecovery`, including source composition, normalized elementary
and exterior generators, and bounded affine recovery.

## 4. Detection, boundary cases, and finite witnesses

For a nonzero element in F_d the recovered standard ELV class is nonzero
by the same strict cutoff inequality. Therefore its evaluated morphism
cannot vanish. Neither nonzero word modules nor injectivity of evaluation
was assumed: for each nonzero PBW identity in the chosen window the argument
itself proves that the corresponding word module is nonzero. It applies
also to d=0: identities and crossing-only elements are not assigned zero
recovery. Cutoff-zero factor cases are unnecessary since every selected
N_i,P_i is positive. Empty J gives Abar=k and only the empty-colour case;
all colourwise inequalities are then vacuous and N0 remains positive.

Thus, from the stated full factor inputs, every fixed finite-colour
(mu,t,t',d) has a constructed admissible bounded observation, with no
simultaneous-choice obstruction. The field specialization of the bounded
cyclic recovery consumer gives upward coefficient independence. This is a
written supply of its existence premise, not a Lean instance of that premise
and not a completed formal nondegeneracy theorem.

For an arbitrary colour set use the finite-witness argument of
`SwappedActionAssembly.md` §8. A putative zero relation has a finite
contextual derivation; choose J containing that derivation, its boundaries
and its coefficients, and then perform the construction above. Extra
coefficient factors have augmentations, so inclusion preserves the tested
nonzero coefficient. This does not construct a global arbitrary-colour Hom
action or require the chosen models to be compatible as J grows. The
remaining obligations are full factor existence at the stated scope and
formalization of this written chain; parameter cofinality adds no further
hypothesis to them.
