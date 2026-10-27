# Cyclotomic cokernel of the short Mackey column

**Status: proposed written proof; not Lean-checked or independently accepted.**
This identifies the top row needed by the snake argument in
`DeformedMatrixComparison.md`. It does not assert existence of a full action.
The source comparison is KKO I, arXiv:1206.5933v2, diagram (9.5), its
specified kernels and the subsequent description of the maps F and B.
KKO's coefficient setting is narrower; the total-parity extension is proved
below using the preceding deformed balanced resolution.

## 1. Objects and shifts

Use the coefficient algebra, finite compatible supports and parameter
hypotheses of `DeformedSquareResolution.md`. In particular the ground ring
is purely even with 2 invertible, the prescribed leading Q coefficients
are units, and independent odd parameters are retained. At positive even
odd-colour cutoff impose d_j chi_(j,top)=0; at cutoff zero f_j=1 and d_j=0.
No field, domain, flatness or new projectivity assumption is imposed.

Suppose first delta=beta−alpha_i is nonnegative and n=ht(beta)>0. Put

    R=R_A(beta), S=R_A(delta), B=R/I, D=S/I_S,
    H=R_A(beta+alpha_i), e=e(delta,i), f=e(i,delta),
    e_R=e(beta,i), e_L=e(i,beta), p=p(i),
    epsilon=p(N_i+p(beta)), a=p(N_i+p(delta))=epsilon+p.

All parity exponents are modulo two. The symbol phi is TOTAL parity,
including every coefficient in A. Write j_L:S→fRf for the inclusion on
positions 2,...,n and j_R:S→eRe for that on positions 1,...,n−1.
The analogous inclusions of R into H are xi and iota. The ideal I_S acts
by zero on eB: its generators embed in I, including their two-sided
multiples. Thus eB is a left D, right B module.

Our parity shift has c(pi^u b)=pi^u phi^u(c)b and unchanged right action.
The top objects, with integer shifts temporarily suppressed, are

    L1'=R f tensor_(S,j_L) Pi^epsilon(eB),
    L0'=R e tensor_(S,j_R) Pi^p(eB).

These are the kernels in the source diagram, not quotients selected by
rank. The notation involving v and T_i^N in that diagram records the
shifted coefficient module; in balanced coordinates its left twist is
exactly phi^epsilon. Retain q_i^(−2) on L0' and on its cokernel, and the
same resolution shift on L1' as on L1. In ordinary q-degree that shift is
D_beta=(alpha_i|2Lambda−beta). Indeed the lower-height multiplier has
degree D_delta, and the final equal-colour crossing has degree
−(alpha_i|alpha_i), so D_delta−(alpha_i|alpha_i)=D_beta.
All maps below are even after these shifts.

## 2. The two affine column embeddings

Let app(h) be h on the first n positions with a final i spectator. Set

    alpha(h tensor pi^epsilon b)=app(h) tensor pi^epsilon b in L1,
    F(c tensor pi^p b)=iota(c) tau_n tensor b in L0,

where L1=e_R H e_L tensor_R Pi^epsilon B and
L0=e_R H e_R tensor_R B. The right coefficient b is included by xi in
the first formula and by iota in the second. For s in S,
app(h j_L(s))=app(h) xi(j_R(s)); thus alpha respects the stated balance.
For F the disjoint-generator identity is

    iota(j_R(s)) tau_n = tau_n iota(j_R(phi^p(s))).

For affine generators it is distant supercommutation; for an odd scalar
it is supercentrality and |tau_n|=p on this equal-colour corner. Therefore
it also holds for products with arbitrary odd coefficients. This proves
F balance, without treating A as purely even.

Both injections, and their polynomial cokernels, come from affine PBW
before imposing I. Here is the coordinate reason that this assertion
survives tensoring. For the first-position right parabolic, choose minimal
permutation representatives according to the destination of position 1,
with the first-position dot as polynomial coordinate. Those with
destination at most n are precisely the image of

    R f tensor_S eR → e_R H e_L,   h tensor b ↦ app(h)xi(b).

Expand h by the right S PBW basis, and b by the right R coefficient;
concatenate the reduced words. Length additivity gives these PBW words
once each. The remaining destination n+1 gives the long column. Ordering
the dot powers changes only unit Koszul signs. This is a direct sum of
right R modules, including word idempotents, before cyclotomic quotient.
For the second-position comparison use the two parabolic double cosets:
the crossing coset gives F, and the identity coset gives the last-dot
polynomial column. Again concatenated reduced words are PBW coordinates.
Incorporating Pi moves the coefficient by the displayed phi powers.
Tensor these explicit direct-sum isomorphisms with B, not an arbitrary
injective map. This proves alpha and F injective over the given A.

In particular im(alpha) is exactly L1' as the short column of
`DeformedMackeyBoundary.md`: in its left PBW notation these are the
x_(n+1)^l c tau_n ... tau_k terms with k≥2, including the empty string.
The tails tau_n ... tau_k fix position 1; the whole terms need not do so.
Expand c in old PBW words: its permutations fix position n+1, so each
full permutation sends the distinguished first strand to a position at
most n. The omitted k=1 term is the long column extracted by B1.
Changing between the two PBW orientations is triangular dot sliding;
deletion terms remain in the same short span, since subwords of the tail
still fix position 1 and subwords of the old factor still fix position n+1.
Conversely, the adapted d_j v words with j≤n factor through this short span.
Thus this identifies the specified inclusion, not merely an isomorphic
abstract source.

## 3. Restricted multiplier and its balance

Put T_-=tau_1 ... tau_(n−1) and W_-=f_i(x_1)T_- e. The required map is

    P'(h tensor pi^epsilon b)=h W_- tensor pi^p b.          (1)

Its balance is the lower-height P balance with the extra shift p, not
centrality of f_i. In R e tensor_S D, the preceding calculation gives

    j_L(s)W_- = W_- j_R(phi^a(s)) mod R j_R(I_S).         (2)

For scalar s this uses |W_-|=a and total coefficient parity. For dots,
the error is f_i times T_- with one crossing omitted. Its disjoint tail
moves left, leaving an old S factor to the right of f_i. For a crossing
of S, the braid error has the form f_i L C V, with C polynomial and V
a tail of crossings disjoint from L and position 1. Expanding C V by
successive dot slides gives sums u q, with u a subword of V. Move u and
the last-dot powers left; the residual right factor is in S. Every error
is therefore in R j_R(I_S). This is exactly the terminating deletion
calculation of `DeformedGlobalQP.md` §4 at height delta; it permits
repeated colours and retains every coefficient sign. It makes no move
of f_i through a crossing meeting its first strand.

Polynomial balance is included: the dot checks extend by multiplication
to all old polynomials, and each monomial of f_i has the same total parity
p N_i. The ideal computation used for the lower cokernel employs the
normalizer b f_j=f_j rho_j(b), with rho_j(x_1)=x_1−2d_j and rho_j equal
to phi^(p(j)N_j) on coefficients and the disjoint tail. For even odd-colour
cutoff its dot defect is 2 chi_top d_j, zero by the stated relation; for
odd cutoff rho_j also negates d_j. Its inverse translates by
2(−1)^(N_j)d_j. Both fix x_1 squared. These are precisely the normality
hypotheses in `DeformedIdealSum.md`, not an undeformed t-linearity claim.

After tensoring (2) with Pi^p(eB), its main term becomes
h W_- tensor pi^p phi^(a+p)(s)b. Since a+p=epsilon, this is the image
of h tensor pi^epsilon phi^epsilon(s)b. Its error vanishes because I_S
annihilates eB. Hence (1) is well defined and right B-linear.

There is now an exact commutative square on representatives:

    F P'(h tensor pi^epsilon b)
      = app(h) f_i(x_1) tau_1 ... tau_(n−1) tau_n tensor b
      = P alpha(h tensor pi^epsilon b).                  (3)

No braid move, coefficient permutation or repeated-crossing cancellation
is used in (3): it is concatenation of the prescribed words. In particular
there are NO additional deletion terms in the restriction itself. The
only deletion terms needed for its balance are those explicitly accounted
for in (2). Since P, alpha and F are injective by the preceding resolution
and affine embeddings, (3) proves P' injective. This does not infer
injectivity by tensoring the lower-height exact sequence.

## 4. Cokernel and its prescribed crossing map

Apply the written lower-height resolution to the addition of i to delta:

    R f tensor_S Pi^a D --P_delta--> R e tensor_S D → Be → 0,
    P_delta(h tensor pi^a d)=h W_- tensor d.

Its cokernel is the literal corner Be by the lower-height ideal-sum
calculation, not by a projectivity or dimension argument. Tensor on the
right over D with Pi^p(eB). Right exactness applies over the underlying
associative ring; the shifts retain the indicated left twists. The two
canonical associators, with formulas on representatives, are

    (h tensor pi^a d) tensor pi^p b
        ↦ h tensor pi^epsilon phi^p(d)b,
    (c tensor d) tensor pi^p b
        ↦ c tensor pi^p phi^p(d)b.

Their inverses insert d=1. Their D balance follows from the left phi^p
action, and their S balance is phi^p phi^a=phi^epsilon in the first
line. These maps identify the tensored arrow with (1). The target before
quotient is L0' since I_S annihilates eB. Consequently, for the canonical
map q(c tensor pi^p b)=bar(c) tensor_D pi^p b,

    im P'=ker q,
    coker P'=Be tensor_D Pi^p(eB),
    0 → L1' --P'--> L0' --q--> Be tensor_D Pi^p(eB) → 0.  (4)

Only the cokernel calculation used right exactness.

Finally let C=R_A(beta+alpha_i)/I_new and N=e_R C e_R. The middle-row
quotient sends F(c tensor pi^p b) to c tau_n b in N. The inclusion of
the old ideal in I_new makes this independent of the chosen lift of b.
Equation (3) shows that this map kills im P', so (4) induces exactly

    Fbar:Be tensor_D Pi^p(eB) → N,
    Fbar(bar(c) tensor pi^p b)=c tau_n b.                 (5)

Equivalently, lift the first factor to R, apply F, then take the middle
cyclotomic quotient. Surjectivity of q makes this formula unique. It has
the source's total-parity balance and unchanged right B-action; no
unspecified cokernel isomorphism or fused inverse enters. Equations
(3)–(5) give the top row and its right vertical arrow for the snake lemma.

If delta is absent, all short corners and the top row are zero: a short
permutation would leave an i among the old beta strands, which is
impossible. This includes n=0, where no tau_n is defined or used. At
n=1 with delta=0 the lower map is multiplication by f_i in the
one-strand algebra over S=D=A, and T_- is empty. Zero cutoffs and zero
cyclotomic corners are allowed in the argument. Both p=0 and p=1 and
both cutoff parities are covered; no inequality on the weight height
enters (4). The all-height matrix consequence still uses the separate
boundary/division calculation. Written top-row exactness, its future
formalization, and a full deformed action remain distinct claims.
