# Bubble moments on the swapped vacuum at positive height

**Status: proposed written derivation, not a Lean theorem.** Assume the
specified full swapped action and its augmented inverse. For an odd colour
at strictly positive external height, the source-placed odd bubble is
`(-1)^(N+1) L_delta`, not uniformly `L_delta`. Here N is the reservoir
cutoff. The even elementary series is `C(-z)/(1+z)^M`, where the probe
polynomial is `(u²-1)^M` and `C(z)=sum chi_r z^r`. The derivation below
uses the prescribed inverse cup and the mate slide, rather than an assumed
bubble normalization. It covers every positive-height cutoff, not just a
bounded list of moments. Nonpositive external heights remain open here.

## 1. Inputs, supports, and scalar conventions

Use `SwappedVacuumCoordinates.md` with the weights chosen at -mu:

    Lambda_P-Lambda_R=(mu,0), h_schedule=-D.h mu,
    V(M)=A tensor_k M_0, extended by zero off formal content zero.

Fix one colour i. Write P for its probe cutoff, N for its reservoir
cutoff, and H=P-N=D.h i mu. In this note H>0. The factor weights at
content zero are k=-P and h=-N. The coefficient algebra A is the full
reservoir quotient, possibly with the finite homogeneous truncation needed
for nilpotence. In particular the odd directions of different colours
remain independent, and at N=2m the relation delta chi_m=0 is retained.

The conditional inverse input is `SwappedHomInversion.md`, in the version
at commit `6f348ac31483097b677fef1a47d49715464c356e`: its central expansion
(4)--(6), whole inverse (13), and support-separated inverse (17). Its full
factor inputs include `DeformedActionAssembly.md` and `InvertibleDotProbe.md`.
No bubble-value assertion is among the inputs used below.

In the intrinsic pre/post coordinates, retain

    q=(-1)^p, sigma=p(k+1),
    c(k)=(-1)^sigma e(k), e(k)=1 for k<0, e(k)=q for k>=0,
    alpha_n=(-1)^(sigma n p),
    beta_n=(-1)^(sigma(1+n p)) c(k)^-1,
    gamma(k)=q^k for k!=0, gamma(0)=q.

In particular pre cups and caps are alpha_n pre(U_n) and
beta_n pre(V_n) after their homogeneous comparisons; their principal
inverse has gamma(k) pre(f_T). The post comparisons are the xi-normalized
ones, not the bare pair of parity removals. At the vacuum betaP=0,
kappa=0. None of these scalars is reassigned to a new dot or adjunction.
The calculation below takes place in the intrinsic shifted modules; hence
these comparisons remain inside the maps rather than being commuted past
odd coefficients. P>0 implies k<0, so no use of a false gamma(0)=1 occurs.

Use functional order for products of maps. On evaluation at the probe
zero-content object k, the mixed source and target reduce to

    X=X_P,             Y=Y_R.

Indeed X_R=B B^right(V)=0, since the post restriction B^right kills
output content zero; Y_P=A^right A(V)=0, since A=pre(E_T) kills V.
Here A,B denote the pre/post raising functors, not coefficient algebras.
The mixed pre/post terms also vanish on evaluation at input content zero:
a post F applied to output content zero is zero, and a pre F evaluates
V on a negative input content. The latter mixed terms need not be zero
functors on positive input contents; no global vanishing is asserted.
The diagonal maps and inverses may be evaluated at k before making this
reduction. This is support in the free content monoid, not weight-root
injectivity.

Consequently the prescribed mate s:X->Y is precisely the pre-to-post
central entry

    s=-sum_(r>=0) q^(r+1) u_R(r) v_P(-r-1).                 (1)

The sum terminates by the reservoir dot bound. Its raw coordinate retains
`-q^(r+1) beta_(-r-1)` and the specified pre comparison. The reverse
central entry does not replace (1). Put u=u_R(0), v=v_P(0), and let x,y
be the inherited dots on X,Y. Their literal mate slide is

    y s-q s x=u v.                                         (2)

This is the same `rouquierMate_slide` used in the candidate inversion,
restricted to the two surviving supports. The full-action hypothesis,
not mere invertibility of an arbitrary matrix, supplies this slide.

For H>0 the augmented matrix and its prescribed inverse are

    F=[s;v;vx;...;vx^(H-1)],       F^-1=[j,a_0,...,a_(H-1)].

Restriction of (13),(17) of the inverse candidate supplies this inverse.
Set a=a_(H-1). Its two needed identities are therefore

    s a=0,             v x^j a=delta_(j,H-1) (0<=j<H).     (3)

Thus a is the extreme inverse column, not a chosen cyclic vector.
All products in (1)--(3) are products of the homogeneous lifted entries;
adjacent parity comparisons cancel, with no permutation of tensor factors.

## 2. The normalized bubbles are inverse-column moments

Define b_l=v x^(H-1+l) a for l>=0, and also for negative l with
H-1+l>=0. Then b_0=1 and b_l=0 for -H+1<=l<0 by (3).
These are endomorphisms of V, with parity lp.

The definitions `etaP`, `bubL`, `bubLs`, `oddBubble`, `betaGen`, and
`betaDGen` identify these moments without a cap/cup normalization premise.
For H>0, etaP is the scalar c_mu times a. Its right dotted cap with
H-1+l dots is v x^(H-1+l). The c_mu inverse in beta and oddBubble
cancels that scalar, without changing composition order. Hence

    odd i:     oddBubble(V)=b_1,       betaSYM(e_r)(V)=b_(2r),
    even i:                            betaSYM(e_r)(V)=b_r,   r>=1. (4)

Here e_r denotes the elementary generator indexed r-1 in Lean. This is
why a forward mate projection is not by itself the bubble calculation:
(4) needs the extreme inverse column a. In particular one cannot discard
the inverse windows in favor of a prescribed coefficient action.

## 3. Odd colour: the polynomial calculation for every cutoff

Suppose p=1, P=2M. The probe algebra relation `(u²-1)^M=0` does NOT
become `(x²-1)^M=0`. For the signed right dot D,

    D^j(z)=(-1)^(j|z|+binom(j,2)) z u^j,

so D²=-R_(u²), and the inherited pre dot satisfies

    (x²+1)^M=0.                                          (5)

The pre shift comparisons preserve this polynomial identity. On Y the
post dot is the reservoir signed right dot; u inserts 1 into its one-strand
module. Its monic defining polynomial, with coefficients on the left, is

    f_N(t)=sum_(r=0)^N (-1)^(N(N-r+1)) c_r t^(N-r),
    c_(2j)=chi_j, c_(2j+1)=delta chi_j, chi_0=1.           (6)

Coefficients beyond the cutoff are zero. At even N=2m, delta chi_m=0;
at N=0, delta=0. Monic division gives the A-basis 1,t,...,t^(N-1)
of this one-strand skew-polynomial quotient (the basis is empty if N=0).
The prescribed full-ELV polynomial is normal; its two-sided ideal is its
principal left ideal. This is the first-strand normality used in
`DeformedIdealSum.md`, not commutativity of an odd dot with A.

Induction from (2), without interchanging maps, gives

    s x^n=q^n y^n s-sum_(j=0)^(n-1) q^(n-j) y^(n-1-j) u v x^j. (7)

Apply s to (5) a and use (3). Since P-H=N, the result is the polynomial
relation in the one-strand reservoir module

    sum_(a0=0)^floor(N/2) binom(M,a0)
      sum_(r=0)^(N-2a0) q^(N+1-r) y^(N-2a0-r) u b_r=0.     (8)

A binomial coefficient outside 0<=a0<=M means zero. Terms with powers
of x below H contribute zero by (3), including the constant term when
needed. Formula (8) is valid also for N=0 in the zero one-strand module.

Identify an endomorphism of V with its signed A-module map on A and then
with its value at 1. Write b_r for this value as well. On applying a term
of (8) to 1, with e=N-2a0-r, its coefficient on the left of t^e is

    q^(N+1-r+e r+binom(e,2)) b_r.                         (9)

The e r term is essential: y^e acts on the parity-r coefficient inserted
by u b_r. The leading coefficient of (8) is the unit
lambda=q^(N+1+binom(N,2)). Divide by lambda. Monic division and (6) now
identify all its coefficients: a monic degree-N polynomial vanishing in
the quotient is f_N. In particular for all admissible l,

    (-1)^l sum_(a0+t=l) binom(M,a0) b_(2t)=chi_l,
    (-1)^(l+1) sum_(a0+t=l) binom(M,a0) b_(2t+1)
                                      =(-1)^N delta chi_l. (10)

The sign reductions in (10) follow by inserting e=N-2a0-r into (9):
the exponent relative to lambda is
`2a0(a0-N)+a0-r(r+1)/2`. Modulo two this is l for r=2t and
l+1 for r=2t+1, where l=a0+t. Thus already the first odd coefficient is

    b_1=(-1)^(N+1) delta,                                 (11)

when N>=1. For N=0, (5) and the initial zero window give b_1=0,
in agreement with delta=0. No probe exterior parameter occurs.

It remains to justify that this computes an entire series, not only its
first N coefficients. Applying v x^n to (5) a for every n>=0 gives

    sum_(a0=0)^M binom(M,a0) b_(l-2a0)=0,       l>=N+1,    (12)

where every negative index that occurs lies in the known zero window
-H+1,...,-1. Equation (12) gives all remaining moments successively.
Therefore, as formal series with a central even variable z,

    B_even(z)=sum_(r>=0) b_(2r) z^r=C(-z)/(1+z)^M,
    B_odd(z) =sum_(r>=0) b_(2r+1) z^r
                  =(-1)^(N+1) delta C(-z)/(1+z)^M.         (13)

For even N the apparent top odd numerator coefficient vanishes by the
relation delta chi_(N/2)=0; deleting that relation would invalidate (13).
The denominator comes from (5), has constant coefficient exactly 1, and
has coefficients binom(M,a0). Its formal inverse has coefficients
`(-1)^j binom(M+j-1,j)`. Thus, explicitly for every r>=0,

    b_(2r)=(-1)^r sum_(t=0)^r binom(M+r-t-1,r-t) chi_t.     (14)

This is an all-cutoff formula for P=2M>N, including arbitrary finite
homogeneous reservoir truncations. It has not been proved here for H<=0.

## 4. Even colour

For p=0 let the probe polynomial be `(u-1)^P`, and write the reservoir
polynomial as `sum_(r=0)^N (-1)^r e_r t^(N-r)`, with e_0=1.
There is no signed-square correction. Repeat (7) with q=1 and apply
`(x-1)^P a=0`. Division by the leading coefficient gives

    sum_(a0+t=r) (-1)^a0 binom(P,a0) b_t=(-1)^r e_r

through r=N; the probe recurrence gives zero beyond N. Consequently

    sum_(r>=0) betaSYM(e_r)(V) z^r=E(-z)/(1-z)^P.           (15)

Again the constant term is 1 by the inverse-window identity, not a
normalization choice. Equations (13),(15) retain the raw reservoir
coefficients rather than relabelling a deconvolution as the factor action.

## 5. Source placement on words and bounded recovery

On V the value b is the map L_b. On an upward reservoir word projective
B e_(reverse t), induction applies it to a pure tensor z tensor a with
sign (-1)^(|b||z|). After contraction its value is

    (-1)^(|b||z|) z b a = b z a.

The equality uses supercentrality of b; it does not treat b as an even
scalar. Every upward pre term vanishes by support, so this is precisely
the source-placed bubble on the surviving word functor. On the word-Hom
module of `SwappedVacuumCoordinates.md`, it acts by postcomposition with
this L_b. Distinct exterior generators and their ordered products retain
their independent Koszul signs. Thus (11),(13),(15) are word formulas,
conditional on the specified full action, not only values on one vector.

For a collection of colours all satisfying H_i>0, these formulas specify
a coefficient substitution theta on the *untruncated* polynomial/exterior
algebra. At odd i it sends

    C_i(z) -> C_i(-z)/(1+z)^M_i,
    delta_i -> (-1)^(N_i+1) delta_i;

at even i it sends `E_i(z) -> E_i(-z)/(1-z)^P_i`.
All polynomial images are even and all exterior images retain their
colour, so this respects the polynomial/exterior relations. The inverse
substitution sends C_i(z) to `(1-z)^M_i C_i(-z)` and E_i(z) to
`(1+z)^P_i E_i(-z)`, with the same exterior sign. These assertions follow
by substitution of the central formal variable; each coefficient uses
only finitely many generators. Neither map is asserted to descend to the
finite ELV quotient. For example a translated top coefficient can spoil
its exterior cutoff relation.

Both substitutions preserve the increasing coefficient-weight filtration:
the image of the rth polynomial generator is a unit sign times that
generator plus terms of strictly smaller weight, and exterior weights are
unchanged. Acting trivially on affine diagrams, they therefore preserve
the bounded space F_d in `SwappedVacuumCoordinates.md`. They also commute
with its source-order involution sigma, since coefficient parities agree.
Let coordK, L_d, q_first be the maps constructed there, under its bound
`d+2 choose(length(s),2)<N0`. Its square for the bubble coefficient a
now reads

    coordK(act(alpha(f))(bubbles(a)(vacuum(s))))
                         = q_K(sigma(theta(a) tensor f)).  (16)

Replace the recovery map by

    q_first o theta^-1 o sigma o inclusion(F_d) o L_d o coordK. (17)

Its value on (16) is q_first(a tensor f), because theta and sigma
preserve F_d and L_d splits q_K there. This proves the bounded adjustment
rather than assuming that deconvolution leaves coordinates unchanged.
It uses no raw-A-linearity of recovery and no automorphism of a cyclotomic
quotient. The comparison remains restricted to admissible bounded windows.

## 6. Remaining boundary

The calculation has not evaluated the inverse cap windows for H<0 or the
principal inverse at H=0. At zero height the odd source definition gives
`u_R(0);s^-1;v_P(0)` in execution order, since both its parity sign and
the minus in the leftward crossing occur. A capped forward mate is not
this composite. The candidate inversion supplies s^-1, but its coefficient
extraction still has to be calculated. A positive-height inverse-column
argument cannot simply be relabelled as that calculation.

Accordingly these results do not provide arbitrary-weight normalized
bubbles, a full detection family, fusion, or nondegeneracy. The total-window
API issue is not used as an obstruction to (16)--(17). Infinite-colour
assembly is separate; each coefficient substitution itself is finite on
each generator. The immediate missing calculation is the zero/negative
height inverse-cap analogue of (8)--(12), with the specified parity lifts.
