# Swapped vacuum bubbles at nonpositive height

**Status: proposed written proof, not a Lean theorem.** Conditional on the
specified full swapped action, its factor constructions and the augmented
inverse of `SwappedHomInversion.md` at
`6f348ac31483097b677fef1a47d49715464c356e`, the elementary bubble series at
H=P-N<=0 are

    odd:  C(-z)/(1+z)^M,  P=2M,   oddBubble=(-1)^(N+1)L_delta;
    even: E(-z)/(1-z)^P.

Here C(z)=sum chi_r z^r and E(z)=sum e_r z^r use the reservoir's raw
coefficients. This derives the nonpositive case from the inverse cap and
principal windows. It does not infer it by exchanging the positive-height
cup and cap. In particular the exterior image is computed before using
symmetric-function identities.

## 1. Supports and prescribed inverses

Use the vacuum and weights of `SwappedVacuumCoordinates.md`, with probe
input, reservoir output, k=-P, h=-N and external height H=P-N. The full
coefficient algebra has independent exterior generators for the odd
colours. At N=2m retain delta chi_m=0; at N=0 this means delta=0. Work in
any of the permitted finite homogeneous reservoir quotients. All arguments
below commute with these quotients, including quotients that kill some of
the displayed coefficients.

Evaluate the maps at probe content zero. As in
`SwappedVacuumBubbles.md` section 1, the surviving mixed objects are
X=X_P and Y=Y_R; X_R, Y_P and the other mixed supports vanish there.
The inherited probe dot x is a unit when its one-strand object is nonzero;
y is the nilpotent reservoir dot. With q=(-1)^p, u=u_R(0), v=v_P(0),
functional-order multiplication gives the literal maps

    s=-sum_(r>=0) q^(r+1) y^r u v x^(-r-1),
    y s-q s x=u v.                                      (1)

Only reservoir nilpotence terminates the sum. These are not forward mate
caps replacing inverse entries. Retain the intrinsic homogeneous lifts:

    sigma=p(k+1), c(k)=(-1)^sigma e(k),
    e(k)=1 (k<0), e(k)=q (k>=0),
    alpha_n=(-1)^(sigma n p),
    beta_n=(-1)^(sigma(1+n p)) c(k)^-1,
    gamma(k)=q^k (k!=0), gamma(0)=q.

The pre whole inverse and the post right inverse closures are exactly
those of the cited inversion note. Its support-separated inverse (17),
with central recovery (14), restricts for d=N-P>0 to

    F=[s,u,yu,...,y^(d-1)u]: X + 1^d -> Y,
    F^-1=[j;b_0;...;b_(d-1)].                           (2)

Thus b=b_(d-1) satisfies bs=0 and b y^a u=delta_(a,d-1)
for 0<=a<d. For d=0 it supplies j=s^-1, equally from (13) or (14).
Uniqueness below identifies components of this prescribed inverse; it
does not prescribe a different inverse or assume faithfulness. All
compositions cancel adjacent homogeneous comparisons only.

## 2. Signed coefficient extraction on the reservoir

Suppose first N>=1. The one-strand reservoir module is the skew-polynomial
quotient with basis 1,t,...,t^(N-1), by monic division. For an odd colour,

    t a=(-1)^|a| a t,
    f_N(t)=sum_(a=0)^N (-1)^(N a) c_a t^(N-a),
    c_(2r)=chi_r, c_(2r+1)=delta chi_r, chi_0=1.         (3)

This is the same polynomial as the exponent N(N-a+1) convention: the
difference is even. Its normality makes the two-sided quotient the monic
left quotient used for coefficient extraction. For an even colour use
f_N(t)=sum (-1)^a e_a t^(N-a). Let ell be the coefficient of t^(N-1)
in the monic remainder, with coefficients written on the left.

In the odd case y is the signed right dot, so

    y^r(a)=(-1)^(r|a|+binom(r,2)) a t^r.

Define the homogeneous signed A-linear functional lambda:Y->A of parity
N-1 by

    lambda(a t^j)=(-1)^((N-1)|a|+binom(N-1,2))
                    a delta_(j,N-1).                  (4)

For even colour lambda=ell. In either case
lambda y^j u=delta_(j,N-1) for 0<=j<N. This normalization is an identity
of maps on A, not only evaluation at 1: all maps involved are homogeneous
signed A-linear. The notation L_a below uses the same convention.

Put h_l=(lambda y^(N-1+l)u)(1) for l>=0, h_l=0 for l<0.
For odd colour, let R_l=ell(t^(N-1+l)). Its parity is l. Formula (4)
and the signed right-dot power give

    h_l=(-1)^binom(l,2) R_l.                             (5)

Indeed the other exponent is twice (N-1)l plus twice binom(N-1,2).
The sign from applying lambda to a coefficient of parity l is essential.

Monic division of f_N(t)t^(l-1), for l>=1, gives the ordered recurrence

    R_0=1, R_l+sum_(a=1)^N (-1)^(N a)c_a R_(l-a)=0.      (6)

Negative indices mean zero. This uses right multiplication by t^(l-1);
it never moves an odd coefficient through t. At even N the relation
delta chi_(N/2)=0 ensures the exact polynomial identity

    sum_(a=0)^N (-1)^(N a)c_a w^a
                    =C(w^2)(1+(-1)^N delta w).

At odd N it holds without a top exterior relation. Since delta^2=0,
(5)--(6) give the complete formal series

    sum h_(2r) z^r   =1/C(-z),
    sum h_(2r+1) z^r =(-1)^(N+1) delta/C(-z).            (7)

In particular h_1=(-1)^(N+1)delta. For even colour, the same monic
recurrence without signed powers gives sum h_l z^l=1/E(-z).
These are formal inverses of series with constant term 1, not inverses
of coefficients in A. The recurrence proves all coefficients, not just a
finite selection of degrees.

## 3. Identify the extreme inverse cap

Set

    g(T)=(T^2+1)^M (odd, P=2M),
    g(T)=(T-1)^P   (even).

The signed probe dot satisfies g(x)=0. In particular the odd relation
is not (x^2-1)^M=0. Write g(T)=sum g_n T^n, g_P=1. Iterating (1) gives

    y^n s-q^n s x^n
           =sum_(j=0)^(n-1) q^j y^(n-1-j)u v x^j.      (8)

Every nonzero g_n has q^n=1. Consequently

    g(y)s=sum_n g_n sum_(j=0)^(n-1)
                           q^j y^(n-1-j)u v x^j.       (9)

No coefficient or map has been commuted across another. Every reservoir
power on the right is at most P-1.

For d=N-P>0, define b'=lambda g(y). Since P-1<N-1, (9) gives b's=0.
For 0<=a<d, monicity and (4) give

    b' y^a u=delta_(a,d-1).                             (10)

All powers in this check are at most N-1. Thus b'F is exactly the last
coordinate projection of X+1^d. Multiplication by the prescribed F^-1
in (2) proves b'=b, the extreme inverse cap. Neither a rank count nor
an explicit large matrix inversion is needed.

Define its normalized moments K_l=b y^(d-1+l)u, l>=0; K_0=1. Writing
a map also for its value at 1, (7) and b=lambda g(y) now give

    odd:  K_(2r)=sum_(a=0)^M binom(M,a) h_(2r-2a),
          K_(2r+1)=sum_(a=0)^M binom(M,a) h_(2r+1-2a),
    even: K_l=sum_(a=0)^P (-1)^a binom(P,a) h_(l-a).    (11)

Terms with negative h index vanish by (4); every underlying exponent
of y in this negative-height calculation is nonnegative. Therefore

    odd:  sum K_(2r)z^r=(1+z)^M/C(-z),
          sum K_(2r+1)z^r=(-1)^(N+1)delta(1+z)^M/C(-z);
    even: sum K_l z^l=(1-z)^P/E(-z).                    (12)

The definitions `epsP`, `bubR`, `bubRs`, `oddBubble` identify K_l with
c_mu times the right bubble with d-1+l dots. The inverse cap is multiplied
by c_mu^-1 in epsP; these factors cancel in their existing order. Thus
oddBubble=K_1=(-1)^(N+1)L_delta already follows directly, without a
Grassmannian or elementary-series assumption.

## 4. Zero height is a principal-inverse calculation

Now N=P>=1. Applying lambda to (9) leaves just n=P,j=0:

    lambda g(y)s=v,      v j=lambda g(y), j=s^-1.        (13)

This uses the prescribed principal inverse; no inverse cap window exists
at this height. In particular, for odd colour the source definition gives

    oddBubble=v j u=lambda g(y)u=h_1=(-1)^(N+1)L_delta.  (14)

In execution order this is u;j;v. The parity sign in etaP and the minus
in the leftward crossing cancel. Substituting a forward mate would not
prove (13) or (14).

For either parity define K_0=1 and K_l=v j y^(l-1)u for l>=1.
At H=0 the definition of epsP is c_mu^-1 v j, because the leftward
crossing is -j and its defining coefficient is -c_mu^-1. Consequently
these are precisely the normalized right bubbles with l-1 dots. Formula
(13) gives (11) for every l>=1; terms of exponent below N-1 are killed
by lambda. K_0 is the fake-bubble value 1, not a use of y^-1. Thus (12)
holds at zero height as well, including its odd series and odd generator.

At N=P=0, both one-strand objects are zero. All positive-index right
bubbles and the odd bubble vanish, while K_0=1. The formulas reduce to
C=E=1 and delta=0, so remain correct. This is conditional on zero-cutoff
factor objects being among the allowed inputs; the cofinal probe
construction itself chooses positive levels (M>=1 for odd colour).
No extension of that construction to level zero is inferred. Similarly,
P=0<N uses g=1 and the proof of section 3 verbatim whenever its factor
inputs are available. The exceptional gamma(0)=q is never set to 1.

## 5. Elementary images and bounded recovery

The identities `beta_h` and `betaD_h` in `OddMath/SKM/Beta.lean` identify
beta(h_r) with (-1)^r K_r in the even case and (-1)^r K_(2r) in the odd
case. These identities apply under the full-action hypothesis. Using
E_sym(z) H_sym(-z)=1 therefore inverts exactly the first series in (12):

    sum beta(e_r)z^r = E(-z)/(1-z)^P                 (even),
    sum betaD(e_r)z^r = C(-z)/(1+z)^M                (odd). (15)

The equality with `betaDGen` is for e_(n+1), whose raw left-bubble dot
count is 2(n+1)+H-1, not a right-bubble count. This passage through the
complete functions accounts also for the negative/fake left dots. The
odd coefficient image in (14) was established independently of this step.

Source placement on a surviving upward reservoir word sends a homogeneous
bubble value b to the signed map on z tensor a with value
(-1)^(|b||z|)z b a=b z a. Thus the word-Hom action is postcomposition
by L_b. Keep distinct delta_i and their ordered exterior products; their
Koszul signs are not collapsed to one shared exterior parameter.

For any collection of colours in the nonpositive-height range, define
theta on the untruncated polynomial/exterior coefficient algebra by

    odd: C_i(z) -> C_i(-z)/(1+z)^M_i,
         delta_i -> (-1)^(N_i+1)delta_i;
    even: E_i(z) -> E_i(-z)/(1-z)^P_i.

Its inverse is

    odd: C_i(z) -> (1-z)^M_i C_i(-z),
         delta_i -> (-1)^(N_i+1)delta_i;
    even: E_i(z) -> (1+z)^P_i E_i(-z).

Each coefficient uses finitely many generators; substitution of -z proves
both inverse identities. The maps preserve parity and the increasing
coefficient-weight filtration: the rth polynomial image is (-1)^r times
that generator plus lower-weight terms. They act trivially on diagrams
and commute with the source-order involution sigma. No automorphism of
the finite ELV quotient is asserted: a translated top generator need not
preserve delta_i chi_(i,N_i/2)=0.

With coordK, L_d, q_first and F_d as in `SwappedVacuumCoordinates.md`,
the observed square has right side q_K(sigma(theta(a) tensor f)). Under
its bound d+2 choose(length(s),2)<N0, replace recovery by

    q_first o theta^-1 o sigma o inclusion(F_d) o L_d o coordK.

Since theta and its inverse preserve F_d, this returns q_first(a tensor f).
The finite homogeneous truncation remains in q_K; it is not conjugated
into another quotient by theta. The same formula can combine these
nonpositive colours with positive colours if the separate positive-height
calculation is supplied. This note proves only the nonpositive part on
paper. Full factor/action assembly, formalization and nondegeneracy are
not consequences claimed here.
