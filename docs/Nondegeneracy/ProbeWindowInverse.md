# Inverting the negative-power probe windows

**Status: proposed written proof, not a Lean theorem.** The headline is an
explicit inverse algorithm for both tables in `HomResidualWindows.md`, at
every pair of heights. Its concrete use is the leading residual inversion
in that note. The comparison with those tables remains conditional on their
stated coordinates and quotient calculation. No fused action is constructed.

The algorithm uses the specified whole probe local inverse, the two
invertible probe dots, and the probe mate slide. It does not require a
cyclotomic Frobenius assertion, a residual inverse, or a nilpotence argument.

## 1. Ordered factor data

In this note only, juxtaposition is functional order: `fg` means first g,
then f. Set X=MN, Y=NM, and write

```
s:X->Y, x:X->X, y:Y->Y, u:1->Y, v:X->1,
u_n=y^n u, v_n=v x^n, q=(-1)^p.
```

These are the raw probe coordinates of `HomProbeMatrix.md`; x and y are
whiskerings of the two adjacent invertible probe dots, not right transposes.
The literal source mate satisfies

```
y s - q s x = u v.                                      (1)
```

This is the execution-order identity `s;y-q[x;s]=[v;u]` supplied by
`SuperRouquierLoc.mate_slide` in `RouquierMate.lean`. In particular s has
not been replaced by the normalized mate `-q s`.

For h>=0 put

```
F=[s;V], V=(v_0,...,v_(h-1))^T, F^-1=[j,A].              (2)
```

For h<0, b=-h, put

```
P=[s,U], U=(u_0,...,u_(b-1)), P^-1=[j;D].                (3)
```

All components in (2),(3) are the specified inverse components, including
j. Thus, for example, `sj=1, sA=0, Vj=0, VA=1, js+AV=1`
in (2), and `js=1, jU=0, Ds=0, DU=1, sj+UD=1` in (3).
At h=0 use (2), with empty V,A and j=s^-1.

The localized factor input already supplies inverse dots on the relevant
edges. Whiskering preserves their two inverse identities, hence supplies
x^-1 and y^-1 here. The polynomial examples in `NondegeneracyProof.md`
are motivation for that input, not a replacement proof of the factor
construction at all contents. No polynomial relation on ker(s) is needed:
ker(s) need not be preserved by x. In particular the argument does not
infer a finite companion module from the local window identities alone.

Every matrix is a matrix between parity-completed sums with the homogeneous
z comparisons of `HomProbeMatrix.md`. Ordered vertical composition has no
additional Koszul multiplier. No two homogeneous factors are commuted,
no dot is transposed, and permutations permute sum labels, not tensor
factors. When shifts change under an odd dot, retain its homogeneous lift
and inverse; adjacent z^-1 z cancel in the two products. This argument does
not forget those shifts or supply a common integer grading.

## 2. Explicit shifted-window inverses

For l>=0, induction on (1), multiplying only in the indicated order, gives

```
s + sum_(r<l) q^(r+1) u_r v_(-r-1) = q^l y^l s x^-l,
s - sum_(r<l) q^(r+2) u_(-r-1) v_r = q^l y^-l s x^l.   (4)
```

For example the first identity at l=1 is `s+q u v_-1=q y s x^-1`;
the second is `s-u_-1 v=q y^-1 s x`. These checks fix both signs.

If h>=0 and 0<=l<=h, let

```
W_l=(v_-l,...,v_(h-l-1))^T, F_l=[s;W_l].
```

Define a row B_l from this window to Y by assigning to its slot with
index `-r-1`, for `0<=r<l`, the component
`q^(l-1-r) u_(r-l)` and zero to its other slots. Then (4) says exactly

```
F x^-l = [q^l y^-l, B_l; 0,1] F_l.
F_l^-1 = x^l [j,A] [q^l y^-l, B_l; 0,1].              (5)
```

Indeed the triangular matrix on the right has inverse
`[q^l y^l,-q^l y^l B_l;0,1]`. Substitution of the first equality
in both orders, using `F^-1 F=1=F F^-1`, proves both inverse products
in (5). No Schur complement is assumed invertible.

If h<0, b=-h, and 0<=l<=b, let

```
U_l=(u_-l,...,u_(b-l-1)), P_l=[s,U_l].
```

Define a column C_l from X to these identity slots by assigning to
slot `-r-1`, for `0<=r<l`, the component
`-q^(l+r+2) v_(r-l)` and zero elsewhere. The second equality of (4) gives

```
y^-l P = P_l T_l,   T_l=[q^l x^-l,0; C_l,1],
P_l^-1 = T_l [j;D] y^l.                               (6)
```

Here `T_l^-1=[q^l x^l,0;-C_l q^l x^l,1]`.
Multiplication by these displayed inverses proves both products in (6).
The restriction l<=h or l<=b is essential: it ensures every correction
slot used in B_l or C_l is present. We never extend an uncorrected window
past that range.

## 3. A finite auxiliary map and its inverse for every height

First work in the **new** reservoir indexing of `HomResidualWindows.md`:
remove its alpha_r and beta_s factors. Write the resulting tables as
Hhat_+, Hhat_-. Put H=h-k and

```
c_r=q^(r+1), d_s=q^(s+2).
```

Define M in the following four cases. All equations specify target
coordinates in terms of source coordinates, so also fix all permutations.
The symbols xi, eta denote X,Y coordinates, respectively. Identity
coordinates are formal summand coordinates, not elements of a chosen
module or a basis of an arbitrary Hom space.

### (a) k>=0, H>=0

M has source X and target Y+F+R, where F has indices t<H and R has r<k:

```
eta=s xi,  f_t=v_t xi,  rho_r=c_r v_(-r-1) xi.
```

Here h>=k. Form the ascending window w with `w_t=f_t` for t>=0 and
`w_(-r-1)=c_r^-1 rho_r`. Then

```
xi=F_k^-1(eta,w).                                     (7)
```

The inverse is (5), not a new matrix inversion.

### (b) k>=0, H<0

Put d=-H=k-h. M has source X+G, t<d, and target Y+R, r<k:

```
eta=s xi-sum_(t<d) u_t g_t,
rho_r=c_r v_(-r-1) xi + (g_r if r<d, otherwise 0).      (8)
```

If h>=0, so d<=k, define

```
a=q^d y^-d (eta+sum_(t<d) u_t rho_t),
w_(d-r-1)=c_r^-1 rho_r                 (d<=r<k),
zeta=F_h^-1(a,w),
xi=x^d zeta,   g_t=rho_t-c_t v_(-t-1) xi (t<d).        (9)
```

The window indices in (9) are exactly -h,...,-1. Substitution of g
into the first row of (8) produces the first correction in (4) with
l=d. Thus (9) solves every row of (8).

If h<0, put b=-h, so d=k+b. Instead define

```
(zeta,z)=P^-1(q^k y^-k (eta+sum_(r<k) u_r rho_r)),
xi=x^k zeta,
g_r=rho_r-c_r v_(-r-1) xi       (r<k),
g_(k+n)=-q^k z_n               (n<b).                 (10)
```

After eliminating g_r for r<k, the first row becomes
`q^k y^k s x^-k xi-sum_(n<b) y^k u_n g_(k+n)`.
This is precisely `q^k y^k P(zeta,z)`. No beyond-window shift is used.

### (c) k<0, H>=0

Put a=-k and d=H=h+a. M has source X+Z, s<a, and target Y+F, t<d:

```
eta=s xi+sum_(s<a) d_s u_(-s-1) z_s,
f_t=v_t xi+(z_t if t<a, otherwise 0).                 (11)
```

If h>=0, so d>=a, set

```
a0=q^a y^a (eta-sum_(s<a) d_s u_(-s-1) f_s),
(zeta)=F^-1(a0,(f_(a+n))_(n<h)),
xi=x^-a zeta,   z_s=f_s-v_s xi.                        (12)
```

Eliminating all z_s changes the top row to the second correction of (4)
with l=a. The remaining cap rows become v_0,...,v_(h-1) on zeta.

If h<0, put b=-h=a-d. Define

```
a0=q^d y^d (eta-sum_(s<d) d_s u_(-s-1) f_s),
(zeta,w)=P_b^-1(a0),
xi=x^-d zeta,
z_s=f_s-v_s xi                         (s<d),
z_(d+n)=d_n^-1 w_(-n-1)                (n<b).          (13)
```

The window w is indexed -b,...,-1. The factor on its column -n-1 is
`q^d d_(d+n)=d_n`; this proves the last line with no parity simplification
other than q^2=1. Formula (6) supplies P_b^-1 explicitly.

### (d) k<0, H<0

Put a=-k, b=-h; then b>a. M has source X+Z+G and target Y:

```
eta=s xi+sum_(s<a) d_s u_(-s-1) z_s
             -sum_(t<b-a) u_t g_t.
```

Compute `(xi,w)=P_a^-1 eta` using (6), and set

```
z_s=d_s^-1 w_(-s-1),   g_t=-w_t.                       (14)
```

Its window is exactly -a,...,b-a-1.

In (7)--(14), substitution proves M followed by the proposed inverse is
the identity. Conversely the eliminations determine all eliminated
coordinates uniquely, and the remaining coordinates are determined by
one of the two-sided inverses (2),(3),(5),(6). Substituting an input into
these formulas therefore returns that same input. This proves the other
product, without dimension cancellation or finite-dimensionality.

## 4. Explicit extraction of the residual inverse

Here is a single extraction rule completing the inverse algorithm. Write
any of the above auxiliary maps in the block form

```
M=[s,B; C,E]: X+L -> Y+T.                              (15)
```

Absent L or T is the empty sum. These B,C,E are read literally from
(7)--(14), not chosen later. In particular B contains **minus** the
nonnegative cups in cases (b),(d). For the original probe h>=0, the
residual in coordinate order (A,L) -> T is

```
R=[C A, E-C j B].                                     (16)
```

Given t, evaluate the explicit M^-1 above on `(0,t)`, obtaining `(xi,e)`.
Then

```
R^-1(t)=(V xi,e).                                     (17)
```

To check both products, the first row gives `s xi=-B e`, hence
`xi=A V xi-j B e`; the second row gives R(V xi,e)=t.
Conversely on input (a,e), M sends `(A a-j B e,e)` to `(0,R(a,e))`.
Its inverse recovers that input, and `V(A a-j B e)=a` by (2).

For h<0 the residual in coordinate order L -> (T,D) is

```
R=[E-C j B; -D B].                                    (18)
```

Given `(t,n)`, evaluate M^-1 on `(-U n,t)`, obtaining `(xi,e)`. Then

```
R^-1(t,n)=e.                                         (19)
```

Indeed jU=0 implies `xi=-j B e`, while D applied to the first row gives
`D B e=-n`. The second row gives `(E-CjB)e=t`.
Conversely M sends `(-j B e,e)` to
`(U D B e,(E-CjB)e)`, since `1-sj=UD`. This is precisely the lifted
output of (18), so the reverse product follows from M^-1 M=1.

These formulas are explicit compositions of the given factor maps and
finite sums. The M^-1 notation in (17),(19) means the algorithms
(7)--(14), not an invocation of an unspecified matrix inverse.

To compare (16),(18) to the candidate tables, order residual coordinates
as follows: positive target (F,R,N_B), negative target (R,N_B), positive
source (P_A,P_B), negative source (G,P_A,P_B); omit empty blocks. Then:

* (a) gives `v_t A_n` and `c_r v_(-r-1) A_n`.
* (b) gives `delta_(rt)+c_r v_(-r-1) j u_t`,
  `c_r v_(-r-1) A_n`, and, when h<0, `D_n u_t`.
* (c) gives `delta_(ts)-d_s v_t j u_(-s-1)`, `v_t A_n`,
  and, when h<0, `-d_s D_n u_(-s-1)`.
* (d) gives `D_n u_t` and `-d_s D_n u_(-s-1)`.

These are every nonempty block of Hhat_+,Hhat_- in functional order.
Thus (17),(19), with the indicated permutations, are their explicit
inverses, and the preceding paragraphs prove both products.

## 5. Zero total height and the original coordinates

At k=h=m>0, let P_rev convert r-indexed entries to ascending indices
`-m,...,-1`, and Cdiag=diag(c_r). The particularly useful formula is

```
Hhat^-1 = V x^m (j B_m+A) P_rev Cdiag^-1.              (20)
```

Here A uses the original slot order 0,...,m-1, paired with the ascending
shifted slot order by n -> n-m in (5). Formula (20) follows from (5),(17).
It inverts the matrix with entries `q^(r+1)[A_n;v_(-r-1)]`.

At k=h=-b<0, let pi_win project the output of P_b^-1 onto its ascending
negative-window slots, and P_rev^-1 restore the s order. Then

```
Hhat^-1 = -diag(d_s^-1) P_rev^-1 pi_win P_b^-1 U.       (21)
```

This inverts `-q^(s+2)[u_(-s-1);D_n]`. It follows from (13),(19)
with d=0. At k=h=0 both residuals are empty.

Finally restore the **old** reservoir indices in the tables. Let
Arow send a new r-coordinate to old row j=k-1-r with multiplier alpha_r,
and Bcol send old column j=-k-1-s to new s with multiplier beta_s.
On other summands use the identity. Then, for either applicable sign,

```
H_table = Arow Hhat Bcol,
H_table^-1 = Bcol^-1 Hhat^-1 Arow^-1.                  (22)
```

This restores c(k), sigma, and every alpha/beta factor exactly as specified
in `HomResidualWindows.md`; none is reset to one. Its L,Q comparison then
has inverse `Q^-1 H_table^-1 L^-1` in the leading quotient. The exceptional
gamma(0)=q is untouched: its disappearance from that quotient is an input
of the preceding comparison, not an extra normalization here. The original
Cartan polynomials Q_ij and both factor actions are unchanged.

## 6. Scope

The whole inverse relations **plus** the mate slide and invertible dots
suffice; inverse relations alone do not justify a shifted window. The
finite formulas above give a basis comparison without a new Frobenius
hypothesis or a polynomial recurrence on an invariant kernel. They apply
to the localized factor data whenever that data has been constructed.
They do not construct missing factor actions or prove their localization.

Lifting the inverse through the nilpotent coefficient ideal still uses the
separate reservoir quotient argument. Source fidelity of that comparison,
full fusion relations, coherent integer shifts, separation and
nondegeneracy remain separate obligations. All results here are proposed
written calculations; no Lean verification is asserted.
