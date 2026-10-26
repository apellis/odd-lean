# Residual windows in the content-shifted Hom construction

**Status: proposed written calculation, not a Lean theorem.** This gives
all-height coordinates and a leading quotient comparison for the corrected
central mixed matrix. It does not prove that the leading matrix is invertible.
The inputs are the specified factor local inverses, the window calculations in
`ReversedReservoirMatrix.md`, and the comparisons in `HomPrincipalMate.md`,
`HomProbeMatrix.md`, and `HomCentralFeedback.md`. No full fused action or braid
relation is an input or a conclusion.

## 1. Coordinates, including empty windows

Use target-row/source-column matrix multiplication (right to left). In a
component word, `f;g` means first f, then g. Fix reservoir content beta,
reservoir height k, probe height h, and total height H=h-k. Write

```
p=p(i), q=(-1)^p, sigma=p(k+1), kappa=p contentParity(beta),
c(k)=(-1)^sigma e(k), e(k)=1 (k<0), e(k)=q (k>=0),
alpha_n=(-1)^(sigma n p), beta_n=(-1)^(sigma(1+np)) c(k)^-1,
gamma(k)=q^k (k!=0), gamma(0)=q.
```

The symbol beta_n is a scalar, not the content beta. All its subscripts below
are nonnegative. Let X=F_- E_-, Y=E_+ F_+ and use the raw coordinate maps

```
A_s=L_+(z_sigma(K_+Hobj)),  A_t=z_sigma(P_X(Hobj)),
B_s=(-1)^kappa z_kappa(M N S_kappa Hobj);MN(z_kappa Hobj),
B_t=N(xi_kappa(M Hobj)).
```

Here Hobj denotes a Hom object, not the integer H. The A comparisons have
parity sigma; the B comparisons are even. In particular B_s is not the bare
pair of z removals. Throughout, maps between shifted summands are transported
using these maps and their inverses and the homogeneous z lifts, not by
unsigned identifications of underlying modules.

Write U_n:1->X and V_n:Y->1 for the left reservoir dotted cup and cap.
Write u_n:Id->NM and v_n:MN->Id for the probe dotted maps, allowing every
integer n on the probe only. Put j=post(R_B):NM->MN, the principal component
of its specified augmented inverse. Denote its other components by

```
A_n:Id->MN  (0<=n<h),
D_n:NM->Id  (0<=n<-h).
```

These are the postcomposed factor inverse components, not newly chosen maps.
For the reservoir write Psi_+^-1=[f;vtilde] when k>0 and
Psi_-^-1=[f,utilde] when k<0, as in the two cited reservoir notes.
All occurrences of reservoir maps below mean their Hom precomposition maps.
In raw coordinates the complete inverse data are

```
I_A=gamma f,                         I_B=j,
a_A,n=beta_n^-1 utilde_n (k<0),       a_B,n=A_n (h>0),
b_A,n=alpha_n^-1 vtilde_n (k>0),      b_B,n=D_n (h<0).
                                                        (1)
```

Thus a0=diag(a_A,a_B):P0->X0 and b0=diag(b_A,b_B):Y0->N0,
where X0=P_Y+MN, Y0=P_X+NM, and

```
P_A=Fin(max(-k,0)), P_B=Fin(max(h,0)), P0=P_A+P_B,
N_A=Fin(max(k,0)),  N_B=Fin(max(-h,0)), N0=N_A+N_B.
```

These index sets label the parity-completed identity summands, not copies
whose parity has been forgotten. The reservoir profiles before forgetting
integer degree are Y[0,sigma], X[0,sigma+p], with
N_A,n=1[d(1-k+2n),(n+1)p] and
P_A,n=1[-d(1+k+2n),np]. The probe lifts are exactly the z lifts of
`HomProbeMatrix.md` (positive cap targets S_(np), negative cup sources
S_(np), with the corresponding principal S_p). No common integer grading
of the fused action is claimed.

There are no a_A columns at k>=0 or b_A rows at k<=0, and no simultaneous
A_n and D_n windows for the probe. In particular one must not cancel P0
against N0 merely because H=0.

The fused unit and counit are diagonal sector sums and the dot is block
diagonal. Therefore their restrictions, with no binomial expansion, are

```
w_t=[beta_t V_t, v_t]:X0->Id,          0<=t<H  (H>=0),
z_t=[alpha_t U_t;u_t]:Id->Y0,          0<=t<-H (H<=0).
                                                        (2)
```

This follows by restricting the dot power and unit/counit to each sector;
the sector inclusions are even. Formula (2) is the specified fused window,
not a freely chosen row or column. It includes c(k), the output-shift cap
sign, and the xi-normalized probe comparison.

## 2. Exact finite Schur coordinates

Use different letters for the literal corrected central entries:

```
C*= -sum_(r>=0) q^(r+1) alpha_r [v_(-r-1);U_r],
D*=  sum_(s>=0) q^(s+2) beta_s  [V_s;u_(-s-1)],
K*=[0 C*;D* 0]=-q [0 C;D 0].                           (3)
```

The order within brackets is part of the formula. Sums terminate by the
reservoir dot bound on the edges involved. No probe-dot truncation occurs.
These are precisely the corrected literal entries, not the historical K.

Define l=C* j, m=D* I_A, T=m l, and E=(1-T)^-1. The fixed-content closure
argument supplies E=sum_(a<N) T^a for a sufficiently large N depending on
this content. Then direct ordered multiplication gives

```
Ainv=(1+K* I)^-1=[1+l E m, -l E; -E m, E], I=diag(I_A,j).
                                                        (4)
```

Indeed (1-ml)E=E(1-ml)=1; the upper-left equation uses
E-ml E=1, not commutativity of l and m. Set

```
Z_A=C* a_B+l E m C* a_B-l E D* a_A,
Z_B=-E m C* a_B+E D* a_A.                              (5)
```

Each expression denotes a row on P_A+P_B: a_A is zero on P_B and a_B is
zero on P_A. Thus (Z_A,Z_B)^T=Ainv K* a0, and the exact positive residual is

```
S_+ = [ w_A a_A+w_B a_B-w_A I_A Z_A-w_B j Z_B;
        -b_A Z_A;
        -b_B Z_B ] : P0 -> F+N_A+N_B, F=Fin(H).         (6)
```

For the negative residual define similarly

```
Y_A=z_A+l E m z_A-l E z_B,
Y_B=-E m z_A+E z_B.
S_-=[ b_A Y_A, -b_A Z_A;
      b_B Y_B, -b_B Z_B ] : G+P0 -> N_A+N_B,
G=Fin(-H).                                             (7)
```

Equations (1)--(7), including the ordered finite inverses T_+^-1,T_-^-1
inside utilde and vtilde, compute every entry from the factor local data.
For (7), use 1-K*(1+I K*)^-1 I=Ainv; it is the negative Schur formula,
not a sign guessed by reflection. Both (6) and (7) are valid at H=0 and
then have exactly the same P0->N0 matrix. The exceptional gamma(0)=q
is still present in (4)--(7).

## 3. The coefficient ideal and the allowed quotient operation

Fix the homogeneous finite reservoir coefficient quotient used in
`DeformedReservoirBound.md`. Let Z_beta be the graded supercentre of its
reservoir algebra at this fixed content, acting as natural endomorphisms
of the reservoir identity. Let Z_beta,>0 be its positive-integer-degree
part. The degree-zero part is not set to the ground ring.

For residual coefficients use the algebra R generated, in the natural
endomorphisms of the identity Hom functor at the fixed source and target,
by the image of Z_beta and the closed probe words that occur in (6)--(7).
The latter include dotted cups/caps, j,A_n,D_n in well-typed composites.
Equivalently retain their image algebra rather than assuming an injective
external tensor-product description. Reservoir and probe coefficients
supercommute by horizontal interchange. Define

```
J=R Z_beta,>0 R.
```

A matrix congruence means entrywise congruence in this ideal, with the
appropriate parity shifts on its source and target. No quotient of a bare
mixed crossing by an unspecified scalar ideal is intended. Expanding the
finite series in (4) and the finite triangular window inverses expresses
all entries of (6)--(7) in R: each reservoir strand segment closes on the
identity, and the remaining segment is a probe word. Their coefficient
order is retained; moving a reservoir coefficient past a probe coefficient
of parity a contributes its usual Koszul sign.

Positive reservoir coefficients can be gathered together in a product in
R using only that supercommutation. They have positive integer degree, so
J is nilpotent at this fixed content by the upper reservoir degree bound.
This requires neither a grading on R's probe part nor a uniform bound on
a weight fiber. It does not say that arbitrary open reservoir functors
preserve the centre, or that every ideal of an open mixed endomorphism
algebra has this nilpotence property.

The following three contracted patterns vanish modulo J:

```
D* I_A C*,       w_A I_A C*,       D* I_A z_A.           (8)
```

Expand (3) and (2). Their reservoir segments are respectively U_r;f;V_s,
U_r;f;V_t, and U_t;f;V_s, with the coefficients gamma, alpha and beta
unchanged. Every such closure has degree 2d(r+s+1), respectively with
s or r replaced by t, strictly positive. All other maps in each pattern
are probe maps. Thus (8) follows from the definition of J and the same
super-interchange used in the feedback calculation. This argument is
applied after the displayed endpoint contractions, not by declaring the
open map C* itself zero modulo J.

It follows from (4)--(8) and the empty same-sector windows that

```
S_+ = [ (w_A-w_B j D*)a_A,  w_B a_B;
         0,                 -b_A C* a_B;
        -b_B D* a_A,          0 ]                 mod J, (9)

S_- = [ b_A(z_A-C* j z_B), 0,              -b_A C* a_B;
        b_B z_B,         -b_B D* a_A,      0 ]     mod J. (10)
```

For example the possible entry b_A C* j D* a_A has empty source or
empty target: k cannot be both positive and negative. It is not removed
by an assumed identity cancellation. The omitted w_A I_A C* terms are
instead removed by (8). Gamma disappears only from the *leading quotient*
through these positive closures, not by replacing gamma with one.

## 4. Explicit leading matrix and the comparison L H Q

For k>0 let e_j: X->1 be the original right cap with j dots, j<k.
For k<0 let d_j:1->Y be the original right cup with j dots, j<-k.
The names e_j,d_j here are not the probe dot or the scalar e(k).
The ordered window changes of `ReversedReservoirMatrix.md` give

```
a_A=d Q_A, Q_A=T_-^-1 diag(beta_n^-1)           (k<0),
b_A=L_A e, L_A=diag(alpha_n^-1) T_+^-1         (k>0).  (11)
```

Here T_-:Pold->P_A and T_+:N_A->Nold; d:Pold->P_Y and
e:P_X->Nold. Thus Q_A:P_A->Pold and L_A:Nold->N_A.
These are specified invertible changes, not unknown inverse matrices.

For every r,t>=0 the local low-window identities and the positive-degree
quotient give

```
k>0: U_r;e_j = delta_(r+j,k-1)       mod J,
k<0: d_j;V_t = delta_(j+t,-k-1)      mod J.             (12)
```

Below the indicated antidiagonal the maps are zero by the local inverse
relations; on it they are the identity. Above it their reservoir degrees
are respectively 2d(1-k+r+j) and 2d(1+k+j+t), strictly positive.
The equality of dot powers in (12) combines dots on the same strand;
there is no right transpose or triangular-number sign. In particular
T_+,T_- reduce to their antidiagonal permutation matrices, with their
specified homogeneous lifts. This uses actual local identities, not a
bubble generating series.

Here are complete entries of coefficient matrices H_+,H_-. A row or
column with an empty indexing set is simply absent. For an old reservoir
column j<-k put s=-k-1-j; for an old reservoir row j<k put r=k-1-j.
Every probe word below is written in execution order.

H_+:Pold+P_B -> F+Nold+N_B has the following entries:

| row, column | entry |
|---|---|
| F_t, Pold_j | beta_s (delta_(t,s) - q^(s+2) [u_(-s-1);j;v_t]) |
| F_t, P_B,n | A_n;v_t |
| Nold_j, P_B,n | q^(r+1) alpha_r [A_n;v_(-r-1)] |
| N_B,n, Pold_j | -q^(s+2) beta_s [u_(-s-1);D_n] |

All other blocks are zero or have an empty index set.
H_-:G+Pold+P_B -> Nold+N_B has entries:

| row, column | entry |
|---|---|
| Nold_j, G_t | alpha_r (delta_(t,r) + q^(r+1) [u_t;j;v_(-r-1)]) |
| N_B,n, G_t | u_t;D_n |
| Nold_j, P_B,n | q^(r+1) alpha_r [A_n;v_(-r-1)] |
| N_B,n, Pold_j | -q^(s+2) beta_s [u_(-s-1);D_n] |

The j inside a bracket is the principal probe inverse, not a window
index. These entries contain only the probe's *specified* local inverse
components and scalars. In particular no identity coefficient is invented
for a probe closure such as u_(-s-1);j;v_t.

Define the maps, with absent blocks omitted,

```
L_+=diag(1_F,L_A,1_NB), Q_+=diag(Q_A,1_PB),
L_-=diag(L_A,1_NB),     Q_-=diag(1_G,Q_A,1_PB).
```

Then the explicit leading comparisons are

```
S_+ mod J = (L_+ mod J) H_+ (Q_+ mod J),
S_- mod J = (L_- mod J) H_- (Q_- mod J).                (13)
```

Proof: substitute (11) into (9)--(10), expand (3), and use (12).
For instance d_j;D* leaves only s=-k-1-j and has coefficient
q^(s+2) beta_s followed by u_(-s-1); similarly C*;e_j has
coefficient -q^(r+1) alpha_r preceded by v_(-r-1).
No probe map is moved through a reservoir map to make these two
contractions: the reservoir cup and cap are adjacent. This explains both
the minus in the Pold/F block and the plus in the Nold/G block, including
for an even colour. Thus (13) is a concrete factor-coordinate comparison,
not the definition H=L^-1 S Q^-1.

Equivalently, in the new reservoir indexing, cancel the antidiagonal and
reciprocal scalars in (13). Replace s by the new P_A index, r by the new
N_A index, and remove beta_s and alpha_r from the two tables. Every other
entry is unchanged. These are useful particularly at total height zero:

* k=h>0: S:P_B->N_A has entry
  q^(r+1) [A_n;v_(-r-1)], for 0<=r,n<k, modulo J.
* k=h<0: S:P_A->N_B has entry
  -q^(s+2) [u_(-s-1);D_n], for 0<=s,n<-k, modulo J.
* k=h=0: the residual is the empty matrix. This does not extend to the
  two preceding nonempty cases.

## 5. What this comparison does not prove

All maps L and Q are invertible by the already specified finite triangular
window changes. Neither table asserts invertibility of H_+ or H_-.
The local identities for the probe give its finite nonnegative dotted
window pairings; the displayed mixed negative-power pairings are not
identities by those axioms alone without a further calculation. Inverting
these concrete matrices from the localized factor action is the next
obligation. If such an inverse is proved, nilpotence of J can lift it;
feedback nilpotence alone cannot replace that step.

There is no independent residual-inverse hypothesis, new bubble-series
assumption, bare-crossing inverse, or cancellation of equal-sized identity
sums in this calculation. Full fusion relations, coherent integer shifts,
separation and nondegeneracy remain separate. The exact formulas and the
leading comparison are written results only; no Lean build is asserted.
