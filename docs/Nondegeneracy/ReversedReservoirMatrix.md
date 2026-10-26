# Reversed reservoir windows and the principal-mate obstruction

**Status: written component and matrix calculations, not Lean theorems.**
The height reversal and both finite dotted-window comparisons below are
proved from the existing inverse relations and dot slide. They construct
an augmented isomorphism with the prescribed left dotted windows and a
specified principal entry. They do **not** identify that entry with the
mixed mate of `homContentPreAdjunction`. Thus the reservoir part of (TC)
in `FusedFeedbackComparison.md` remains open. In particular the matrix
constructed below is not asserted to be the Hom Rouquier matrix.

The algebraic window arguments require the same-colour local Rouquier
inversion identities and signed dot slide over the original coefficient
ring. The Hom formulas additionally use the normalized left adjunction
proved on paper in `SignedFTriangle.md`. Integer-degree assertions use the
homogeneous all-symmetrizable factor action and coefficient hypotheses of
`DeformedGradedAction.md`; no integer grading is required on the probe.
No cyclicity, faithfulness, new coefficient commutativity, or bound uniform
over a weight fiber is assumed.

## 1. Boundaries before signs

Use execution order `f;g`. Fix a reservoir content beta, reservoir weight
lambda and height `k=<h_i,lambda>`. Put `d=d_i`, `p=p(i)` and
`sigma=p(k+1)` in Z/2. Around lambda write

```
E_-:lambda-alpha_i -> lambda, F_-:lambda -> lambda-alpha_i,
E_+:lambda -> lambda+alpha_i, F_+:lambda+alpha_i -> lambda,
X=F_- E_-, Y=E_+ F_+.
```
Here products of 1-morphisms are in execution order. Write

```
f:X->Y, R:Y->X, u_j:1->Y, v_j:X->1,
a_j:1->X (0<=j<k), b_j:Y->1 (0<=j<-k)
```
for `sig`, the principal inverse `-sigL`, `cupD j`, `capD j`,
`cupN j`, and `capN j`. A window is empty unless its displayed bound
is positive. The original augmented matrix and its inverse have these
components, with the two five-part inverse identities of
`RouquierInverseRelations.lean`. Neither f nor R is assumed invertible.

On the Hom sector with source `T(lambda)=T(-muP)`, raising by
`homContentPreE` changes this source to `T(lambda-alpha_i)`: the edge
used is E_-, not E_+. Consequently the reservoir contribution to the Hom
weight is `-lambda`, and its height is

```
h_Hom=-k.                                                   (1)
```
This is not the same-height reflection in `SignedFTriangle.md` §4.
That reflection exchanges E and F in a horizontal opposite while retaining
its local object indices; precomposition here retains E and reverses the
weight direction. Equating those two heights loses the identity window.

For a fixed target c let `P_Z(H)=Z H`, with canonical even reassociations.
The Hom mixed source (first lowering, then raising) has underlying word Y;
the mixed target (first raising, then lowering) has underlying word X.
The actual coordinate maps removing their shifts are

```
C_src(H)=homPre(E_+)(z_sigma(homPre(F_+)(H))) : source(H)->P_Y(H),
C_tgt(H)=z_sigma(P_X(H)) : target(H)->P_X(H).                (2)
```
Both have parity sigma and integer degree zero in the graded precursor.
They are homogeneous isomorphisms, not even identifications of unshifted
modules. Their inverses are the indicated inverse z maps. All maps below
can be whiskered with H; the raw formulas are identities of 2-morphisms
at this fixed content, before that whiskering.

## 2. Dotted components and their degrees

Let `U=cupL(k):1->X`, `V=capL(k):Y->1`, and set

```
A=F_- whisker x_-, B=x_+ whisker F_+,
U_n=U;A^n, V_n=B^n;V (n>=0),
c(k)=(-1)^sigma e(k), e(k)=1 if k<0, e(k)=(-1)^p if k>=0.
```
The U component uses the adjunction edge with bottom height k-2; the V
component uses the edge with bottom height k. Their parities coincide,
but substituting c(k-2) for the cap's c(k) is not justified.
`HomSectorTransport.md` gives, with the coordinates (2), exactly

```
cup_H(n);C_tgt = (-1)^(sigma*n*p) P_(U_n),
cap_H(n) = (-1)^(sigma*(1+n*p)) c(k)^(-1) C_src;P_(V_n). (3)
```
Thus all scalar normalizations of the actual windows are known. These
formulas include every n>=0, not only the inverse window.

The piecewise definitions of U,V and the inverse degrees in
`DeformedGradedAction.md` imply

```
deg U=d(1-k), deg V=d(1+k), |U|=|V|=sigma,
deg U_n=d(1-k+2n), deg V_n=d(1+k+2n),
|U_n|=|V_n|=sigma+np.                                    (4)
```
For example, for k>0, U=a_(k-1) has degree
`d(k-1-2(k-1))=d(1-k)`; for k<=0 it is `u_(-k);(-R)`
and has the same degree. For k<0 use V=b_(-k-1); for k>=0 use
`V=R;v_k`. This proves all four branches, including zero. Normalization
signs do not alter integer degrees. Equation (4) agrees with the standard
cup/cap degrees at height -k, not k.

## 3. Positive reservoir height: the whole left cup window

Suppose k>0. Define ordered identity endomorphisms

```
H_(n,j)=U_n;v_j=U;v_(n+j), 0<=n,j<k.                      (5)
```
The equality uses composition of powers on the *same* E_- strand; it
introduces no exchange and no sign. From `cupL_capD`,

```
H_(n,j)=0 if n+j<k-1,  H_(n,j)=1 if n+j=k-1.             (6)
```
Above the antidiagonal retain the actual endomorphism (5). It need not
be replaced by an ordinary central scalar. The dot slide
`cupL_powComp_sig` gives `U_n;f=0` for n<k. Composing U_n with the
original total inverse identity therefore gives the componentwise formula

```
U_n = sum_(j<k) H_(n,j);a_j.                              (7)
```
This determines the entire window, not just the extreme cup. Reverse the
old index by j=k-1-l. The matrix `H_(n,k-1-l)` is lower triangular with
identity diagonal: it is zero for n<l. Hence it is invertible by the finite
ordered series for `1+N`, with `N^k=0`. Every product is in its original
order; no commutativity is used.

More precisely let Aold be the sum of the shifted identity sources of a_j,
and Anew those of U_n. Define `T_+:Anew->Aold` by components H_(n,j)
(source index n, target index j). Equation (7) says `U=T_+;a`.
Writing rows as target and columns as source just for this block display,

```
Psi_+ = [R U] = Phi^(-1) diag(1_Y,T_+) : Y+Anew -> X,
Psi_+^(-1) = diag(1_Y,T_+^(-1)) Phi : X -> Y+Anew.        (8)
```
Here Phi is the original positive augmented isomorphism `[f;v]`.
Both products in (8) are identities: in one order cancel
`diag(1,T_+)diag(1,T_+^-1)`, in the other cancel `Phi Phi^-1`.
The principal inverse component of Psi_+ is exactly f. This assertion
is about the explicitly defined Psi_+, not yet the Hom mixed mate.

## 4. Negative reservoir height: the whole left cap window

Suppose k<0 and put m=-k. Set

```
K_(j,n)=u_j;V_n=u_(j+n);V, 0<=j,n<m.                     (9)
```
By `cupD_capL` this is zero for j+n<m-1 and identity for j+n=m-1.
Again higher entries remain ordered identity endomorphisms.

For completeness the needed annihilation is `f;V_n=0` for n<m.
From the existing slide `A;f=s f;B-s v_0;u_0`, solve for
`f;B=s A;f+v_0;u_0` and iterate. After composing with V, the first
term vanishes by `sig_capL`; each remaining term contains
`u_j;V=0` with j<n<=m-1. Thus the entire expression vanishes,
without an unsigned reflection or cyclicity assertion. Compose V_n with
the negative total inverse identity on Y to obtain

```
V_n = sum_(j<m) b_j;K_(j,n).                             (10)
```
Let Bold be the sum of the targets of b_j and Bnew those of V_n.
Define `T_-:Bold->Bnew` by components K_(j,n). After reversing j the
matrix is unit triangular, and has a finite ordered inverse. Equations
(9)-(10) prove componentwise

```
Psi_- = [R;V] = diag(1_X,T_-) Phi^(-1) : Y -> X+Bnew,
Psi_-^(-1) = Phi diag(1_X,T_-^(-1)) : X+Bnew -> Y.        (11)
```
Phi is now `[f u]:X+Nold->Y`. Direct multiplication cancels the same
two pairs as in (8), in the opposite order. Both inverse identities hold;
the principal inverse is f. No inverse to the bare f was used.

## 5. Shifts, boundary cases, and transposition

Here is an even degree-zero packaging of (8)-(11). Use
`Hom^0(Z[l,e],W[t,a])=Hom^(l-t,e-a)(Z,W)`, as in
`FusedFeedbackComparison.md`. The raw principal coordinates are

```
Y[0,sigma] -> X[0,sigma+p].
k>0: Anew_n=1[d(1-k+2n),(n+1)p], 0<=n<k,
k<0: Bnew_n=1[-d(1+k+2n),np], 0<=n<-k.                 (12)
```
They are the profiles at h_Hom=-k with delta=epsilon=0 in the Hom
coordinates. On the original inverse matrix add the common parity shift
sigma+p. Its old positive identity source is
`1[d(k-1-2j),jp+sigma+p]`, and its old negative identity target is
`1[d(k+1+2j),(j+1)p+sigma+p]`. Substituting respectively
j=k-1-n and j=-k-1-n gives (12), in both integer and parity coordinates.
The degree of (5) is `2d(1-k+n+j)`, and that of (9) is
`2d(1+k+j+n)`; their parities are sigma+(n+j)p. These are exactly
the degree differences between their respective shifted summands.

Choose lifts to parity-shifted summands using the z maps, not bare
underlying module identities. The preceding raw equations then define the
shifted matrices by transport; their inverse equations are conjugated
identities. On supermodules the shifted targets carry their parity-twisted
actions. No step regards a parity involution as a bimodule endomorphism.
The additional signs in (3) can be incorporated by diagonal sign changes
on Anew or Bnew, respectively. They are involutive units, so both inverse
identities persist and the principal inverse stays f. This does not
identify the principal entry with the actual Hom mate.

At k=1, T_+ is the one-entry identity, U=a_0; at k=-1,
T_- is the one-entry identity, V=b_0. At k=0 both windows are empty:
Psi=R and its inverse is f, using both height-zero inversion identities.
Here U=-u_0;R and V=R;v_0, sigma=p and c(0)=1. In particular zero
height does not license using bare-crossing invertibility at other heights.

There is **no right transposition in (5)-(11)**. The dot is kept on its
original E strand, and powers combine by vertical composition. Accordingly
no q(n) factor belongs in these window matrices. If one instead replaces
a power by powers of its right transpose, one must insert
`q(n)=(-1)^(p*n*(n-1)/2)` as proved in `SignedFTriangle.md`; already n=2
is different for an odd dot. That alternative coordinate change has not
been identified with (2). It cannot repair a missing principal-mate
comparison merely by adding q(n) to (7) or (10).

## 6. Exact remaining obstruction

Let tau_H be the specified diagonal upward Hom crossing, including its
horizontal reversal convention, and let P_H(tau_H) be its partial mate
formed with the **specified** units and counits of
`homContentPreAdjunction`. The raw principal component still to evaluate is

```
D_H(H)=C_src(H)^(-1);P_H(tau_H)(H);C_tgt(H)
       : P_Y(H)->P_X(H).                                  (13)
```
Equations (3), (7), (10) identify its adjacent dotted windows. To substitute
(8) or (11) for the actual augmented Hom matrix requires an equality of
(13) with P_R, or with an explicitly determined scalar multiple of P_R
and the matching whole-matrix rescaling. No such equality is proved here.
The same-height reflection of `SignedFTriangle.md` uses the original
*right* adjunction, not this normalized-left composite. Abstract
uniqueness of adjoints identifies adjunctions only after a specified
comparison; it does not evaluate (13). Nor does taking a partial mate
preserve arbitrary isomorphisms.

The improvement is that the finite identity windows are now explicit
invertible, generally non-diagonal changes of the **inverse** original
matrix at height k, with index reversal and Hom height -k. Literal
same-height right-factor window identification is the wrong target.
The remaining crossing equality must be derived with the signed
pitchforks and the actual tau_H convention; this note does not assume it.

If that equality is obtained with a scalar of degree zero, the resulting
principal inverse has degree zero, and each left closure
`U_r;f;V_s` has degree `2d(r+s+1)>0` by (4). The fixed-content
supercentre argument of `DeformedReservoirBound.md` would then apply to
these closures directly, without identifying them with right closures.
This is a conditional consequence, not nilpotence of actual Hom feedback:
(13), the shifted swapping-mate evaluations and the tensor support in (TC)
are still needed. Residual `S=LHQ`, multicolour relations, separation and
nondegeneracy remain open. No coefficient order or feedback factorization
hypothesis has been changed.
