# Same-colour inversion with the probe on the precomposition side

**Status: proposed written proof, not a Lean theorem.** On each specified
finite homogeneous reservoir quotient, the prescribed same-colour augmented
map on `Hom(T(-muP),W(muM))` has a two-sided inverse when T is the unit-dot
probe and W is the full-ELV reservoir. The reduction below uses the existing
negative-window algorithm, but exchanges only **direct-sum labels after
forming the mates**, not the two adjunctions or the upward crossing entries.
In particular no opposite-category, Chevalley, or E/F replacement is used.

## 1. Factors, weights and the fixed conventions

Assume the full factor constructions of `DeformedActionAssembly.md`,
`DeformedMixedBraid.md`, `DeformedGradedAction.md` and `InvertibleDotProbe.md`,
with their stated admissibility hypotheses: finite compatible support,
positive integral symmetrizers, purely even base with 2 invertible, and the
prescribed homogeneous Q parameters and leading units. Use the exact ELV
coefficient quotient, including its even-cutoff exterior relations. At each
reservoir content beta its finite homogeneous truncation has upper integer
support M_beta and nilpotent dots on the required adjacent edges. There is
no grading requirement on the specialized probe.

Here are literal weights, not just coroot coordinates. Apply
`ProbeReachability.md` to **-mu**. In its pairing extension choose

    Lambda_P=(0,P(-mu,m)),  Lambda_R=(-mu,P(-mu,m)),
    Lambda_P-Lambda_R=(mu,0).

Take m sufficiently large for positive, cofinal, even probe levels and the
required reservoir bounds. At contents betaP,betaR put

    lambdaP=-Lambda_P+betaP, lambdaR=-Lambda_R+betaR,
    muP=-lambdaP, muM=lambdaR,
    H=<h_i,muP+muM>=h-k,
    k=<h_i,lambdaP>, h=<h_i,lambdaR>.

The original X coordinate of mu is retained, including its coroot kernel.
The content-zero labels are `(Lambda_P,-Lambda_R)` and their sum is mu.
Thus the weight-sign issue in `ELVVacuumTransport.md` §4 (version at
`92669e8f1baff31eb45bab135ce4af835d88e87b`) is avoided by the cutoff choice,
not by reflecting a constructed action. This says nothing about its
remaining vacuum-generator or boundary comparison.

Use exactly `homWeightSector`, `homContentPreE`, `homContentPostE`:

    A=pre(E_T), B=S_kappa post(E_W), kappa=p contentParity(betaP).

The pre right adjoint is obtained from the normalized **left** adjunction
of T. The post right adjoint uses the **right** adjunction of W. All
comparisons are those of `HomSectorTransport.md`. In particular

    q=(-1)^p, sigma=p(k+1),
    c(k)=(-1)^sigma e(k), e(k)=1 (k<0), e(k)=q (k>=0),
    alpha_n=(-1)^(sigma n p),
    beta_n=(-1)^(sigma(1+n p)) c(k)^-1,
    gamma(k)=q^k (k!=0), gamma(0)=q.

The beta subscript denotes a scalar, not content. These formulas extend to
integer n for the probe, since its inverse dot has parity p. No reservoir
negative power is used. Retain `xi_t=(-1)^t z_t(S_t -);z_t`: at t=1 the bare
pair of z removals is **minus** xi. A homogeneous comparison is not silently
regarded as an even identification.

## 2. The sector inverses do not require a new factor action

Write X_A,Y_A for the pre mixed source and target, and X_B,Y_B for the post
mixed source and target. In intrinsic sector coordinates let

    s_A:X_A->Y_A, s_B:X_B->Y_B,
    u_A(n):1->Y_A, v_A(n):X_A->1,
    u_B(r):1->Y_B, v_B(r):X_B->1.

Indices n are integers and r are nonnegative. These are the specified
sector dotted cups/caps; the standard parity shifts on each summand are
understood. All subsequent matrices are even maps between those shifted
sums. For execution words we write `f;g`; juxtaposition of matrix entries
is functional order.

`HomPrincipalMate.md` uses no nilpotence in its pre-sector calculation.
It therefore applies to T without alteration. Its homogeneous raw
comparisons are

    A_s=L_+(z_sigma(K_+ -)), A_t=z_sigma(P_X(-)),
    A_s^-1;s_A;A_t=gamma pre(R_T), R_T=-sigL_T,
    u_A(n);A_t=alpha_n pre(U_n),
    v_A(n)=beta_n A_s;pre(V_n).

Here the raw factor X,Y,U,V are exactly those of that note; its raw X is
not the symbol X_A. The whole pre inverse has principal coordinate
`gamma pre(f_T)`, not `pre(f_T)`. At k<0 its inverse cap-window columns
have coordinate `beta_n^-1 pre(utilde_n)`; at k>0 its inverse cup-window
rows have coordinate `alpha_n^-1 pre(vtilde_n)`. All finite triangular
changes in `ReversedReservoirMatrix.md` remain in utilde and vtilde.
At k=0 both windows are empty, but gamma(0)=q is retained.

`HomProbeMatrix.md` likewise uses no invertibility in its nonnegative post
windows or principal comparison. Applied to W, it gives

    B_s=(-1)^kappa z_kappa(M N S_kappa -);MN(z_kappa),
    B_t=N(xi_kappa(M -)),
    B_s^-1;s_B;B_t=post(sig_W),
    u_B(r);B_t=post(cupD_W(r)),
    v_B(r)=B_s;post(capD_W(r)),
    B_t^-1;j_B;B_s=post(R_W).

Its whole inverse columns a_B exist for h>0, and inverse rows b_B for
h<0. Its principal R_W is the inverse-matrix component, not a bare-crossing
inverse. All these statements hold on zero corners as well.

Finally the literal pre mate satisfies

    y_A s_A-q s_A x_A=u_A(0)v_A(0),                       (1)

where x_A,y_A are the two inherited unit dots on X_A,Y_A. This follows by
applying `rouquierMate_slide` in `OddMath/SKM/RouquierMate.lean` to the
specified even pre adjunctions and the reversed crossing `-q pre(t_T)`.
`HomPrincipalMate.md` §1 checks precisely that crossing's upward slide.
Thus (1) is not a guessed slide for gamma times an inverse. Whiskering
preserves both inverse-dot identities. These facts give exactly the whole
unit-factor input of `ProbeWindowInverse.md` at height **-k**.

## 3. Expand the prescribed entries in the other nilpotent variable

On the execution word AB let x be the pre probe dot and y the post
reservoir dot, with xy=q yx. Keep, literally,

    a=(x-y)^-1                         (p=0),
    a=(x-y)(x^2-y^2)^-1                (p=1),
    T=[[ -q a, J],[-J^-1 a^2, q J^-1 a J]],
    J:BA->AB, J u=q y J, J v=q x J.                     (2)

In particular the negative coefficient of the second swapping entry is
not changed. Now x is a unit and y is nilpotent. The finite expansion is

    a=sum_(r>=0) q^r x^(-r-1)y^r.                       (3)

For odd p this is the even-square geometric series separated into its
even and odd y powers; for even p it is the usual geometric series.
The sums terminate by the reservoir bound. Conjugation by J contributes
q to a monomial of total exponent -1. Also r(-r-1) is even, so the two
powers in every term commute with each other without an extra sign.
Bending the two diagonals of (2), in their actual adjunctions, consequently
gives the following **literal**, not normalized, central entries:

    C:X_B->Y_A = sum_r q^r u_A(-r-1) v_B(r),
    D:X_A->Y_B = -sum_r q^(r+1) u_B(r) v_A(-r-1).        (4)

This uses the same unit-map-cap calculation as `HomCentralFeedback.md`
§2: a first-strand dot belongs before its cap, a second-strand dot after
its cup. It uses no dot transposition. As an explicit raw-coordinate check,

    B_s^-1;C;A_t
      =sum_r q^r alpha_(-r-1) [post(capD_W(r));pre(U_(-r-1))],
    A_s^-1;D;B_t
      =-sum_r q^(r+1) beta_(-r-1) [pre(V_(-r-1));post(cupD_W(r))]. (5)

Thus c(k), every dotted scalar, and the negative bare-xi comparison have
not been removed by declaring A and B interchangeable.

Only NOW permute central direct-sum labels from (A,B) to (B,A). Call the
first sector R (reservoir), the second P (probe), and set

    ell=-h, t=-k, H=t-ell=h-k,
    X0=X_R+X_P=X_B+X_A, Y0=Y_R+Y_P=Y_B+Y_A,
    C_RP=D=-sum_r q^(r+1) u_R(r)v_P(-r-1),
    D_PR=C= sum_s q^(s+2) u_P(-s-1)v_R(s),
    K=[0,C_RP;D_PR,0].                                  (6)

These are exactly the intrinsic-sector coefficients of the corrected
central table, since q^(s+2)=q^s. This is an even permutation of summand
labels, not a tensor interchange, transpose, or new adjunction. Heights,
source and target objects, and every map in (6) have been specified.

## 4. Reservoir contractions and the coefficient ideal

Write j_R:Y_R->X_R and j_P:Y_P->X_P for the two principal whole-inverse
components, and a_R,a_P,b_R,b_P for their other components. Their index sets
in the reordered coordinates are

    P_R=Fin(max(-ell,0))=Fin(max(h,0)), P_P=Fin(max(t,0)),
    N_R=Fin(max(ell,0))=Fin(max(-h,0)), N_P=Fin(max(-t,0)),
    P0=P_R+P_P, N0=N_R+N_P,
    Phi=[diag(s_R,s_P),u;v,0]:X0+N0 -> Y0+P0,
    Phi^-1=[I,a0;b0,0], I=diag(j_R,j_P).

For R these are the **post right** inverse windows. Their useful
contractions need no antidiagonal index change:

    h>0: v_R(r)a_R,j = delta_(r,j) modulo J,
    h<0: b_R,j u_R(r) = delta_(j,r) modulo J,             (7)

for every r>=0 and the indicated finite j window. To prove this, within
the window use the whole inverse identities exactly. Outside it r>j;
`DeformedGradedAction.md` (G6)--(G8) give degree 2d(r-j)>0. The same
calculation shows that the degree-zero diagonal is literally 1, not an
unspecified unit. There are no a_R and b_R windows simultaneously.

The contracted principal closures on the reservoir are

    b_(s,r)=cupD_W(r);R_W;capD_W(s):1_beta->1_beta,
    deg b_(s,r)=d(h+1+2r)+0+d(1-h+2s)
                =2d(r+s+1)>0,
    parity b_(s,r)=p(r+s+1).                            (8)

In particular (8) uses the right closures of W; it is not the old pre
reservoir's left closure with names exchanged. The B_s,B_t pairs cancel
adjacently inside this composite, giving exactly (8).

Take the image coefficient algebra generated by reservoir supercentral
identity maps at beta and the closed probe words in the residuals and
in their finite table inverses. Let J be the two-sided ideal generated by
its positive-integer-degree reservoir part. Products of n such coefficients
vanish for n>M_beta: move only reservoir coefficients past probe words by
supernaturality, retaining their Koszul signs, then use the reservoir upper
degree bound. This is a jointly nilpotent **matrix ideal** on the finite
parity-shifted identity windows. Summing over matrix paths leaves products
of n reservoir factors at the same beta. It is not entrywise nilpotence.
No arbitrary open reservoir functor is allowed in this coefficient algebra.

The same argument applies with the probe source or target left open. In
particular the three contracted expressions

    D_PR j_R C_RP, v_R(a)j_R C_RP, D_PR j_R u_R(a)         (9)

are sums of positive-degree closed reservoir coefficients times probe
words. The first has reservoir closure (8), as do the other two after
replacing one index by a. If l=C_RP j_P and m=D_PR j_R, a product of N
copies of ml has N reservoir closures and vanishes whenever 2dN>M_beta.
No grading on a probe word is used in this assertion. Consequently

    E=sum_(a<N)(ml)^a,
    A0=1+KI, A0^-1=[1+lEm,-lE;-Em,E],
    B0=1+IK, B0^-1=1-I A0^-1 K                          (10)

are exact two-sided inverses. These are ordered products.

## 5. The explicit residual transport

The actual fused window restrictions, in the reordered intrinsic sectors,
are `w_a=[v_R(a),v_P(a)]` and `z_a=[u_R(a);u_P(a)]`; there is no binomial
expansion. For H>=0 set F=Fin(H), and for H<=0 set G=Fin(-H). Define

    S_+=[w a0;0]-[w I;b0] A0^-1 K a0 : P0 -> F+N0,
    S_-=[b0 z,0]-b0 K B0^-1 [I z,a0] : G+P0 -> N0.       (11)

Expanding (10) and using (9) gives precisely the elimination in
`HomResidualWindows.md` §3 with R,P replacing its two sectors. Its
possible b_R C_RP j_P D_PR a_R entry has an empty source or target, since
h cannot be both signs. It is not discarded by a degree guess.

Here is the entire resulting leading table, so the reduction is checkable.
Use a_P,n for probe inverse columns (t>0), b_P,n for inverse rows (t<0),
and j_P for its principal component. Unlisted blocks are zero or empty.
All products below are functional order.

| S_+ row, column | entry modulo J |
|---|---|
| F_a, P_R,s | delta_(a,s)-q^(s+2) v_P(a)j_P u_P(-s-1) |
| F_a, P_P,n | v_P(a)a_P,n |
| N_R,r, P_P,n | q^(r+1) v_P(-r-1)a_P,n |
| N_P,n, P_R,s | -q^(s+2) b_P,n u_P(-s-1) |

| S_- row, column | entry modulo J |
|---|---|
| N_R,r, G_a | delta_(a,r)+q^(r+1) v_P(-r-1)j_P u_P(a) |
| N_P,n, G_a | b_P,n u_P(a) |
| N_R,r, P_P,n | q^(r+1) v_P(-r-1)a_P,n |
| N_P,n, P_R,s | -q^(s+2) b_P,n u_P(-s-1) |

For example, contracting C_RP with b_R leaves only its r-index by (7),
including the minus in C_RP; the minus in (11) then gives the positive
N_R/P_P entry. Contracting D_PR with a_R leaves its s-index and the
minus in (11) gives the negative N_P/P_R entry. The two delta terms
come from the actual fused windows and (7).

These tables are **Hhat_+, Hhat_-** of `ProbeWindowInverse.md` §§3--4,
with its `(k,h)` replaced by `(ell,t)=(-h,-k)`. There are no old-index
alpha/beta changes on the reservoir here: (7) uses its right inverse
coordinates directly. The probe's alpha/beta, gamma and finite triangular
changes remain inside its specified a_P,b_P,j_P and u_P,v_P. They have
not been set to 1. In particular this is an entrywise comparison to the
explicit table, not a definition of a table as L^-1 S Q^-1.

Its algorithm applies because §2 supplies the whole pre-probe inverse,
unit dots and literal slide (1). Its six subcases are respectively

    ell>=0,H>=0;
    ell>=0,H<0,t>=0; ell>=0,H<0,t<0;
    ell<0,H>=0,t>=0; ell<0,H>=0,t<0;
    ell<0,H<0.

The algorithm's source/target order is exactly the order in our tables:
positive source (P_R,P_P), target (F,N_R,N_P); negative source
(G,P_R,P_P), target (N_R,N_P). Its auxiliary correction coefficients are
q^(r+1), q^(s+2), including its **negative** nonnegative cup columns.
For an explicit common parity profile take X_R,X_P at shift 0 and
Y_R,Y_P at shift p; take P_R,s and P_P,n at shifts sp and np,
N_R,r and N_P,n at shifts (r+1)p and (n+1)p, F_a at shift ap,
and G_a at shift (a+1)p. These are the algorithm's profiles with common
shift zero. In particular a negative-height cup source has shift (r+1)p,
not rp, when its principal target has shift p. The whole sector matrices
in §2 acquire exactly these profiles by their common parity shifts.
They apply to the intrinsic even pre adjunction, not to an unsigned removal
of A_s,A_t. Lift every entry by its own source/target z comparison;
inverse products cancel adjacent comparisons only. There is no
need to identify either adjunction with the other.

At H=0 there are two nonempty cases:

* k=h<0: ell=t>0, S:P_P->N_R has entries
  `q^(r+1) v_P(-r-1)a_P,n`. Use that algorithm's (20).
* k=h>0: ell=t<0, S:P_R->N_P has entries
  `-q^(s+2) b_P,n u_P(-s-1)`. Use its (21).
* k=h=0: both residuals are empty. The cases k=0 or h=0 with H nonzero
  are included by the displayed weak inequalities, not by a limiting claim.

Let V0 be the finite inverse from that algorithm for the applicable
explicit table, composed with its stated sum permutations. It is an actual
map before reduction, built only from the unit probe's whole inverse and
unit dots. With n>M_beta put

    e_U=1-V0 S, e_W=1-S V0,
    V=(sum_(a<n)e_U^a)V0=V0(sum_(a<n)e_W^a).             (12)

The errors lie in the coefficient matrix ideal proved above. Telescoping
and e_U V0=V0 e_W give `VS=1` and `SV=1`. This constructs the residual
inverse; it is not an additional hypothesis about that inverse.

## 6. Recover the whole central augmented inverse

For completeness here are typed recovery formulas, with the exact K of
(6). They are the ordered stabilization calculation of
`SameColourInversion.md` §4, not cancellation of identity summands.

For H>=0 let `F_+=[diag(s_R,s_P)+K;w]:X0->Y0+F` and set
`D_+=[wI;b0]:Y0->F+N0`, `C_+=Ka0:P0->Y0`. On (y,f) define

    a=S_+^-1((f,0)-D_+ A0^-1 y),
    eta=A0^-1(y-C_+ a), F_+^-1(y,f)=I eta+a0 a.          (13)

Stabilizing by 1_N0 and applying Phi^-1 and the two elimination shears
gives `diag(A0,S_+)`. Its inverse is two-sided by (10),(12). On output
(y,f,0) the auxiliary N0 coordinate is zero, since the original stabilized
map retains that coordinate. This proves both products of (13).

For H<=0 let `F_-=[diag(s_R,s_P)+K,z]:X0+G->Y0`, and put
`C_-=[Iz,a0]:G+P0->X0`, `D_-=b0 K:X0->N0`. Define

    (g,a)=S_-^-1(b0 y-D_- B0^-1 I y),
    x=B0^-1(I y-C_-(g,a)), F_-^-1(y)=(x,g).              (14)

Stabilize by 1_P0, use the shear `(x,g,a)->(x,g,a+v x)` and Phi^-1,
then the two block elimination shears. The resulting diagonal is
`diag(B0,S_-)`. On stabilized output (y,0) the recovered auxiliary
coordinate a+v x is zero. Both products of (14) follow. At H=0 the two
formulas agree by uniqueness, including the nonempty residual cases.

## 7. The two swapping blocks still have their prescribed inverses

The snake and parity computations in `HomSwappingMates.md` §§2--3 do not
use which dot is nilpotent. With its exact comparisons and scalar names,

    A_s^-1;W_A;A_t=alpha h_A, alpha=(-1)^(sigma kappa'),
    B_s^-1;W_B;B_t=-beta h_B;g_B, beta=(-1)^(kappa p),
    kappa'=kappa+p.

In this paragraph A_s,A_t,B_s,B_t denote that note's **swapping**
comparisons (4), not the central comparisons in §2. The initial minus is
still the initial minus of `-J^-1 a^2` in (2).
Now let X be the surviving pre probe dot and W the raw right transpose of
the post reservoir dot. Transposition preserves nilpotence, including
`M(y^n)=(-1)^(p n(n-1)/2) W^n`. Therefore X is a unit, W nilpotent, and

    p=1: g_B=(X^2-W^2)(X^2+W^2)^-2,
          v=X^-2 W^2, v^m=0,
          g_B=X^-2(1-v)(sum_(r<m)(-v)^r)^2,
          g_B^-1=X^2(1+v)^2 sum_(r<m)v^r;
    p=0: g_B=(X-W)^-2, g_B^-1=(X-W)^2.                 (15)

Even squares commute. Multiplication in either order in (15) gives 1 by
the two finite geometric identities. In the even case X-W itself is a
unit by the same finite series. Thus the inverses are, in execution order,

    W_A^-1=alpha A_t;h_A^-1;A_s^-1,
    W_B^-1=-beta B_t;g_B^-1;h_B^-1;B_s^-1.               (16)

All scalar and comparison pairs cancel adjacently. This replaces only the
finite inverse formula in the nilpotent variable, not the forward map.
The even sector-projection calculation of that note §5 still separates
these supports from the central block and from all dotted windows. No
extra Schur correction is introduced.

If Dsrc,Dtar incorporate these support permutations, the central (A,B) to
(B,A) permutation, and the stated homogeneous lifts, the full inverse is

    Ffull^-1=Dsrc^-1 diag(F_sign^-1,W_A^-1,W_B^-1) Dtar, (17)
    Dtar Ffull Dsrc^-1=diag(F_sign,W_A,W_B).

Both products of (17) are identities by (13)--(16). This proves the whole
same-colour augmented inverse, rather than just a central feedback inverse.

## 8. Scope and remaining obligations

All formulas are contentwise finite. They impose no common exponent on an
infinite weight fiber, no Hom-finiteness, no integer-graded probe, and no
bare-crossing invertibility. Between finite reservoir quotients they commute
with any supplied base-change comparison intertwining the actual Hom maps;
uniqueness makes the result independent of larger adequate bounds. Scalar
extension commuting with arbitrary Hom spaces is not inferred.

The full factor-action constructions remain the stated written inputs;
this note does not require another factor action. Its contribution is the
explicit central/residual transport (4)--(12), using post-reservoir right
closures and the existing pre-probe whole inverse. The calculation is
written, not formalized or independently verified in Lean. The accepted
conditional upward braid calculations require mixed denominators and full
factor relations; they are not themselves full fusion existence theorems.
No full action assembly, tensor-coordinate TC, vacuum/bubble comparison,
regular-word detection, or nondegeneracy claim follows from (17).

The local source statements used here are the inspected
`rouquierMate_slide` and `SuperRouquierLoc.mate_slide`, the definitions in
`RouquierHomContent.lean`, and the written component proofs cited above.
The grading estimates use `DeformedGradedAction.md` (G6)--(G8), not an
unproved grading on the Hom probe. The six-case inverse and its extraction
are exactly `ProbeWindowInverse.md` (7)--(19), with (20)--(21) at H=0;
they are not replaced by a dimension count.
