# Content-shifted Hom adjunction components

**Status: written mathematical derivations, not new Lean theorems.** These
calculations use the factor action and the signed triangles in
`SignedFTriangle.md`. They remove the unspecified cup/cap transport from the
Hom construction. They also specify the parity-correct interchange. They do
not identify the resulting principal inverse closures with the literal
right-adjunction tensor coordinates of the factors; that remaining distinction
is stated in §6. In particular the whole fusion comparison is not proved here.

## 1. Typed conventions

Write `f;g` for first f, then g. Functor application is ordinary functional
order: `KL(X)=K(L(X))`. Suppress only canonical even associators and unitors
when using this functor notation. A Hom-category object X is a 1-morphism;
it has no assigned parity. A homogeneous morphism `f:X→X'` has parity q.

Fix a colour i, `p=p(i)`, and a reservoir edge

```
a=T(-nuP), b=T(-muP), E:a→b, F:b→a,
-nuP+alpha_i=-muP, h_A=<h_i,-nuP>, sigma=p(h_A+1).
```

For any fixed target c put `L=homPre(E):(b→c)→(a→c)` and
`K=homPre(F):(a→c)→(b→c)`. Let `z_t(X):S_t X→X` be the comparison of
`homParityShiftDatum t`, identity if t=0 and ζ if t=1. Its degree is t.
For a homogeneous f of degree q the exact rule is

```
S_t(f);z_t(X') = (-1)^(t q) z_t(X);f.                   (1)
```

Write `xi_t:S_t S_t→Id` for `homParityShiftSquare t`. In particular

```
xi_1(X)=Pi(z_1(X));z_1(X)=-z_1(Pi X);z_1(X),
beta_H(X)=z_t(HX);H(z_t(X)^-1):S_t HX→H S_t X.         (2)
```

The second formula is for t=1, with identity for t=0. Thus two consecutive
bare ζ removals are **minus** ξ, not ξ. These conventions are precisely
`PiSupercategory.ξ_hom_eq_neg`, `β_hom`, and
`RouquierHomContentCoherence.homParityShiftCommute`. They also agree with
`Envelope.ζPow`: parity removal is a homogeneous isomorphism, not an even
identification of the underlying morphism spaces.

For the probe edge `muM+alpha_i=nuM`, put `M=homPost(E_B)`,
`N=homPost(F_B)`, `kappa=p contentParity(betaP)`, and `S=S_kappa`.
The sector functors are exactly

```
L_A=L,  R_A=S_sigma K;       L_B=S M,  R_B=N S.          (3)
```

These are the functors in `homContentPreE/F` and `homContentPostE/F`.
The normalization of the reservoir factor is not adjustable: write U for
`T.leftCup`, V for `T.leftCap`, and

```
e(h)=1 (h<0), e(h)=(-1)^p (h>=0),
c=(-1)^(sigma sigma)e(h_A),   Vbar=c^-1 V.
```

The normalized F snake is 1 and normalized E snake is `(-1)^sigma`.
Here U is at b (top of this edge) and V is at a (bottom); using the same
region for both is incorrect. Since the height changes by two along the
edge, their parities agree, but their local inverse definitions differ.

## 2. Reservoir unit and counit, including the normalization sign

Define the raw, degree-sigma components

```
u_X = lambda_X^-1 ; (U ▷ X) ; alpha_(F,E,X)
      : X→F(E X)=KLX,
v_Y = alpha_(E,F,Y)^-1 ; (Vbar ▷ Y) ; lambda_Y
      : E(F Y)=LKY→Y.
```

Then the unit and counit of the **specified** `homContentPreAdjunction` are

```
eta_A(X) = u_X ; z_sigma(KLX)^-1
          : X→S_sigma(KLX)=R_A L_A X,
eps_A(Y) = (-1)^sigma L(z_sigma(KY));v_Y
          : L(S_sigma(KY))=L_A R_A Y→Y.                (4)
```

Both maps are even. In particular the raw coefficient of the cap in this
output-shift convention is `(-1)^sigma c^-1`, not just `c^-1`.

Here is a derivation rather than a chosen adjunction gauge. The intermediate
`homPreShiftAdjunction` has left functor `S_sigma L`, right functor K,
unit `u_X;K(z_sigma(LX)^-1)`, counit `z_sigma(LKY);v_Y`.
Compose with the self-adjunction of S, exactly as in
`homContentPreAdjunction`, then remove the left S² using ξ and move the
right S through K using beta_K inverse. In the unit, `xi_(S LX)^-1`
cancels `S(xi_LX)`, and the remaining `K(z_LX^-1)` cancels the K(z_LX)
in beta_K inverse. This gives the first line of (4). In the counit the
remaining pair is `S(z_KY);z_KY=xi_KY`; replacing the other consecutive
ζ pair by this pair uses `S(z)=-z_S`. This yields `(-1)^sigma` in (4).

One can verify that coefficient independently without any shift convention
inference. The L triangle of (4) is `(-1)^sigma` times the raw E snake,
hence the identity. For the R triangle use (1) and supernaturality of u:

```
u_(S KY);KL(z_KY)=(-1)^sigma z_KY;u_KY.
```

The extra sign cancels the coefficient of eps_A, after which the raw F
snake and `z;z^-1=1` finish. For a degree-q f, naturality of u or v costs
`(-1)^(sigma q)` and naturality of z costs the same sign. Their product is
one; (4) is natural on the full Hom categories, not just even morphisms.

For the dot `d_A(X)=x_A ▷ X`, put

```
u_n(X)=u_X ; K(d_A(X)^n),
v_n(Y)=d_A(KY)^n ; v_Y,
chi_A(Y)=L(z_sigma(KY)):L S_sigma KY→LKY.
```

With the sector definitions `cup_A(n)=eta_A;R_A(d_A^n)` and
`cap_A(n)=d_A(R_A(-))^n;eps_A`, one obtains

```
cup_A(n)(X);z_sigma(KLX) = (-1)^(sigma n p) u_n(X),
cap_A(n)(Y) = (-1)^(sigma(1+n p)) chi_A(Y);v_n(Y).     (5)
```

The first sign is (1) applied to `K(d_A^n)`. For the second, exchange
`x_A^n` with z once; their parities are np and sigma. All other coherence
maps are even. This holds for every n≥0, all heights and all contents; it
is not inferred from a finite parity table. In terms of the unnormalized
left cap, the coefficient in the second line is
`(-1)^(sigma(1+n p)) c^-1`.

## 3. Probe components and the double-shift sign

Let u_B:Id→NM and v_B:MN→Id be the even raw postcomposition unit and
counit of `homPostAdjunction`. Explicitly

```
u_B(X)=rho_X^-1;(X ◁ eta_B);alpha_(X,E_B,F_B)^-1,
v_B(Y)=alpha_(Y,F_B,E_B);(Y ◁ eps_B);rho_Y.
```

Set `d_B(X)=X ◁ x_B` (on M X),
`u_B,n=u_B;N(d_B^n)`, and `v_B,n(Y)=d_B(NY)^n;v_B(Y)`.
The composite adjunction defining `homContentPostAdjunction` gives

```
eta_B^Hom(X)=u_B(X);N(xi_kappa(MX)^-1),
eps_B^Hom(Y)=S(v_B(SY));xi_kappa(Y),
cup_B(n)(X)=u_B,n(X);N(xi_kappa(MX)^-1),
cap_B(n)(Y)=S(v_B,n(SY));xi_kappa(Y).                 (6)
```

The cup formula follows by naturality of the even ξ, not by commuting a
single odd ζ across the dots. The cap formula agrees with the literal
`homPostCounit` word order, including its associator.

There is a useful completely explicit raw cap coordinate. Set H=MN and

```
chi_B(Y)=z_kappa(H S Y);H(z_kappa(Y)):S H S Y→H Y,
chi_B^xi(Y)=(-1)^kappa chi_B(Y).
```

These maps are even. Directly from (1), applied first to v_B,n and then
to its supernatural dependence on Y, one gets

```
cap_B(n)(Y)=chi_B^xi(Y);v_B,n(Y).                     (7)
```

Indeed `xi_kappa=(-1)^kappa z_(S Y);z_Y`. Moving the first z past
`v_B,n(SY)` costs `(-1)^(kappa n p)`, and moving the second past that
transformation costs the same sign. They cancel. The surviving
`(-1)^kappa` is the double-shift sign in (2). Equivalently chi_B^xi is
`S(beta_H^-1);xi_(H Y)`. It is not correct to discard this sign while
using the bare z;H(z) comparison. Formula (7) also holds for negative n
when the probe dot is invertible, with integer parity np modulo two.
No integer-degree bound or nilpotence is imposed on the probe.

## 4. The parity-correct swapping comparison

Here restrict to one fixed colour, not to any parity or height. An A step
changes reservoir content by one i, so its B shift changes from kappa to
`kappa'=kappa+p`. Removing a strand has the same parity effect as adding
one. The two upward words on an object X are

```
AB(X)=S_kappa'(M L X),    BA(X)=L(S_kappa(M X)).
```

Write `j_X:L M X→M L X` for the inverse of the associator in
`homSectorInterchange E_A E_B`. This j is even. The matrix convention in
`NondegeneracyProof.md` §5.3 has its upper-right entry going **BA→AB**;
use J in that direction here, regardless of the earlier prose orientation.
The explicit comparison in that direction and its inverse are

```
J_X = L(z_kappa(MX));j_X;z_kappa'(MLX)^-1,
J_X^-1 = z_kappa'(MLX);j_X^-1;L(z_kappa(MX)^-1).       (8)
```

Their parity is `kappa+kappa'=p`. The two inverse identities follow by
adjacent cancellation, with no exchange of odd maps. For a homogeneous
f of degree q, (1) twice and ordinary naturality of j give
`BA(f);J_(X')=(-1)^(p q) J_X;AB(f)`.

For either factor dot, moving it through the two comparison maps in (8)
costs `(-1)^(kappa p+kappa' p)=(-1)^p`. Thus J intertwines each dot with
its same-factor dot in the other order with exactly that sign. The same
argument applies to inverse probe dots. This proves the two signed dot
intertwinings directly from the content change, rather than the false
claim that an even external interchange becomes odd without a comparison.
For different colours the same construction changes kappa by `p(i)p(j)`;
no multicolour braid conclusion is drawn from that observation.

If a is the specified diagonal rational endomorphism of AB, the two
swapping entries, in the source-on-the-right matrix convention, are
`J:BA→AB` and `-a^2;J^-1:AB→BA`. This specifies their shifts and signs
without treating raw j as J. It does not verify the remaining crossing
relations for a.

## 5. Partial mates: types, substitutions and dot powers

For an upward entry `t: L_c L_d→L_a L_b` in execution-word order, its
sector partial mate has type `R_a L_c→L_b R_d` and execution word

```
(R_a L_c ◁ eta_d);
(R_a ◁ t ▷ R_d);
(eps_a ▷ L_b R_d).                                  (9)
```

All weight labels in a unit or counit are those of its own edge, not the
central weight of the whole word. Formula (9) is obtained by inserting
the even sector projections into `rouquierMate`; diagonality of the unit
and counit kills every other sector. There is no sign from projections.
For J in (8), take `(c,d,a,b)=(B,A,A,B)`; for `-a²;J^-1` take
`(A,B,B,A)`. In particular their mixed supports are, respectively,
`R_A L_B→L_B R_A` and `R_B L_A→L_A R_B`, not the central AA/BB blocks.

Equations (4), (6), (8), (9) are explicit composable formulas for both
partial mates, using only factor U,V,eta_B,eps_B,x_A,x_B and ζ,ξ. The first
has precisely the normalized A cup and A cap, hence one factor
`(-1)^sigma c^-1`; the second has the B unit and B cap and the initial
minus from `-a²;J^-1`. This statement describes coefficients **before**
moving any ζ through these words. It is not an assertion that the final
raw scalar is that coefficient: those movements must use (1), and σ can
also occur in their exponents.

Dots cannot be partially transposed by unsigned substitution. For the
factor's even right adjunction, `SignedFTriangle.md` gives

```
M(f;g)=(-1)^(|f||g|) M(g);M(f),
M(x^n)=q(n) M(x)^n,   q(n)=(-1)^(p n(n-1)/2).          (10)
```

In particular an odd square changes sign. For an invertible odd dot,
`M(x^-1)=-M(x)^-1`, by transposing both inverse identities. Formula (10)
concerns the right transpose; the A edge in (9) instead uses its normalized
left adjunction through (4). Identifying these operations requires a
proved left/right mate comparison, not a silent application of (10).
No claim that taking an arbitrary partial mate preserves isomorphisms is
used or justified by these formulas.

## 6. What remains of the fusion comparison

The former missing input of normalized reservoir left adjunction transport
is now replaced by (4)–(5); the probe transport is (6)–(7). The comparison
J, including its degree and both dot signs, is (8). These formulas apply
at all admissible contents without collapsing content to weight.

The remaining identity is more specific than an abstract tensor-support
assumption. Under the coordinate maps `z_sigma(KLX)`, chi_A and chi_B^xi,
compute the two complete words (9) with (8), and compute the diagonal
reservoir mixed mate and its augmented inverse using (4). Their reservoir
cup/cap coordinates are **U and Vbar**, as (5) shows, not the even right
cup/cap of the unreversed factor. One must identify that reversed,
shifted augmented matrix with the intended raw factor matrix, including
its principal inverse, dotted windows and q(n) factors. The resulting
closure must then be compared with `v_A(s) R_A u_A(r)` in the proposed
feedback formula. Neither a renaming of U,V nor the existence of both
adjunctions proves this matrix identity.

The finite C,D series already proved from the slide can be populated by
the sector cups/caps (5)–(7), including their listed signs. To replace them
by literal right-factor supported tensors requires the preceding
left/right matrix comparison and the evaluation of the two shifted
swapping mates. Those evaluations are not completed here. In particular
no invertibility claim for those partial mates, no principal-feedback
nilpotence assertion for the Hom realization, no residual `S=LHQ`, no
crossing braid, no joint separation and no nondegeneracy theorem follows
from this note. Integer grading on an unspecialized Hom realization is
also separate from these parity identities.
