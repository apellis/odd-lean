# Paired Hom interchange and repeated-factor crossings

**Status: written component proof, not a Lean theorem.** This computes the
two equations (5A) and (5B) of `ThreeStrandSectorBraid.md`, using the
reservoir crossing of `HomPrincipalMate.md` and the even probe word-removal
transport fixed in `HomProbeMatrix.md` §1, equation (1). The expanded map
below is exactly that prescribed transport, not an additional convention
or a crossing gauge. Together with `ThreeStrandSectorBraid.md`, this proves
the same-colour iii braid under that reduction's factor and denominator
hypotheses. It does not construct a localized sector comparison or establish
the other fusion relations.

## 1. Types, maps, and conventions

All composites separated by semicolons are in execution order. Functor
application is functional order. Fix the colour parity p and put q=(-1)^p.
Let a_r=T(-(muP+r alpha_i)) and b_s=W(muM+s alpha_i). For every required
index take the factor edges

```
e_r:a_(r+1)->a_r,              f_s:b_s->b_(s+1),
C_(r,s)=Hom(a_r,b_s),
L_r:C_(r,s)->C_(r+1,s),        L_r(X)=e_r X,
M_s:C_(r,s)->C_(r,s+1),        M_s(X)=X f_s.
```

The same notation L_r or M_s at different unused indices means the
corresponding Hom functor, not an identification of the categories. Each
X is an arbitrary object of C_(0,0); every morphism h:X->Y considered below
is homogeneous of arbitrary parity d. No parity is assigned to X.

Let kappa be the shift at reservoir content betaP. At content
betaP+r i the shift is kappa+r p. Denote kappa by k and k+p by u in the
formulas below; k+2p=k. Each S_t acts in the particular C_(r,s) containing
its argument. Its comparison z_t(Z):S_t Z->Z has parity t and satisfies

```
S_t(h);z_t(Y)=(-1)^(t d) z_t(X);h.                    (1)
```

All L and M are even superfunctors. Write

```
j_(r,s)(Z)=alpha_(e_r,Z,f_s)^-1:
 L_r M_s Z -> M_s L_r Z,
J_(r,s,t)(Z)=L_r(z_t(M_s Z));j_(r,s)(Z);
             z_(t+p)(M_s L_r Z)^-1.                  (2)
```

Here Z belongs to C_(r,s); j is even and J has parity p. These are exactly
the inverse associator and shift-removal formula of `HomSectorTransport.md`,
not independently chosen swapping maps. Their homogeneous naturality is

```
L_r S_t M_s(h);J(Y)=(-1)^(p d) J(X);S_(t+p) M_s L_r(h).
```

It follows by applying (1) twice and the ordinary naturality of the even
associator; the exponent is td+(t+p)d=pd. In particular every displayed
component calculation below applies to the full Hom categories.

## 2. Raw repeated-factor maps and the associator calculation

Set P=L_1 L_0 and Q=M_1 M_0. The reservoir raw crossing C_Z:PZ->PZ has
parity p and is the reassociated map `-q (t_A whisker Z)` from
`HomPrincipalMate.md`. Explicitly, for e=e_1 e_0 and
`a_Z=alpha_(e_1,e_0,Z):e Z->PZ`,

```
C_Z=a_Z^-1;[-q (t_A whisker Z)];a_Z.
```

The probe raw crossing B_Z:QZ->QZ has parity p. For f=f_0 f_1 and
`b_Z=alpha_(Z,f_0,f_1):QZ->Z f`, it is

```
B_Z=b_Z;(Z whisker t_B);b_Z^-1.
```

Both are supernatural of degree p. Thus, for example,
`P(h);C_Y=(-1)^(pd) C_X;P(h)`. This is the super-interchange
law for t_A and h, with the fixed scalar -q unchanged.

The two raw paired comparisons are

```
jA_X=L_1(j_(0,0)(X));j_(1,0)(L_0 X):P M_0 X->M_0 P X,
jB_X=j_(0,1)(M_0 X);M_1(j_(0,0)(X)):L_0 Q X->Q L_0 X.
```

Their crossing equations are

```
C_(M_0 X);jA_X=jA_X;M_0(C_X),
L_0(B_X);jB_X=jB_X;B_(L_0 X).                        (3)
```

Here is the component content of the coherence used in (3). The pentagon
identifies jA with
`a_(M_0 X)^-1;alpha_(e,X,f_0)^-1;M_0(a_X)` and jB with
`L_0(b_X);alpha_(e_0,X,f)^-1;b_(L_0 X)^-1`.
After substituting C and B and cancelling adjacent a or b inverses, (3)
reduces respectively to the two associator naturality equations

```
(t_A whisker (X f_0));alpha_(e,X,f_0)^-1
 =alpha_(e,X,f_0)^-1;((t_A whisker X) whisker f_0),
(e_0 whisker (X whisker t_B));alpha_(e_0,X,f)^-1
 =alpha_(e_0,X,f)^-1;((e_0 X) whisker t_B).
```

The first equation is multiplied on both sides by -q. The only moving
nonidentity homogeneous map in either equation is the indicated crossing;
all other coherence maps and identity whiskers are even. Hence the scalar
from super-interchange here is 1, not (-1)^p. This proves the raw input (3)
without assuming either shifted target equation.

## 3. AAB: cancellation of the intermediate shift

All three word objects lie in C_(2,1):

```
W0=BAA=P S_k M_0 X,
W1=ABA=L_1 S_u M_0 L_0 X,
W2=AAB=S_k M_0 P X.
J2=L_1(J_(0,0,k)(X)):W0->W1,
J1=J_(1,0,u)(L_0 X):W1->W2.
```

Each J has parity p. Set R0=P(z_k(M_0 X)) and
R2=z_k(M_0 P X); both have parity k. Expanding (2) gives

```
J2;J1 = P(z_k(M_0 X));L_1(j_(0,0)(X));
 L_1(z_u(M_0 L_0 X)^-1);L_1(z_u(M_0 L_0 X));
 j_(1,0)(L_0 X);z_k(M_0 P X)^-1
 = R0;jA_X;R2^-1.                                    (4)
```

The middle inverse pair cancels adjacently, so no exchange sign occurs.
The prescribed boundary crossings are

```
T0=T_2|BAA=C_(S_k M_0 X),
T2=T_1|AAB=S_k(M_0(C_X)).
```

The complete two paths W0->W2, both of parity p, normalize as follows:

```
T0;J2;J1
 =(-1)^(kp) R0;C_(M_0 X);jA_X;R2^-1
 =(-1)^(kp) R0;jA_X;M_0(C_X);R2^-1,
J2;J1;T2
 =(-1)^(kp) R0;jA_X;M_0(C_X);R2^-1.                   (5)
```

The first sign is supernaturality of C on z_k, of parity k. The second
is (1) applied to M_0(C_X), of parity p. The -q of the reservoir crossing
remains inside C on both sides, giving total coefficient
`-q (-1)^(kp)` relative to the reassociated inherited t_A. Thus (5)
proves (5A), with all k and p retained.

## 4. ABB: the double-shift calculation

Use the even map fixed in `HomProbeMatrix.md` and also displayed in
`HomCentralFeedback.md`:

```
Theta_t(Z)=S_t M_1(z_t(M_0 Z));z_t(Q Z):
 S_t M_1 S_t M_0 Z -> Q Z.
```

To identify it with the fixed transport, expand the specified beta and xi
comparisons, retaining the two adjacent probe-edge indices:

```
S_t(beta_(M_1)(M_0 Z)^-1);xi_t(Q Z)
 = S_t M_1(z_t(M_0 Z));S_t(z_t(Q Z)^-1);
   S_t(z_t(Q Z));z_t(Q Z)
 = S_t M_1(z_t(M_0 Z));z_t(Q Z).
```

The middle inverse pair cancels adjacently, with no sign or gauge change.
These are the beta and xi used by `homParityShiftCommute` and
`homParityShiftAdd`, including their identity cases at t=0.

Each constituent has degree t; Theta_t is even and natural on all
homogeneous maps. This also follows directly from (1): the two signs
for a morphism of degree d are (-1)^(td) and (-1)^(td), whose product is 1.
It is important that the *map*, not just its parity, is retained:

```
Theta_t(Z)=(-1)^t z_t(M_1 S_t M_0 Z);M_1(z_t(M_0 Z)).  (6)
```

Equation (6) is (1) for the degree-t map M_1(z_t). At t=1 its minus
is the same negative self-interchange responsible for
`z_1(S_1 Y);z_1(Y)=-xi_1(Y)`. Theta cannot be replaced by the bare
right side of (6) without this scalar.

All word objects now lie in C_(1,2):

```
V0=BBA=L_0 S_k M_1 S_k M_0 X,
V1=BAB=S_u M_1 L_0 S_k M_0 X,
V2=ABB=S_u M_1 S_u M_0 L_0 X,
J2=J_(0,1,k)(S_k M_0 X):V0->V1,
J1=S_u M_1(J_(0,0,k)(X)):V1->V2,
R0=L_0(Theta_k(X)),  R2=Theta_u(L_0 X).
```

The R maps are even. To expand and normalize the pair, put
`Z=S_k M_0 X` and `F=L_0(z_k(M_0 X));j_(0,0)(X)`, of parity k.
Substitution of J1 and Theta_u cancels the adjacent inner z_u inverse
and z_u before any interchange, giving

```
J2;J1;R2
 = L_0(z_k(M_1 Z));j_(0,1)(Z);
   z_u(M_1 L_0 Z)^-1;S_u M_1(F);z_u(Q L_0 X)
 = (-1)^(uk) L_0(z_k(M_1 Z));j_(0,1)(Z);M_1(F)
 = (-1)^(uk) L_0(z_k(M_1 Z);M_1(z_k(M_0 X)));jB_X
 = (-1)^(uk+k) R0;jB_X
 = (-1)^(kp) R0;jB_X.                                (7)
```

The first sign uses (1) with the degree-k map M_1(F). The next equality
is naturality of the even j_(0,1) on z_k; its sign is 1. The next sign
is (6), not an unsigned removal of two shifts. Finally
`uk+k=(k+p)k+k=kp` in Z/2. Consequently the paired comparison in raw
coordinates is *not always* jB: it is (-1)^(kp) jB.

Define the already specified probe transport, separately at each content,
by `Bhat_t(Z)=Theta_t(Z);B_Z;Theta_t(Z)^-1`. This is transport by the
fixed even word-removal map, not by J or by a map chosen to force (5B).
The two boundary crossings are precisely

```
T0=T_1|BBA=L_0(Bhat_k(X)),
T2=T_2|ABB=Bhat_u(L_0 X).
```

Expanding these formulas and (7), the two complete paths normalize to

```
T0;J2;J1
 =(-1)^(kp) R0;L_0(B_X);jB_X;R2^-1
 =(-1)^(kp) R0;jB_X;B_(L_0 X);R2^-1,
J2;J1;T2
 =(-1)^(kp) R0;jB_X;B_(L_0 X);R2^-1.                  (8)
```

Only adjacent inverse cancellations and (3) are used in (8); both paths
have parity p. The common coefficient is (-1)^(kp), including the case
k=p=1 where it is -1. This proves (5B) for the displayed Theta transport.
All Hom indices, shifts, and homogeneous morphisms were retained; no
nilpotence, height restriction, localized equivalence, or braid axiom for
these mixed paths was used.

## 5. Boundary of the result

The component calculation supplies the two paired-J equations for the
specified C and Bhat. It is a written proof awaiting formalization,
not a kernel-checked consequence of
`RouquierHomContentCoherence.lean` alone. That module supplies single-shift
movement and negative self-interchange; `RouquierHom.lean` supplies the
Hom functors, homogeneous transformations, and raw associator comparison.
Neither module bundles the two boundary crossings used here.

The identification in §4 fixes Bhat to the prescribed BB transport.
No new choice of crossing is licensed by the proof: an arbitrary even
automorphism need not preserve that crossing. Combining (5) and (8) with
the separate reduction in `ThreeStrandSectorBraid.md` proves every component
of the same-colour iii braid. Mixed-colour braids, coherent integer word
shifts, full fusion and separation are not asserted here.