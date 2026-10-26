# Three-strand sector braid and paired interchange residual

**Status: proposed finite component reduction, not a proof of the shifted
Hom braid or a Lean theorem.** The headline calculation reduces every
same-colour three-strand component to two explicitly typed paired-interchange
residuals. Its downstream use is the iii relation for the corrected fused
crossing, without a localized sector identification. The rational part closes
in both parities. The remaining categorical identities are displayed below;
they have not been derived here from the Hom shift comparisons. In particular,
this note does not add them as premises of a claimed fused-action theorem.

## 1. Conventions and the two blocks

Products are functional, with target rows and source columns. Put
`q=(-1)^p`. Every dot and crossing has parity p. Use exactly the mixed matrix
of `CrossingNormalization.md`:

```
[[-q a, J], [-J^-1 a², q J^-1 a J]].
```

Every J below is a whiskered, content-indexed instance of
`L(z_kappa M);j;z_(kappa+p)(ML)^-1`, in execution order inside this formula.
No J is replaced by an unsigned permutation. Conjugation by one J transports
each of the two local dots with coefficient q. Its transport of a spectator
dot also has coefficient q, by super interchange. Consequently a mixed
coefficient involving one spectator transports with coefficient q, in either
parity. Its square transports without that coefficient.

For the sector order `(AAB,ABA,BAA)` write

```
J1 : ABA -> AAB,       J2 : BAA -> ABA,
P0=1,                 P1=J1,           P2=J1 J2.
```

These P maps identify only the three given Hom-sector objects with the first
one. They are not a comparison with a localized representation. Their
parities are respectively 0,p,0. Entrywise conjugation `T_uv -> P_u T_uv P_v^-1`
is ordinary composition in the Hom category; it introduces no extra matrix
multiplication sign. The signs from whiskering remain in the entries.

Let x,z be the reservoir dots and y the probe dot on AAB, and set

```
f=a(z,y),   g=a(x,y),   D=T_1|AAB,
E=(J1 J2) (T_2|BAA) (J1 J2)^-1.
```

The transported matrices are

```
U = [ D   0    0 ]       V = [ -q f   1    0 ]
    [ 0  -g    1 ]           [ -f²   q f   0 ]
    [ 0  -g²   g ]           [  0     0    E ].             (1)
```

Here U is T_1 and V is T_2. In particular the middle diagonal of U is
`-q (q g)=-g`, not `-q g`. This retains the odd spectator sign in the
previous AAB calculation. The all-same-factor boundary E has deliberately
not been identified with D.

For `(ABB,BAB,BBA)`, instead use

```
J1 : BAB -> ABB,       J2 : BBA -> BAB,
P0=1,                 P1=J1,           P2=J1 J2.
```

On ABB let x be the reservoir dot and y,z the probe dots, and put

```
f=a(x,y),   g=a(x,z),   D=T_2|ABB,
E=(J1 J2) (T_1|BBA) (J1 J2)^-1.
```

The same displayed matrices apply, but now V is T_1 and U is T_2.
Thus the execution braid difference is the negative of `UVU-VUV` in this
block. These two blocks include every mixed A/B sector of iii.

## 2. Rational reduction using only factor slides

In either block use the ordered first and second dots of the repeated
factor. For a polynomial h the two fixed slides and the spectator sign give

```
D h = s(h) D + delta(h),
s(first)=q second,  s(second)=q first,  s(spectator)=q spectator,
delta(first)=-q,    delta(second)=1,    delta(spectator)=0,
delta(h k)=delta(h) k+s(h) delta(k).                    (2)
```

The square relation is `D²=0`. All three dots pairwise q-commute. Define

```
a(u,v)=(u-v)^-1                           if q=1,
a(u,v)=(u-v)(u²-v²)^-1                    if q=-1.
```

Only mixed reservoir/probe denominators occur. They are units by the
nilpotent-reservoir/invertible-probe finite geometric series. The odd
squares are central in this dot algebra, not necessarily central with D.
For a denominator h, extension of (2) is forced by

```
delta(h^-1)=-s(h)^-1 delta(h) h^-1.
```

Applying this formula gives, in both blocks and both parities,

```
D f=q g D-f g,            D g=q f D+q g f.             (3)
```

For example the first formula at odd AAB is precisely `D f=-g D-f g`
from `ParitySectorComparison.md`. The ABB formula has the same sign:
the repeated pair is now y,z, and x is the odd spectator. One must not use
the AAB delta values for x,y,z unchanged in this block.

Here is a complete list of the nine entries of `UVU-VUV`, before identifying
E and D. It also records every finite path contribution; juxtaposition is
ordered multiplication and is not commutative shorthand.

| target, source | entry |
| --- | --- |
| 0,0 | `-q D f D-f D f-g f²` |
| 0,1 | `-D g+q f D+q g f` |
| 0,2 | `D-E` |
| 1,0 | `g f² D-q f² D f-q f g f²` |
| 1,1 | `q g f g-E g²+f² D+f g f` |
| 1,2 | `-q g f+E g-q f E` |
| 2,0 | `g² f² D-E g² f²` |
| 2,1 | `q g² f g-g E g²+q E g² f` |
| 2,2 | `-q g² f+g E g-E g E` |

Setting E=D makes all nine expressions zero. This is an algebraic identity,
not a polynomial representation assumption on the factor crossing: move D
to the right with (2), discard D², and clear only the mixed denominators.
Both coefficients, that of 1 and that of D, vanish as ordered skew
polynomials. Formula (3) gives the two simplest entries immediately.
The first entry at odd parity reduces to `f²g-gf²=0`; at even parity the
same calculation uses ordinary commutativity. The remaining entries use
the same Leibniz and inverse rules, without any inverse of a same-factor
dot difference. An exact symbolic expansion of all nine entries for each
block and parity checks these numerator identities; it does not sample
values of dots or choose a finite-dimensional factor representation.

For clarity the whole unreduced categorical obstruction can now be written
without nine separate rational obligations. Put K=E-D. The matrix is exactly

```
UVU-VUV =
[ 0       0                         -K                         ]
[ 0      -K g²                       K g-q f K                 ]
[-K g² f²  -g K g²+q K g² f          g K g-D g K-K g D-K g K   ]. (4)
```

No commutation of K with f or g is used. In particular its bottom-right
entry retains `E g E`, rather than incorrectly replacing it by E² times g.
The 0,2 entry shows that the entire block braid holds **if and only if**
its specified paired-interchange residual K vanishes. This is a reduction
of the obstruction, not a proof that it vanishes.

## 3. First remaining equations on the shifted Hom functors

The two precise equations left by (4) are

```
(T_1|AAB) J1 J2 = J1 J2 (T_2|BAA),                    (5A)
(T_2|ABB) J1 J2 = J1 J2 (T_1|BBA).                    (5B)
```

Each side has the same indicated source (BAA or BBA) and target (AAB or
ABB). Every J includes its content change, its whiskering, and the even
bicategory associators. These are equations for the given factor crossings,
not for a newly chosen crossing conjugated to make them true.

There is no independent three-mixed-exchange braid to impose: with only two
sector labels, a three-strand mixed word has a repeated factor. The first
unresolved path is the component BAA -> AAB: the two paths are precisely
the two sides of (5A). Its rational coefficients are both units 1 after
transport to (1); rational slides cannot repair a failure of (5A).
The analogous first unresolved path in the other block is BBA -> ABB.

The expected proof must expand J from the z and j formula above. For AAB,
the odd-colour word functors are `S_c MLL`, `L S_(c+1) ML`, `LL S_c M`.
For ABB, BAB, BBA they are respectively
`S_(c+1) M S_(c+1) ML`, `S_(c+1) ML S_c M`, and
`L S_c M S_c M`.
Thus (5B) compares two double-shift boundaries with different individual
shift indices, even though both total parities vanish. Removing them with
bare z introduces `z_1(S_1 X);z_1(X)=-xi_1(X)`.

`RouquierHomContentCoherence.lean` proves supernatural movement of a single
shift and its negative self-interchange. It does not itself state (5A) or
(5B) for the transported repeated-factor crossings. A proof must combine
those statements with the even associator coherence and the specified
same-factor crossing transport; total parity zero alone is insufficient.
No derivation of those two identities is claimed in this note. They are
not justified by the existence of the forced localized H of
`ParitySectorComparison.md`, which remains unconstructed.

## 4. Coverage and remaining scope

AAA and BBB use their factor braid axioms. Each mixed block has nine
components. Components between different A-counts vanish because every
entry preserves that count. Thus the finite decomposition covers the whole
three-strand sector matrix; its only unevaluated identities after the
rational reductions are (5A) and (5B). Neither iij/iji braids nor integer
word shifts are addressed. Q, factor crossings, dots, adjunctions, and the
corrected mixed entries are unchanged. There is no evaluation from a total
quotient ring at nilpotent dots and no scalar a-gauge.
