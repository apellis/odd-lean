# Content-shifted swapping mates

**Status: written component calculation, not a Lean theorem.** This note
uses the normalized left adjunction of `HomSectorTransport.md`, hence the
written F triangle in `SignedFTriangle.md`. For the precise upward matrix
in `NondegeneracyProof.md` §5.3, it evaluates both swapping partial mates
and gives their inverses. It does not prove the remaining central-feedback
transport in (TC), integer-graded fusion, or the fusion relations.

## 1. Edges, order and coordinates

Use `f;g` for first f, then g, and functional order for functors. Fix one
reservoir edge, and write

```
L:D -> C, K:C -> D, R=S_sigma K,
B=S_kappa M on D, B'=S_kappa' M on C,
Q=N S_kappa, Q'=N S_kappa', kappa'=kappa+p.
```

Here L and K are precomposition by E and F; M and N are postcomposition
by the probe E and F. The letters D,C stand for reservoir Hom sectors;
all four probe source/target categories in the squares are implicit, but
no reservoir content is identified. If the bottom factor height of the
reservoir edge is h, `sigma=p(h+1)`; the top height is h+2. A probe step
does not change either reservoir height or content. Removing the reservoir
strand changes content parity by p, just as adding it does.

Write `z_t:S_t H -> H` for the specified parity-removal comparison. The
only shift rules used below are

```
S_t(f);z_t = (-1)^(t|f|) z_t;f,
xi_t = (-1)^t z_t(S_t H);z_t(H),
j:L M -> M L is even.
```

These are the conventions of `RouquierHomContentCoherence`,
`RouquierShiftedAdjunction` and `StringDiagrams.Super.Pi` at dependency
revision `8ae261b`; in particular bare consecutive z's are not xi.
All omitted associators and unitors are even.

The two upward summands and their specified comparisons are

```
BA=L B=L S_kappa M,       AB=B' L=S_kappa' M L,
J=L(z_kappa M);j;z_kappa'(M L)^-1 : BA -> AB,
J^-1=z_kappa'(M L);j^-1;L(z_kappa M)^-1 : AB -> BA.       (1)
```

Both have parity p. Adjacent cancellation proves both inverse identities.
Each individual dot changes by `(-1)^p` through J; its square does not.
The chosen upward matrix has entries J and `-a^2;J^-1`, not a rational
coefficient on both orientations. For an odd colour,

```
a=(X-Y)(X^2-Y^2)^-1,
a^2=(X^2+Y^2)(X^2-Y^2)^-2                              (2)
```

on AB, where X is the reservoir dot and Y the probe dot. For an even
colour `a=(X-Y)^-1`. These are exactly the orientation and normalization
of that matrix, not a replacement by an even raw interchange.

The two mixed sources and targets, in functional order, are

```
P_A(J): B R -> R B',
P_B(-a^2;J^-1): L Q -> Q' L.                            (3)
```

Thus the A bend at an object H in C has source `S_kappa M S_sigma K H`
and target `S_sigma K S_kappa' M H`. The B bend at an object H in D
has source `L N S_kappa H` and target `N S_kappa' L H`.
Use precisely these coordinate maps:

```
A_s=z_kappa(M S_sigma K H);M(z_sigma(K H)) : B R H -> M K H,
A_t=z_sigma(K S_kappa' M H);K(z_kappa'(M H)) : R B' H -> K M H,
B_s=L N(z_kappa(H)) : L Q H -> L N H,
B_t=N(z_kappa'(L H)) : Q' L H -> N L H.                 (4)
```

Their parities are respectively `kappa+sigma`, `sigma+kappa'`,
kappa and kappa'. Their integer degrees are zero. Inverses reverse the
listed factors; none of these comparisons is declared even by fiat.
Let `h_A:M K -> K M` and `h_B:L N -> N L` be the canonical even
mixed pre/post interchanges. Their inverses are the opposite associators.

## 2. A bend: the normalized left snake and every sign

Let `u:Id -> K L` insert the factor left cup at height h+2 and let
`v:L K -> Id` insert `c(h)^-1` times the factor left cap at height h,
where

```
c(h)=(-1)^sigma e(h),   e(h)=1 for h<0, e(h)=(-1)^p for h>=0.
eta=u;z_sigma(K L)^-1,  eps=(-1)^sigma L(z_sigma K);v.
```

The normalized K snake is one. Both u and v have parity sigma, whereas
eta and eps are even. In particular no unnormalized cap is substituted.
The exact unit-map-cap word at H is

```
P_A(J)_H = eta_(B R H); R(J_(R H)); R B'(eps_H).         (5)
```

To evaluate `A_s^-1;P_A(J);A_t`, first move the final outer z_sigma
left through `R B'(eps)` and `R(J)`. Only J is odd, so this contributes
`(-1)^(sigma p)` and cancels the z_sigma inverse in eta. Naturality of
z_kappa' on the even eps then cancels the z_kappa' inverse in J. What
remains, with this first coefficient understood, is

```
A_s^-1;u_(B R H);K L(z_kappa(M R H));
K(j_(R H));K M(eps_H).
```

Move z_kappa through u: its exponent is `sigma kappa`. The first factor
of A_s cancels. Move `M(z_sigma^-1)` through u: its exponent is
`sigma^2=sigma`. Naturality of the even j introduces no further sign.
The resulting inverse `K M L(z_sigma^-1)` cancels the z_sigma in eps,
whose explicit coefficient contributes another sigma. The total is

```
sigma p + sigma kappa + sigma + sigma = sigma kappa'.   (6)
```

The remaining raw word is

```
u_(M K H);K(j_(K H));K M(v_H) = h_A(H).                (7)
```

Indeed external pre/post reassociation puts u and v on the reservoir
strand with the probe strand untouched; their composite is the normalized
F (equivalently K) snake, equal to one. There is no crossing of two
nonidentity factor maps in this reassociation. Therefore

```
A_s^-1;P_A(J);A_t = alpha h_A,  alpha=(-1)^(sigma kappa'). (8)
```

The coefficient c(h) inverse has not disappeared by an arbitrary gauge:
it is used exactly in (7), where the unnormalized F snake is c(h).
There is no principal inverse component in this calculation.

## 3. B bend: xi and the probe snake

Write `u_B:Id -> N M` and `v_B:M N -> Id` for the even probe
adjunction components. The two content labels have the units/counits

```
eta_t=u_B;N(xi_t(M -)^-1),
eps_t=S_t(v_B(S_t -));xi_t.
```

For now bend J inverse without its coefficient. Its exact word is

```
P_B(J^-1)_H = eta_kappa'(L Q H);
              Q'(J^-1_(Q H)); Q' L(eps_kappa(H)).       (9)
```

Removing B_t moves z_kappa' through J inverse and the even eps_kappa,
contributing `kappa' p`. The remaining pair in the unit is

```
xi_kappa'(Z)^-1;z_kappa'(S_kappa' Z)
  = (-1)^kappa' z_kappa'(Z)^-1.
```

This cancels the first z_kappa' in J inverse. At the other end use the
literal probe cap comparison from `HomSectorTransport.md` (7):

```
z_kappa(M N S_kappa H)^-1;eps_kappa(H)
  = (-1)^kappa M N(z_kappa(H));v_B(H).                  (10)
```

Move the remaining z_kappa through the even raw j inverse and u_B; it
cancels B_s. The total exponent is

```
kappa' p+kappa'+kappa = kappa p.                       (11)
```

The raw word `u_B(L N H);N(j^-1_(N H));N L(v_B(H))`
contracts the probe snake and is h_B. Consequently

```
B_s^-1;P_B(J^-1);B_t = beta h_B, beta=(-1)^(kappa p).   (12)
```

This proves a scalar depending on the content; omitting either xi sign
in (10)–(11) would change it. It is not a consequence of invertibility
of J inverse.

## 4. The rational coefficient and finite inverses

Put W equal to the raw right transpose of the probe dot, on N. On the
mixed target N L put X for the surviving reservoir dot. Inserting an
even monomial in X squared and Y squared into (9) changes none of the
exponents (11). Its square dots commute through all z comparisons without
a sign. The probe cap and cup give the signed transpose law

```
M_B(f;g)=(-1)^(|f||g|) M_B(g);M_B(f),
M_B(Y^n)=(-1)^(p n(n-1)/2) W^n.
```

It follows directly, not by unsigned rational substitution, that
`Y^2` maps to `-W^2` when p=1. Restricted to commuting even squares,
the transpose preserves products and inverses: transpose each of the two
inverse identities, whose factors are even. For p=0 it is the usual
substitution Y to W. Thus, with the rational factor placed **after h_B**,

```
B_s^-1;P_B(-a^2;J^-1);B_t = -beta h_B;g_B,
g_B=(X^2-W^2)(X^2+W^2)^-2                 (p=1),
g_B=(X-W)^-2                             (p=0).       (13)
```

The initial minus is the specified upward coefficient. Both J and J
inverse commute with even squares up to their same-factor transport, so
placing a squared coefficient before J inverse causes no extra sign.

Here are explicit finite inverse formulas. Choose m with `X^(2m)=0` in
the odd case and set `t=X^2 W^-2`. Then t is nilpotent and commutes with W.
The probe transpose is invertible: transposing both original inverse
equations gives `M_B(Y^-1)=-W^-1` for p=1. Hence

```
S_minus=sum_(0<=r<m) t^r, S_plus=sum_(0<=r<m) (-t)^r,
g_B=-W^-2 (1-t) S_plus^2,
g_B^-1=-W^2 (1+t)^2 S_minus.                          (14)
```

Multiplying in either order uses `(1-t)S_minus=S_minus(1-t)=1`
and `(1+t)S_plus=S_plus(1+t)=1`. Thus both products are one;
no inverse of the reservoir dot occurs. For p=0 choose `X^n=0`, put
`t=X W^-1`, and use

```
g_B=W^-2 (sum_(0<=r<n) t^r)^2,  g_B^-1=(X-W)^2.        (15)
```

These identities require only a bound on the fixed reservoir content
(and its finitely many adjacent edges), not arbitrary Hom-finiteness or
a uniform bound across an infinite weight fiber.

For clarity the two inverse maps on the actual shifted objects are

```
I_A=alpha A_t;h_A^-1;A_s^-1,
I_B=-beta B_t;g_B^-1;h_B^-1;B_s^-1.                    (16)
```

Equations (8), (13) identify the forward maps with
`alpha A_s;h_A;A_t^-1` and `-beta B_s;h_B;g_B;B_t^-1`.
Their forward-then-inverse composites cancel A_t or B_t first, then
`h_A;h_A^-1` or `g_B;g_B^-1`, then the source comparisons. The
inverse-then-forward composites cancel A_s or B_s first, then
`h_A^-1;h_A` or `h_B^-1;h_B` and `g_B^-1;g_B`, then the target
comparisons. The scalar products are alpha squared and beta squared,
both one. These are ordinary adjacent composition cancellations; no
Koszul sign arises from moving the inverse across a homogeneous map.
This proves both inverse identities for each mate.

The A-bent rational expression in `FusedFeedbackComparison.md` is not
the coefficient of the first map (8): that upward entry is J, not a²J.
If one separately bends a squared coefficient attached to J, the same
argument on commuting squares gives
`(Y^2-Z^2)(Z^2+Y^2)^-2`, with the scalar alpha, where Z is the dot
transposed by the **normalized-left sector adjunction**, then transported
by z_sigma to K. The signed power law follows by taking mates in the
even sector adjunction; conjugation by z_sigma preserves products. This
statement does not identify Z with a right transpose in the unreversed
factor. Such an identification is not needed for either map (8), (13).
It must not be inferred from the untwisted right-adjunction calculation.

## 5. Integer profiles and scope of the conclusion

The functors currently specified in `RouquierHomContent` have parity
shifts, not an additional integer content shift. In the homogeneous
precursor, with dots of degree 2d, the exact local degree inventory is

| map | integer degree | parity |
|---|---:|---:|
| J, J inverse | 0 | p |
| a | -2d | p |
| -a²;J inverse | -4d | p |
| P_A(J), I_A | 0 | p |
| P_B(-a²;J inverse), I_B | -4d, +4d | p |
| A_s, A_t | 0 | kappa+sigma, kappa'+sigma |
| B_s, B_t | 0 | kappa, kappa' |

For the A bend the fixed-edge cup degree is `-d(h+1)` and cap degree
`d(h+1)`; they cancel. The B cup and cap are likewise on the same edge
and have opposite degrees. The retained coefficient g_B has degree -4d.
Every normalization scalar in this note has integer degree zero.
Under `Hom^0(U[l,e],V[m,f])=Hom^(l-m,e-f)(U,V)`, (8) is an even
map from its source to its target `[0,p]`, and (13) is an even map
from its source to its target `[4d,p]`. Their inverses have the opposite
profiles. This records the local homogeneous maps; it is **not** a claim
that these independently shifted targets form a single graded fused
Rouquier matrix.

In particular the displayed upward normalization is not homogeneous of
degree -2d on the unmodified integer-graded sector functors: its two
swapping entries have degrees 0 and -4d. To make the whole upward block
have degree -2d requires relative word shifts
`delta_AB-delta_BA=-2d` in this convention. No such integer content
shift has been constructed by (1)–(16), and none is silently chosen here.
After the invertible-dot probe specialization there need not be an integer
grading at all. The parity-supercategory inverse statement above still
applies. The distinction is necessary when using a graded precursor to
justify central-closure degree bounds.

Finally, the six projected supports in `FusedFeedbackComparison.md` §2
apply before any coordinate removal. The two maps (3) have only their
respective mixed source and target; the diagonal unit and counit kill
all projections to the same-sector central block. Dotted augmented cups
and caps also stay in their matching sectors. Eliminating these two
invertible cross blocks therefore contributes **no extra Schur term**
to the central block.

What remains of (TC) is the central ordered-series/closure comparison:
transport its C,D entries and the full reversed reservoir augmented
inverse into common tensor coordinates, including the signed dotted
windows and all homogeneous comparisons. Where that inverse enters,
`HomPrincipalMate.md` gives `gamma(k) f`, with
`gamma(k)=(-1)^(p k)` for k nonzero and `gamma(0)=(-1)^p`.
It does not enter either snake calculation above; inserting gamma here
would replace a snake by a different principal-inverse closure. Conversely
it cannot be dropped when computing the central feedback. The residual
identity-summand matrix, fusion relations and separation also remain open.
