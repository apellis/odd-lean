# Distinct-colour mixed-sector mates in the swapped Hom construction

**Status: proposed written calculation, not a Lean theorem.** Assume the
factor actions and normalized left adjunctions used in
`SwappedActionAssembly.md` §1. This note computes the two mixed-sector
entries of its (A8), with its (A5) unchanged. It does not address the
pre/pre distinct-colour entry or assert a full action. The factor categories
are the all-module supercategories of the prescribed full-ELV quotients.
On a factor edge at content beta, E is tensoring by
`B_(beta+i)e(beta,i)` and F is restriction to its corner. Its even right
unit inserts `e tensor e`, its right counit multiplies the kernels, and
its dot is the signed right multiplier `R_x(w)=(-1)^(p_i |w|)wx`.
These are the constructions of `DeformedActionAssembly.md` §§1,5 at
`6f348ac3`, specialized for the unit-dot probe or truncated for the
reservoir, not replacement functors. The normalized left adjunction is
still the specified full-factor input. Independent odd coefficient
directions and their own ELV relations are retained; none is set to zero.
Absent contents are zero categories; the resulting zero functors satisfy
the same inverse identities on their zero supports.

## 1. The square, including both content labels

Semicolons are chronological; functor application is functional. Fix
`i != j`, write `p=p_i`, `q=p_j`, and `r=pq`. Choose nonnegative contents
`b,b-i,c,c+j`. Put

```
D0=H_(b,c),       C0=H_(b-i,c),
D1=H_(b,c+j),     C1=H_(b-i,c+j).
L:Ds -> Cs = pre(E_i^T),       K:Cs -> Ds = pre(F_i^T),
M:D0 -> D1, C0 -> C1 = post(E_j^W),
N:D1 -> D0, C1 -> C0 = post(F_j^W).
t=q P(b),       u=q P(b-i)=t+r,
h=h_i(-Lambda_P+alpha(b-i)),  sigma=p(h+1).
```

The two copies of L have the **same probe edge**, bottom height h and top
height h+2. Postcomposition changes c, not b, so sigma is unchanged on
them, even when the external Hom weight changes. The two post edges
have the same reservoir bottom weight `-Lambda_R+alpha(c)`, but their
shifts are t and u, respectively. Let

```
R=S_sigma K,    B=S_t M on D0,    B'=S_u M on C0,
T=N S_t:D1 -> D0,                T'=N S_u:C1 -> C0.
```

T here denotes the post right adjoint, not the probe category. In
chronological words `BA` and `AB`, respectively, the upward functors are
`L B` and `B' L`. Thus exactly (A5) says

```
j:L M -> M L,
J=L(z_t M);j;z_u(M L)^-1 : L B -> B' L,
J^-1=z_u(M L);j^-1;L(z_t M)^-1.                       (1)
```

The raw j is the even inverse associator. J and its inverse have parity
r. All shifts act on their own Hom categories; an object H has no parity.
The prescribed unequal-colour upward entries are `J^-1` and `J;Q`, where
Q is evaluated on the target `AB=B'L`. The notation `QJ` in functional
matrix notation therefore means `J;Q` here.

The projection (A8) gives the following **different** bent supports:

```
U=M(J^-1): A_i R_(B_j) -> R_(B_j) A_i,
  functionally L T -> T' L : D1 -> C0;
V=M(QJ): R_(A_i) B_j -> B_j R_(A_i),
  functionally B R -> R B' : C0 -> D1.                (2)
```

For U the quadruple `(c,d,a,b)` of (A8) is `(A_i,B_j,B_j,A_i)`;
for V it is `(B_j,A_i,A_i,B_j)`. Sector projections are even. The unit
and counit select these single entries; no central block is added.
In particular **QJ bends the pre-probe i strand**, not the post-reservoir
j strand. With the fixed orientation (1), the polynomial below contains
a transposed unit probe dot and a surviving nilpotent reservoir dot.
A polynomial in a surviving probe dot and a transposed reservoir dot
would instead belong to a polynomial attached to J inverse. That is not
the prescribed unequal-colour assignment.

## 2. Specified adjunctions and raw coordinate maps

Let `a:Id -> KL` be the raw pre unit, and `v:LK -> Id` its normalized
raw counit. Their parity is sigma. The factor left cup is at top height
h+2, the left cap at bottom height h, and

```
e(h)=1 (h<0), e(h)=(-1)^p (h>=0),
c(h)=(-1)^sigma e(h),    v=c(h)^-1 pre(leftCap),
eta_A=a;z_sigma(KL)^-1,
eps_A=(-1)^sigma L(z_sigma K);v.                      (3)
```

Associators and unitors in a and v are those of `HomSectorTransport.md`
(4). The raw K snake is 1, the raw L snake is `(-1)^sigma`.
For the even raw post unit `a_B:Id -> NM` and cap `v_B:MN -> Id`,

```
eta_s=a_B;N(xi_s(M -)^-1),
eps_s=S_s(v_B(S_s -));xi_s,             s=t,u.         (4)
```

These are the input-shift right adjoints NS, not output-shift SN.
The fixed coherence identities are

```
S_s(f);z_s=(-1)^(s|f|) z_s;f,
xi_s=(-1)^s z_s(S_s -);z_s,
beta_(H,s)=z_s(H -);H(z_s^-1).                        (5)
```

In particular the two bare z removals are not xi. Formula (3) is the
output-shift result of the prescribed beta transport of the intermediate
pre adjunction; (4) retains xi from the post composite adjunction.
No new beta or word comparison is chosen.

The coordinate maps, with H in the source category indicated in (2), are

```
C_s=L N(z_t(H)) : L T H -> L N H,
C_t=N(z_u(L H)) : T' L H -> N L H,
D_s=z_t(M S_sigma K H);M(z_sigma(K H)) : B R H -> M K H,
D_t=z_sigma(K S_u M H);K(z_u(M H)) : R B' H -> K M H.
                                                               (6)
```

Their parities are t,u,t+sigma,sigma+u, respectively. Each inverse
reverses the listed maps. Let `h_B:LN -> NL` and `h_A:MK -> KM` be the
canonical even associator interchanges, with their opposite associators
as inverses. These are concrete pre/post interchanges of the specified
factor edges, not new comparison assumptions.

## 3. The two dotless component calculations

The literal words obtained by expanding (A8), at H, are

```
U_H=eta_u(L T H); T'(J^-1_(T H)); T'L(eps_t(H)),
V0_H=eta_A(B R H); R(J_(R H)); R B'(eps_A(H)).          (7)
```

Here V0 denotes the mate of J before inserting Q.
The unit and cap in each line carry their own edge labels.

For U, move the final z_u through the middle J inverse and the even
cap. This gives exponent ur. Expanding its unit gives

```
xi_u(Z)^-1;z_u(S_u Z)=(-1)^u z_u(Z)^-1.
```

That inverse cancels the first z_u in J inverse. At the other end (4)
and (5) give

```
z_t(M N S_t H)^-1;eps_t(H)=(-1)^t MN(z_t(H));v_B(H).
```

The remaining z_t moves only through the even j inverse and raw post
unit and cancels C_s. The exponent is `ur+u+t=tr`. After the even
associator reassociation the residual word is
`a_B(LNH);N(j^-1_(NH));NL(v_B(H))=h_B(H)`: it is the post right snake
with the pre factor untouched. Consequently

```
C_s^-1;U;C_t = beta h_B,       beta=(-1)^(tr).         (8)
```

For V0, removal of the final z_sigma through R(J) gives sigma r.
Removal of z_u through the even cap contributes nothing. Moving z_t
through the raw unit a contributes sigma t; moving the remaining
z_sigma inverse through a contributes sigma squared. The cap in (3)
contributes sigma. Thus the total is

```
sigma r+sigma t+sigma^2+sigma = sigma u.
```

The remaining word is
`a_(MKH);K(j_(KH));KM(v_H)=h_A(H)`, by the normalized K snake.
This explicitly uses c(h) inverse; it does not replace that snake by
a principal inverse component. Therefore

```
D_s^-1;V0;D_t = alpha h_A,      alpha=(-1)^(sigma u).   (9)
```

This derivation extends the calculation of `HomSwappingMates.md` §§2–3
at `6f348ac3` by retaining the independent parities p,q and replacing
only the crossing parity by r. The exponent reductions use `r^2=r`,
not `p=q`. At h=0, c(0)=1 is obtained from (3); it is not replaced by
a nonzero-height formula. No gamma principal-inverse scalar occurs.

## 4. The particular probe dot which is transposed

Write d for the inherited dot of L, of parity p. On K define Z by the
following **explicit normalized-left cup–dot–cap word**:

```
Z_H=a_(K H);K(d_(K H));K(v_H).                        (10)
```

The unit and cap, with their normalization, are those of (3). This is
not an identification with the unrelated factor right transpose. To
verify (10), take the right transpose in the even adjunction `L ⊣ R`,
whose component is

```
d^R_H=eta_A(RH);R(d_(RH));R(eps_A(H)).
```

Then `z_sigma(KH)^-1;d^R_H;z_sigma(KH)=Z_H`. Expand (3): moving the
last z_sigma left contributes sigma p, moving the initial inverse
through a contributes sigma, moving it through d contributes sigma p,
and the cap contributes sigma. Their sum is zero. This proves (10)
with no extra dot sign suppressed.

For a homogeneous endomorphism f of L let `Z(f)` denote the same word
with d replaced by f. The even-sector transpose law and ordinary
conjugation by z_sigma give

```
Z(f;g)=(-1)^(|f||g|) Z(g);Z(f),
Z(d^m)=(-1)^(p binom(m,2)) Z^m,
Z^-1=(-1)^p Z(d^-1).                                 (11)
```

The last line follows by transposing **both** inverse-dot identities;
it proves that this actual Z is a unit on the probe. Its two inverse
products are 1. The composition and power laws are the laws of
`SuperAdjunction.rightTranspose_comp` and `rightTranspose_power`, not
an assumption that arbitrary partial mates preserve isomorphisms.

## 5. Polynomial coordinate of the prescribed QJ

Write the target-AB polynomial in the fixed colour order as

```
Q_ij(X,Y)=sum_(m,n) a_mn X^m Y^n,
```

where X is the pre i dot, Y the post j dot, and nonzero coefficients
have `pm=0` and `qn=0` in Z/2. These are the separate exponent-support
conditions of the stated original homogeneous parameters: for the
interior coefficients, `Scalars.s_eq_zero` gives the first condition
and `Scalars.s_symm` gives the second. The Cartan parity condition gives
the same statements for the two leading terms. These are the data in
`Basic.lean`, not a common-parity restriction on i and j. In particular
both dot powers have parity zero in each supported monomial. On raw KM let Y now
denote the surviving post j dot, with its factor action unchanged, and
Z the dot (10) on K, whiskered by M. Put

```
G(Z,Y)=sum_(m,n) a_mn (-1)^(p binom(m,2)) Z^m Y^n.
                                                               (12)
D_s^-1;V;D_t = alpha h_A;G.                            (13)
```

Here is the insertion check for (13). Expand V by replacing J in (7)
with `J;Q`. On `B'L=S_u ML`, the inherited dot powers become
`S_u(M(d^m))` and the shifted post dot power. Removing z_u gives
exponents upm and uqn; moving these powers through the raw pre unit
or cap gives sigma pm and sigma qn. All four vanish on support.
The post power is on the untouched external factor, so it moves to the
KM output through even reassociation. The pre power is precisely the
cup–power–cap word of (10), hence contributes the first sign in (11).
Reordering the two supported powers gives exponent `(pm)(qn)=0`.
Thus the only additional sign relative to (9) is
`p binom(m,2)`, separately for each monomial. Linearity proves (13).
For an odd i, a supported square has coefficient -1, not +1. There
is no transpose of the j power in this orientation.

## 6. Finite two-sided inverse on the actual mixed target

The dot Y is nilpotent at the fixed reservoir edge, uniformly on its
modules; choose `Y^N=0`. On KM the dots obey `ZY=(-1)^(pq)YZ` by
super interchange. All supported powers in (12) commute with both
dots and with each other. The y-free part is

```
A=a_(d_ij,0) (-1)^(p binom(d_ij,2)) Z^d_ij,
H=G-A,       E=A^-1 H,
A^-1=a_(d_ij,0)^-1 (-1)^(p binom(d_ij,2)) Z^(-d_ij).
```

Homogeneity and the leading-unit parameter condition say that this is
the whole y-free part. For disconnected colours `d_ij=0`, it is the
nonzero constant leading coefficient. This is a unit by (11), even
when i is odd. Every term of H has positive Y exponent, and the
commutation just proved gives `E^N=0`. Hence an explicit inverse is

```
G^-1=(sum_(ell=0)^(N-1) (-E)^ell) A^-1.               (14)
```

Both products with G are 1: write `G=A(1+E)=(1+E)A` and use
`(1+E) sum (-E)^ell=sum (-E)^ell (1+E)=1`. This is a
finite natural-transformation identity, not a choice of inverse at
individual modules. No reservoir inverse dot and no inverse of an
upward partial mate is used. The finite bound may vary with c.

On the original shifted words the two inverse maps are

```
U^-1=beta C_t;h_B^-1;C_s^-1,
V^-1=alpha D_t;G^-1;h_A^-1;D_s^-1.                    (15)
```

For U followed by its inverse, cancel C_t inverse with C_t, then
h_B with its inverse, then C_s with its inverse; the scalar is beta
squared. In the opposite product cancel C_s first and then h_B.
For V followed by its inverse cancel D_t first and G G inverse,
then h_A and D_s. In the opposite product cancel D_s first, then
h_A, then G inverse G and D_t. Both scalar squares are 1. These are
adjacent cancellations, so no exchange of homogeneous maps introduces
an additional Koszul sign. This proves both inverse identities.

## 7. Dependency and scope ledger

The inspected definitions are `homContentPreE`, `homContentPostE/F`,
`homContentPostAdjunction` in `RouquierHomContent.lean`;
`homContentPreF/Adjunction` and `homParityShiftSquare` in
`RouquierShiftedAdjunction.lean`; `homParityShiftCommute` in
`RouquierHomContentCoherence.lean`; and `homSectorInterchange` in
`RouquierHom.lean`. The transpose laws are in
`RouquierRightTranspose.lean`, including `rightTranspose_apply`.
The beta/xi convention agrees with the explicit paired transport in
`PairedHomInterchange.md` at `24cd3760`, especially its (6).

The factor actions, dot-unit probe and fixed homogeneous reservoir
truncation remain the written inputs of `SwappedActionAssembly.md`.
Only the two cross-sector instances of its (A8) are addressed here.
Their dotless raw interchanges, normalized-left probe dot (10), signed
polynomial (12), and both inverse maps (15) are specified, not assumed.
The source obligation is the mixed-sector part of `invNe₁`, `invNe₂`
in `Presentation.relation`, as identified in that assembly's table.
The pre/pre calculation and full finite-action verification are separate;
so are the post same-colour principal comparison, normalized bubbles,
bounded detection, and nondegeneracy. No Lean build or new checked
mathematical declaration accompanies this written argument.
