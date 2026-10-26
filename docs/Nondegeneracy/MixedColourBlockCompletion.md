# Repeated-outer-colour sector blocks and unequal probe transport

**Status: proposed component proof, not a Lean theorem.** The headline is
that the prescribed crossing has execution braid difference
`diag(-q_i C_ij)` on each of `(A_i A_j B_i, B_i A_j A_i)` and
`(A_i B_j B_i, B_i B_j A_i)`, with zero off-diagonal entries. Together with
`MixedColourSectorBraid.md`, this supplies the mixed-sector iji calculation.
The downstream use is the original-datum upward relation of the separated
Hom construction. The iij, ijj and pairwise-distinct ijk component tests
remain open here; neither full fusion nor nondegeneracy follows.

## 1. Fixed data and polynomial identity

Use execution-order words and functional products of maps (rightmost map
first). Semicolons within component formulas instead mean chronological
composition. All functor edges carry their actual weights and reservoir
contents. A Hom object has no parity; a homogeneous Hom morphism has an
arbitrary parity e. The factor actions must satisfy their full multicolour
KLR relations. `RouquierData.cross_mem` specifies degree, and
`RouquierFamily` supplies rank-one relations, not those additional axioms.

Put `p=p_i`, `h=p_j`, `q=(-1)^p`, `epsilon=(-1)^(ph)`. Keep the reservoir
same-colour crossing normalization `-q`, the preassigned different-colour
factor crossings, the degree-`ph` map `J:B_j A_i -> A_i B_j`, and the
unit crossing `J^-1:A_i B_j -> B_j A_i`. The return crossing is `Q J`,
with Q in target coordinates. The same-colour mixed matrix is unchanged:

```
[[-q a, J], [-J^-1 a², q J^-1 a J]].                  (1)
```

Write the existing polynomial as `Q_ij(u,y)=sum c_(r,s) u^r y^s`.
For connected colours this includes **both** leading terms
`t_ij u^(d_ij)` and `t_ji y^(d_ji)`, as well as the permitted mixed terms.
Every supported monomial has `pr=0` and `hs=0` separately in Z/2.
The restrictions on the leading exponents are included. For disconnected
colours Q is the **single** constant `t_ij`. No parameters are changed.

For one reservoir i-dot u and one probe i-dot v, define only the allowed
mixed inverse expression (the reversed argument order is also allowed):

```
a(u,v)=(u-v)^-1                         (p=0),
a(u,v)=(u-v)(u²-v²)^-1                  (p=1).
F(u,y,v)=a(u,v)(Q_ij(u,y)-Q_ij(v,y)).
S(u,y,v)=sum c_(r,s) sum_(0<=l<r) q^l u^(r-1-l) y^s v^l.
```

Then, as identities of the ordered dot algebra,

```
F(u,y,v)=S(u,y,v),
S(v,y,u)=q S(u,y,v),
C_ij(u,y,v)=epsilon S(u,y,v).                         (2)
```

Here is an arbitrary-index proof, without a polynomial representation.
For even i use the finite geometric identity for `u^r-v^r`. For odd i,
only even r occur; `u²,v²` commute with the dots. Factor
`u^r-v^r=(u²-v²) sum_(0<=m<r/2) u^(r-2-2m) v^(2m)`.
Multiplication by `u-v` produces successively the even and odd l terms
of S, with coefficients 1 and -1. Moving `y^s` costs no sign because
`hs=0`. Reversing u,v in S and reordering their powers costs
`q^(l(r-1-l))`; combined with the coefficient and the relabeling
`l -> r-1-l`, the ratio is q for supported r. The r=0 terms vanish.
Thus the second leading term contributes zero to the correction but is
present in both paths. In the disconnected case both F and S are zero.

The denominators above exist by reservoir nilpotence and probe-dot
invertibility. In the odd case `a(u,v)^2=(u²+v²)(u²-v²)^-2`, so its square
commutes with all dots. No same-factor difference or factor crossing is
inverted. Formula (2) is an identity after an already valid mixed inverse,
not a specialization from a total quotient ring.

## 2. Unequal probe colours: the prescribed even transport

Let r,s be arbitrary probe colours, with parities R,S, and let b be the
reservoir content parity. Put `k_r=bR`, `k_s=bS`, `t=k_r+k_s`, and
`Q_rs=M_s M_r`. The word functor is
`F_rs=S_(k_s) M_s S_(k_r) M_r`. Distinguish the functor Q_rs from the
polynomial Q_ij. For the fixed raw probe crossing write
`B_rs:Q_rs -> Q_sr`, of degree `d=RS`.

The pinned parity comparisons are

```
z_k:S_k -> Id,
S_k(f);z_k=(-1)^(k |f|) z_k;f,
beta_(M,k)=z_k(M-);M(z_k^-1):S_k M -> M S_k,
c_(a,c):S_a S_c -> S_(a+c),
c_(1,1)=xi=S_1(z_1);z_1=-z_1(S_1-);z_1.
```

These are `homParityShiftCommute` and `homParityShiftAdd`, not new choices.
The even word-comparison supplied by them is

```
E_rs = S_(k_s)(beta_(M_s,k_r)^-1 at M_r(-));
       c_(k_s,k_r)(Q_rs(-)) : F_rs -> S_t Q_rs.        (3)
```

Consequently the prescribed shifted factor crossing is the ordinary even
transport `E_rs;S_t(B_rs);E_sr^-1`. To compute it, do not assume that the
following removal is even:

```
Theta_rs=S_(k_s) M_s(z_(k_r)(M_r(-)));z_(k_s)(Q_rs(-))
        : F_rs -> Q_rs,       |Theta_rs|=t.
```

Expansion of beta inverse in (3), followed by
`c_(k_s,k_r);z_t=S_(k_s)(z_(k_r));z_(k_s)`, cancels adjacent maps and gives
`E_rs;z_t=Theta_rs`. The displayed identity for c includes its negative
bare double-removal sign when both indices are 1. Hence the prescribed
crossing, with its sign derived rather than stipulated, is

```
Bhat_rs=(-1)^(td) Theta_rs;B_rs;Theta_sr^-1
       =Theta_rs;B_rs;Theta_sr^-1,                   (4)
td=b(R+S)RS=0.
```

In particular an odd Theta occurs only when the raw crossing is even.
This is why (4) has coefficient 1; arbitrary odd conjugation would not
justify it. The degree of Bhat is d. Naturality on a degree-e Hom map
has exponent `te+de+te=de`. The entire construction therefore acts on the
full Hom supercategories, not only their even parts.

Now move the pair of probes past a reservoir colour a of parity A.
Use `u_r=(b+A)R`, `u_s=(b+A)S`, and let j_rs be the pair of even inverse
associators from `L_a Q_rs` to `Q_rs L_a`. The two consecutive J maps give

```
K_rs:B_r B_s A_a -> A_a B_r B_s,
K_rs=(-1)^(A b R S) L_a(Theta_rs);j_rs;
                         Theta_(rs;b+A)(L_a(-))^-1. (5)
```

For completeness, the expansion first cancels the inner `z_(u_r)^-1`
and `z_(u_r)`. Moving the remaining degree-k_r map through `z_(u_s)`
contributes `(-1)^(u_s k_r)`. Replacing the remaining bare removals by
Theta contributes `(-1)^(k_s k_r)`. Their sum is
`(u_s+k_s)k_r=A b R S`. All associators are even. This proves (5) for
arbitrary contents, not just equal probe colours.

The coefficient of (5) is unchanged on exchanging r,s. Substituting (4)
in the two boundary paths, the adjacent Theta inverse pairs cancel; the
paths become the same coefficient times

```
L_a(Theta_rs);L_a(B_rs);j_sr;Theta_(sr;b+A)^-1,
L_a(Theta_rs);j_rs;B_rs(L_a(-));Theta_(sr;b+A)^-1.
```

These are equal by associator naturality for the *fixed* B_rs. No odd
maps are commuted in this cancellation. Thus

```
L_a(Bhat_rs);K_sr = K_rs;Bhat_(rs;b+A)(L_a(-)).        (6)
```

Together with the general AA comparison of `MixedColourSectorBraid.md`
§3, this supplies both orientations of the paired comparison needed below.
The derivation identifies the beta/xi transport with Theta transport; it
does not select a factor crossing to enforce (6).

## 3. One typed graph for both two-by-two blocks

The following two columns give distinct instantiations of the same graph.
Every named map is at the unique adjacent position indicated by its source
and target, with all unused strands whiskered. A prime on a node is just
a node label, not a derivative.

| node | reservoir-middle block | probe-middle block |
| --- | --- | --- |
| V | A_i A_j B_i | A_i B_j B_i |
| Z | B_i A_j A_i | B_i B_j A_i |
| W | A_j A_i B_i | A_i B_i B_j |
| W' | A_j B_i A_i | B_i A_i B_j |
| Y | A_i B_i A_j | B_j A_i B_i |
| Y' | B_i A_i A_j | B_j B_i A_i |

Use these typed edges, never inverses of H or G:

```
H:V->W, Hbar:W->V, G:Y'->Z, Gbar:Z->Y'  (factor crossings),
u:V->Y, v:W'->Z                         (distinct-colour unit crossings),
ubar:Y->V, vbar:Z->W'                   (their Q-weighted returns),
J:W'->W, K:Y'->Y                       (same-colour shifted comparisons).
```

Thus `ubar=Q_u^V u^-1`, `vbar=Q_v^(W') v^-1`, where each Q is an
endomorphism in the displayed **target** coordinates (V and W'). The four factor crossings
have degree ph; u,v have degree ph; J,K have degree p. Set
`a=a(reservoir i,probe i)` on W and `b0=a(reservoir i,probe i)` on Y.
Use (1) on `(W,W')` and `(Y,Y')` respectively.

There are exactly two paths from each source to each target: the middle
same-colour crossing contributes its diagonal or its swapping entry;
all other crossings are single-entry maps. The two route matrices are

```
              source V                         source Z
P, target V   -q Hbar a H                       Hbar J vbar
P, target Z   -v J^-1 a² H                      q v J^-1 a J vbar

R, target V   -q ubar b0 u                      ubar K Gbar
R, target Z   -G K^-1 b0² u                     q G K^-1 b0 K Gbar.    (7)
```

In the reservoir-middle column, P is 121 and R is 212. In the
probe-middle column, P is 212 and R is 121. This records every diagonal
and swapping path; it is not a diagonal-only test.

The paired AA identity, respectively (6) for BB, and the same identity
for the reversed factor crossing give the explicitly typed equalities

```
H u^-1 K = J v^-1 G       : Y' -> W,
Hbar J v^-1 = u^-1 K Gbar : Z -> V.                  (8)
```

For example, the first equation compares moving a probe past the two
reservoir strands before or after their crossing in the first column;
the second uses the given reverse crossing, not an inverse of H. In the
second column the probe pair and reservoir strand exchange these roles,
and (6) gives exactly the same endpoints. No factor braid is used in (8).

## 4. All four entries of each block

Let `a_V` denote a(reservoir i,probe i) on V. Dot transport through H
and u gives

```
a H=epsilon H a_V,       b0 u=epsilon u a_V,
a² H=H a_V²,             b0² u=u a_V².              (9)
```

The local dot and spectator-dot signs are both included. The same rules
apply at Z. Transport through the equal-colour J or K has coefficient q
on a, so the lower diagonal `q J^-1 a J` becomes **+a** in the local
(reservoir i,probe i) coordinates. This is where retaining the corrected
matrix's lower diagonal matters.

For the lower-left entry of P-R, (7)--(9) give exactly

```
-v J^-1 H a_V² + G K^-1 u a_V²=0.                   (10)
```

For the upper-right entry, move the Q factor of vbar and ubar to the
common target V, retaining the i-dot belonging to that mixed crossing
and the middle j-dot. These
moves are unsigned: each monomial has even i exponent if i is odd and
even j exponent if j is odd. The result is

```
Q_cross,target (Hbar J v^-1-u^-1 K Gbar)=0.           (11)
```

Here Q_cross,target uses the probe i-dot and middle j-dot in the
reservoir-middle block, and the reservoir i-dot and middle j-dot in the
probe-middle block. Thus these are different dot arguments, not a common
probe-only scalar. Equivalently (11) is

```
(Hbar J vbar)-(ubar K Gbar)=0.
```

Equations (10) and (11) use the two separate equalities of (8). No Q
factor is cancelled or inverted. In particular (11) still holds if Q
vanishes or has zero divisors.

To evaluate both diagonals, let x,y,z denote the dots in execution
positions 1,2,3 of V or Z. In V, x is reservoir and z is probe; in Z,
x is probe and z is reservoir. Write `Q_x=Q_ij(x,y)`, `Q_z=Q_ij(z,y)`.
Factor squares and the Q-weighted returns give the following entries;
the signs epsilon arise from moving a through the one degree-ph crossing.

| block | P_VV | R_VV | P_ZZ | R_ZZ |
| --- | --- | --- | --- | --- |
| reservoir-middle | `-q epsilon a(x,z) Q_x` | `-q epsilon a(x,z) Q_z` | `epsilon a(z,x) Q_x` | `epsilon a(z,x) Q_z` |
| probe-middle | `-q epsilon a(x,z) Q_z` | `-q epsilon a(x,z) Q_x` | `epsilon a(z,x) Q_z` | `epsilon a(z,x) Q_x` |

Here Q commutes with the a factor by its separate support; this is not
a claim that all dots commute. For the first column of nodes subtract
R from P. Its V entry is `-q epsilon F(x,y,z)` and its Z entry is
`-epsilon F(z,y,x)`. By (2), both equal `-q C_ij(x,y,z)`, in their own
execution coordinates. For the second column subtract P from R instead;
the same two answers result. Thus both entire matrices are

```
path(121)-path(212)
  = [ -q C_ij|V       0          ]
    [     0       -q C_ij|Z      ].                 (12)
```

This proves the stated two-by-two block identities as written component
arguments. The off-diagonal maps need not be endomorphisms of one common
object; their source and target are the different nodes V,Z. No unsigned
identification of those nodes or invertibility of the factor H,G was used.

## 5. Coverage and the remaining typed tests

The four mixed sectors here, the two mixed sectors ABA/BAB of
`MixedColourSectorBraid.md`, and the AAA/BBB relations of the full factor
actions account for iji. All arguments retain arbitrary content b and
arbitrary homogeneous Hom morphisms. Whiskering by an external prefix
changes b to its content; suffix whiskering applies the same superfunctor
to both sides. Coherence maps used for rebracketing are even.

This does not assert the iij/ijj/ijk tests. To specify what remains,
let `F_(w,s)` be the content-indexed word functor for colour word w and
sector word s. Let
`T_a(w)[t,s]:F_(w,s)->F_(s_a w,t)` be the corresponding full crossing
entry, including (1), the Q-weighted unit return, or the fixed factor
crossing as appropriate. For each w of type iij, ijj, or pairwise-distinct
ijk and each pair of input/output sector words s,t, the exact remaining
map equation from `F_(w,s)` to `F_(reverse(w),t)` is

```
sum_(u,v) T_1(s_2 s_1 w)[t,v] T_2(s_1 w)[v,u] T_1(w)[u,s]
 =
sum_(u,v) T_2(s_1 s_2 w)[t,v] T_1(s_2 w)[v,u] T_2(w)[u,s].       (13)
```

All u,v range over A/B words of length three; inadmissible entries are
zero by their sector types. The all-one-factor components use the factor
axioms. The mixed components of (13) are not discharged merely by (8):
their Q placements and, in iij/ijj, their full same-colour matrix paths
still require expansion. Formula (13) is an open target, not a premise
inserted into a purported fused-action theorem.

No Lean verification is claimed for this note. Integer word shifts,
localization comparisons, augmented inverses, fused local inversion,
bubble normalization and separation remain separate obligations.
