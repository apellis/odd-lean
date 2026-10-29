# Zero-correction mixed-colour braid components

**Status: proposed written proof, not a Lean theorem.** This evaluates the
component equations (13) of `MixedColourBlockCompletion.md` for iij, ijj
and pairwise-distinct ijk. The unequal-probe comparison used here is the written calculation
in that note, with its prescribed beta/xi maps. The conclusion is
conditional on the specified separated Hom data and full multicolour
factor actions. It does not follow from `RouquierFamily` alone and does
not assert a fused action or nondegeneracy.

The source target is Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Definition 1.5, equation (1.9), in its zero-correction
cases. The parameter conditions are (1.2)–(1.4). In the library compare
`QuiverHecke/MixedRelations.lean`, `braid_ne`, and the two distinct-colour
square declarations. Reversing displayed strand order to execution order
interchanges the two braid paths, which leaves these zero equations intact.

## Checked three-distinct-colour two-probe sectors

`BraidMixed/DistinctProbeSector.lean` proves `distinctProbe_braid`, the entry
`PᵢPⱼRᵣ → RᵣPⱼPᵢ` for pairwise distinct colours and a valid reservoir step.
It reduces both finite sums by endpoint-wise uniqueness of the sector paths.
`distinctProbe_left` and `distinctProbe_right` identify the literal probe
edges with `preCrossNe`, including the equality transports between the two
probe orders; `distinctProbe_move_heq` identifies the other two-edge paths
with the two prescribed mixed interchanges. A typed transport lemma aligns
the raw triangle before applying `homMixedInterchange_pair_cross`; the two
content-shift signs multiply to one. No factor braid, transported-dot law,
Q invertibility or cancellation of a probe crossing is assumed.

The importing consumer uses `Fin 3`, colours `0,1,2`, and reservoir content
`single 2 1`. This is a checked occupied-sector application with arbitrary
representation data, not a nonzero representation construction. The reverse
Q-weighted direction for distinct probes is now proved by
`BraidMixed/ReverseDistinctProbeSector.lean`, `reverseDistinctProbe_braid`.
It derives the unequal-probe Q transport from the actual signed dot slides
and supernaturalness, retains both Q factors with their shared reservoir
spectator, and cancels only mixed comparison isomorphisms.

`BraidMixed/MiddleDistinctProbeSector.lean` proves `middleDistinctProbe_braid`,
the middle placement `PᵢRᵣPⱼ → PⱼRᵣPᵢ`. Transport of the individual inner
Q factor uses the prescribed unequal-probe slide and supernaturalness; the
forward braid and mixed comparison isomorphisms then give the middle braid
without cancelling Q or a probe crossing. Its importing consumer retains
arbitrary colours and arbitrary occupied content. Thus all three
pairwise-distinct two-probe placements have explicit sector lemmas.

`BraidMixed/DistinctReservoirSector.lean` now proves the forward unequal-reservoir
placement `PᵢRᵣRₛ → RₛRᵣPᵢ` as `distinctReservoir_braid`. The actual
sector sums reduce by endpoint uniqueness; the prescribed `postCrossNe`
edges and all endpoint transports are retained. This coefficient-one placement
uses the shifted interchange triangle without cancelling a Q factor or crossing.

Reverse and middle unequal-reservoir placements, same-side factor-braid
transport and arbitrary-path assembly remain open. Repeated-outer corrections
are separate obligations. The complete component calculation below retains
its proposed status.

## 1. Typed entries and polynomial conventions

Words are in execution order. Products of maps below act rightmost first;
a semicolon instead denotes chronological composition. Every word functor
is based at an arbitrary reservoir content and probe weight, and every
edge uses the weight reached by its prefix. All identities are components
on an arbitrary Hom object, and are natural on homogeneous morphisms of
any parity. No parity is attached to a Hom object.

Write p_r for the parity of colour r. On distinct colours define

```
c_rs^{XY}: X_r Y_s -> Y_s X_r,
c_rs^{AA}=C_rs,             c_rs^{BB}=Bhat_rs,
c_rs^{AB}=J_rs^-1,          c_rs^{BA}=Q_sr(x_A,x_B) J_sr.       (1)
```

Here `J_rs:B_s A_r -> A_r B_s` is the prescribed shifted inverse
associator, not a freely selected isomorphism. In the BA entry the
polynomial is evaluated AFTER J, on the target `A_s B_r`. Thus its
arguments are the s-coloured reservoir dot and r-coloured probe dot.
Every c has degree p_r p_s. Whiskering by the unused strand is understood
in each use of (1), never an identification of different word objects.

For equal colour r, put q=(-1)^{p_r}. On the mixed pair, with target rows
and source columns ordered AB,BA, use precisely

```
D_r = [ -q a          J             ]
      [ -J^-1 a²     q J^-1 a J    ],                         (2)
a(x_A,x_B) = (x_A-x_B)^-1                         if p_r=0,
a(x_A,x_B) = (x_A-x_B)(x_A²-x_B²)^-1              if p_r=1.
```

On AA and BB, D_r is the fixed factor crossing. The only denominators
in this note are those of (2), which already exist by reservoir-dot
nilpotence and probe-dot invertibility. No factor crossing, Q polynomial,
or difference of two reservoir dots is inverted.

For distinct r,s retain the complete datum
`Q_rs(u,v)=sum c_mn u^m v^n`, with separate conditions
`p_r m=0` and `p_s n=0`. This includes both pure leading terms in the
connected case. For disconnected colours it is the single constant t_rs.
In particular every supported power of each individual dot is even;
this is stronger than total evenness of Q. The symmetry is
`Q_rs(u,v)=Q_sr(v,u)` with the indicated ordered dot arguments.

A distinct crossing transports either of its own dots with sign
`(-1)^(p_r p_s)`. A dot of degree e on the unused strand transports
with sign `(-1)^(p_r p_s e)`. The same statements hold for J and its
inverse, including equal colours. These are the local slides and
super-interchange, respectively. A Q monomial therefore transports
unsigned through any such map: each exponent annihilates its own dot
parity. Such Q polynomials also commute with each other and with mixed
a coefficients. These assertions do not make odd dots commute.

## 2. The comparison used for all three-strand triangles

Here is the component calculation underlying the unweighted triangles.
It is included to distinguish the argument from an assumption that the
mixed crossings satisfy braid. Put b=p(beta) and use even Hom functors
L_r and M_s. If t=b p_s and v=(b+p_r)p_s, then

```
J_rs=L_r(z_t(M_s(-)));j_rs;z_v(M_s L_r(-))^-1,
S_t(h);z_t=(-1)^(t |h|) z_t;h.                              (3)
```

The map j is the even inverse associator. Let P=L_s L_r and let
`C:P->P'` be the prescribed reservoir crossing of degree d=p_r p_s.
For a probe of colour a, set t=b p_a and w=(b+p_r+p_s)p_a. The pair
moving `B_a A_r A_s` to `A_r A_s B_a` expands as

```
K_P=P(z_t);jA_P;z_w^-1.                                     (4)
```

Indeed the two intervening comparisons with index `(b+p_r)p_a`
cancel adjacently. The pentagon expresses jA_P as reassociation across
the composite reservoir edge. Expanding C as that edge's crossing,
its two paths through jA become

```
C_(M_a X);jA_P' = jA_P;M_a(C_X).
```

After insertion of (4), the scalar on the first path is (-1)^(td)
and that on the second is (-1)^(wd). Their ratio is one, since
`(w+t)d=p_a(p_r+p_s)p_r p_s=0`. This proves the shifted triangle
for the actual C, with its fixed same-colour normalization when r=s.
The raw equality just used is associator naturality: after the adjacent
reassociation inverses cancel, only the factor crossing is nonidentity
and homogeneous. Hence there is no additional interchange sign there.

For two probes r,s and one reservoir a, set R=p_r, S=p_s, A=p_a,
`k_r=bR`, `k_s=bS`, `t=k_r+k_s`, and `Qfun_rs=M_s M_r`. The prescribed
even comparison E is formed from beta and the shift-addition comparison c:

```
E_rs=S_(k_s)(beta_(M_s,k_r)^-1);c_(k_s,k_r),
Theta_rs=S_(k_s) M_s(z_(k_r));z_(k_s),
E_rs;z_t=Theta_rs.                                          (5)
```

The last equality is the unequal-probe computation of
`MixedColourBlockCompletion.md` §2: substitute
`beta^-1=M_s(z_(k_r));z_(k_r)^-1` and
`c_(k_s,k_r);z_t=S_(k_s)(z_(k_r));z_(k_s)` and cancel the adjacent
inverse pair. The c identity includes the negative bare double-removal
sign when both indices are odd. Consequently, for the fixed raw crossing
B_rs of degree d=RS,

```
Bhat_rs=E_rs;S_t(B_rs);E_sr^-1
        =(-1)^(td) Theta_rs;B_rs;Theta_sr^-1
        =Theta_rs;B_rs;Theta_sr^-1,     td=b(R+S)RS=0.        (6)
```

Theta has degree t; it is not declared even. Expanding the two J maps
that move the probes past A_a gives

```
K_rs=(-1)^(A b R S) L_a(Theta_rs);jB_rs;
                         Theta_(rs;b+A)(L_a(-))^-1.         (7)
```

The first adjacent cancellation removes the internal z inverse. Passing
the remaining degree-k_r map across z_((b+A)S) contributes
`((b+A)S)k_r`; replacing the bare pair of removals by Theta contributes
`k_s k_r`. Their sum is A b R S. This is an arbitrary-index computation,
not an even-object calculation. The exponent is unchanged by r,s exchange.
Substitute (6) into both paths around (7). The adjacent Theta inverses
cancel, and both paths have the coefficient (-1)^(A b R S) multiplying

```
L_a(Theta_rs);L_a(B_rs);jB_sr;Theta_(sr;b+A)^-1
 = L_a(Theta_rs);jB_rs;B_rs(L_a(-));Theta_(sr;b+A)^-1.
```

After reassociation this is naturality of the even associator against
B_rs. Thus the triangle concerns the beta/xi-prescribed BB crossing; it
is not obtained by choosing a conjugation to enforce the equation.

For precision, all placements of the single opposite-sector strand follow
from one rectangular equation, not from cancellation of a factor crossing.
For two A strands and one B, name the objects

```
N=B_a A_r A_s,  M=A_r B_a A_s,  S=A_r A_s B_a,
N'=B_a A_s A_r, M'=A_s B_a A_r, S'=A_s A_r B_a,
I:N->M, H:M->S, I':N'->M', H':M'->S'.
```

All four I,H maps are J maps. Let C_N:N->N' and C_S:S->S' be the
factor crossings with their specified spectators. Equation (4) proves

```
C_S H I = H' I' C_N,
H'^-1 C_S H = I' C_N I^-1,                              (8)
I'^-1 H'^-1 C_S = C_N I^-1 H^-1.
```

The middle line follows by multiplying only by H'^-1 and I^-1; the
last follows by multiplying only by the displayed J inverses. These
are the three placements of B. Exchanging r,s supplies the other
orientation of the factor crossing, not its inverse. For two B strands,
exchange A and B in the object labels of this rectangle and take I,H
to be inverse J maps: the singleton A now moves right. Equation (7)
gives its first line after multiplication by the invertible paired
comparisons, without inverting Bhat. The same two rearrangements give
all placements of one A among two B strands, also when their colours coincide.
This proves every unweighted triangle needed below directly from (3)–(7).

## 3. Pairwise-distinct colours: every component

Let i,j,k be pairwise distinct, and let X,Y,Z each be A or B. There is
one possible output, ZYX, and one route on either side:

```
X_i Y_j Z_k --c_ij--> Y_j X_i Z_k --c_ik--> Y_j Z_k X_i
              --c_jk--> Z_k Y_j X_i,
X_i Y_j Z_k --c_jk--> X_i Z_k Y_j --c_ik--> Z_k X_i Y_j
              --c_ij--> Z_k Y_j X_i.                       (9)
```

For each arrow use (1) at the displayed position. Every other output
entry of (13) is zero, since none of these arrows branches. Strip only
the Q multiplier from a BA arrow, leaving J, and retain all factor
crossings. For mixed sectors the resulting equality is exactly one
of (8), or its BB rectangle. For AAA and BBB it is the given factor
braid, not a consequence of (8).

Each original pair of strands crosses once in each path. A Q factor
occurs precisely for an original B-before-A pair. By the unsigned
transport of §1 all these factors can be moved to the common target.
Write x_l for the target dot on the strand originally in position l.
The exact common multiplier and output are:

| source | target | multiplier in target coordinates |
| --- | --- | --- |
| AAA | AAA | 1 |
| AAB | BAA | 1 |
| ABA | ABA | Q_kj(x_3,x_2) |
| ABB | BBA | 1 |
| BAA | AAB | Q_ji(x_2,x_1) Q_ki(x_3,x_1) |
| BAB | BAB | Q_ji(x_2,x_1) |
| BBA | ABB | Q_ki(x_3,x_1) Q_kj(x_3,x_2) |
| BBB | BBB | 1 |

Multiplying the unweighted equality by this polynomial proves (13).
No common polynomial is cancelled. The table remains valid for a zero
divisor Q or a disconnected constant.

## 4. All iij and ijj path sums

Assume i differs from j. For iij let the input be X_i Y_i Z_j. The
first crossing on path 121 is D_i. For a possible output pair U,V of
that crossing the complete chronological routes are

```
121: X_i Y_i Z_j --D_i[UV,XY]--> U_i V_i Z_j
                 --c_ij^{VZ}--> U_i Z_j V_i
                 --c_ij^{UZ}--> Z_j U_i V_i,
212: X_i Y_i Z_j --c_ij^{YZ}--> X_i Z_j Y_i
                 --c_ij^{XZ}--> Z_j X_i Y_i
                 --D_i[UV,XY]--> Z_j U_i V_i.              (10)
```

The two occurrences of D are at different positions and contents; the
route displays specify them. Each admissible entry is one product on
each side, not a suppressed sum of several products. The possibilities
are UV=XY for AA or BB and UV in {AB,BA} for a mixed pair.

For ijj the exact corresponding routes, for input X_i Y_j Z_j, are

```
121: X_i Y_j Z_j --c_ij^{XY}--> Y_j X_i Z_j
                 --c_ij^{XZ}--> Y_j Z_j X_i
                 --D_j[UV,YZ]--> U_j V_j X_i,
212: X_i Y_j Z_j --D_j[UV,YZ]--> X_i U_j V_j
                 --c_ij^{XU}--> U_j X_i V_j
                 --c_ij^{XV}--> U_j V_j X_i.              (11)
```

Thus the support of all entries is explicitly:

| input | iij outputs | ijj outputs |
| --- | --- | --- |
| AAA | AAA | AAA |
| AAB | BAA | ABA, BAA |
| ABA | AAB, ABA | ABA, BAA |
| ABB | BAB, BBA | BBA |
| BAA | AAB, ABA | AAB |
| BAB | BAB, BBA | ABB, BAB |
| BBA | ABB | ABB, BAB |
| BBB | BBB | BBB |

Outside this table the sums in (13) vanish on both sides. Within the
table, (10) and (11), together with the four literal entries (2) and
(1), give every summand, with its source and target and its Q placement.
In particular the diagonal branch of D does not exchange its two
sector letters; ignoring that branch would omit entries in this table.

## 5. Repeated colour in different sectors: four matrix entries

Consider first (10) with XY mixed. Let R_AB and R_BA be the two-arrow
maps moving the j strand left past the respective i pair, INCLUDING
the Q factors in (1). Put J_s:BA->AB on the source pair and J_t:BA->AB
on the target pair, with the j strand whiskered in its indicated place.
Let a_s and a_t be (2) on the AB source and target. The following are
identities between differently typed word functors:

```
R_AB J_s = J_t R_BA,
a_t R_AB = R_AB a_s.                                      (12)
```

For the first identity, the Q-free paths are the middle rectangle (8)
for reservoir colours i,j and probe i when Z=A, or its probe rectangle
for probes i,j and reservoir i when Z=B. If Z=A, both paths carry one
Q_ji on the j reservoir and i probe; move it to their common target.
If Z=B, neither path has a Q multiplier. Transport through J_s or J_t
is unsigned for Q by separate support, proving the first identity
without cancelling Q.

For the second identity, each of the two distinct crossings transports
BOTH i dots with the same sign epsilon=(-1)^(p_i p_j): one is a local
dot, and the other is a spectator of parity p_i, so its sign is
`(-1)^(p_i p_j p_i)=epsilon`. Consequently the two-crossing transport
has sign epsilon squared, namely one, on each dot. Transport of the
mixed inverse follows by multiplying its two inverse identities; no
inverse of R is required. Q commutes with a. This proves the second
identity. It also proves `a_t² R_AB=R_AB a_s²`.

Write the left and right sides of (10) as R D_s and D_t R, respectively.
Their four entries are equal by the following explicit reductions:

```
AB->AB:  -q R_AB a_s = -q a_t R_AB,
BA->AB:       R_AB J_s = J_t R_BA,
AB->BA:  -R_BA J_s^-1 a_s² = -J_t^-1 a_t² R_AB,
BA->BA:   q R_BA J_s^-1 a_s J_s
                         = q J_t^-1 a_t J_t R_BA.          (13)
```

In the last two lines use only `R_BA J_s^-1=J_t^-1 R_AB`, obtained
from (12) by multiplying by J inverses. In particular no same-factor
crossing is cancelled, and the lower diagonal is the specified
`q J^-1 a J`, not a replaced scalar expression.

For (11) take R to move the i strand RIGHT past the j pair. Formula
(12) holds with i and j in the roles of spectator and repeated colour.
Its Q-free identity is again (8), now with its other placement. If X=A
there is no Q multiplier; if X=B there is one Q_ji on the j reservoir
and i probe, on both paths. The local/spectator sign calculation is
`(-1)^(p_i p_j)` twice on both j dots. The equality to prove is now
D_t R=R D_s, which is exactly the same four equations (13) with sides
exchanged and q=(-1)^(p_j). This supplies every mixed repeated-pair
entry of both tables, not merely the J entry.

## 6. Repeated colour in one sector: symmetric polynomial transport

There remain the entries where the repeated pair is AA or BB. If all
three letters agree, use the full factor-action relation. Otherwise
there is a single opposite-sector strand. The Q-free equations are the
boundary rectangle equations (8), including coincident factor colours.
For clarity the Q multipliers before comparison are as follows:

| colour word and sector | multiplier |
| --- | --- |
| iij, AAB | 1 |
| iij, BBA | Q_ji(z,x) Q_ji(z,y) |
| ijj, ABB | 1 |
| ijj, BAA | Q_ji(x,z) Q_ji(y,z) |

Here x,y are the two repeated-colour dots and z the other-colour dot,
with arguments placed by their colours. The two Q factors arise at
different stages in (10) or (11); their transport past distinct-colour
maps is unsigned. The remaining issue is passage through the
same-colour factor crossing D, where a derivative term must not be
ignored.

Write r for the repeated colour, h for the other colour's parity,
p=p_r, q=(-1)^p. By symmetry of Q express the multiplier as
`F=Q_rj(x,z) Q_rj(y,z)`. On its dot algebra the factor slides give

```
D f = s(f) D + delta(f),
s(x)=q y, s(y)=q x, s(z)=(-1)^(p h) z,
delta(x)=-q, delta(y)=1, delta(z)=0,
delta(fg)=delta(f)g+s(f)delta(g).                            (14)
```

These are polynomial identities; no rational expression on the two
same-sector dots is being introduced. For supported coefficients c_mn,
define the POLYNOMIAL G as follows:

```
p=0: G=sum c_mn sum_(0<=l<m) x^(m-1-l) y^l z^n,
p=1: G=(x-y) sum c_mn sum_(0<=l<m/2) x^(m-2-2l) y^(2l) z^n.
```

An empty inner sum is zero. In the second line all supported m are
even. Induction in (14) gives, term by term,

```
delta(Q_rj(x,z))=-q G,       delta(Q_rj(y,z))=q G,
s(Q_rj(x,z))=Q_rj(y,z),     s(Q_rj(y,z))=Q_rj(x,z).          (15)
```

For p=0 the induction is the finite geometric sum. For p=1 first
compute `delta(x²)=x-y`, `delta(y²)=y-x`; the even squares commute and
s exchanges them. Applying the product rule to their arbitrary powers
produces exactly the second line for G. Multiplication by z^n introduces
no further term or sign: delta(z^n)=0 and hn=0. This proves (15) for
every allowed exponent, including both pure leading terms and m=0.

Each Q commutes with G, by separate support. Therefore

```
s(F)=F,
delta(F)=(-q G) Q_rj(y,z)+Q_rj(y,z)(q G)=0,
D F=F D.                                                  (16)
```

Insert (16) into the weighted boundary rectangle. It moves the two Q
factors through the factor crossing without a residual term, proving
all four remaining mixed-sector cases of the table. For disconnected
colours G=0 and F is the product of the two prescribed constants; no
second constant leading term has been added.

## 7. Conclusion and boundary

Equations (9)–(16) evaluate every admissible path in equation (13) of
`MixedColourBlockCompletion.md`; nonadmissible outputs have zero paths.
The proof uses the fixed multicolour factor actions, the corrected
same-colour mixed matrix, prescribed shifted J, and beta/xi probe
transport. Its use of the unequal-probe calculation (5)–(7) is explicit.
The iji block result in that note is not used in the zero-correction
calculation.

All calculations hold at arbitrary content b and on full Hom categories.
An external prefix merely supplies the starting content; an external
suffix applies its superfunctor to both sides. The local spectator signs
are recorded in §§1, 5 and 6, while all reassociations are even. Only
already available mixed denominators are used. These are written
component arguments; Lean formalization remains outstanding;
coherent integer shifts, the remaining fusion relations, local inversion
and separation are not conclusions of this note.