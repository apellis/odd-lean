# Equal-colour crossing normalization and central mates

**Status: written two-strand convention repair; not a Lean theorem or a fusion
theorem.** The old assertion in `NondegeneracyProof.md`
§5.3 that its mixed matrix satisfied the fixed library slides is withdrawn.
The error is visible for an even colour. This note changes only the two
position-preserving cross-sector entries; all factor maps, dots, adjunctions
and sector-swapping entries remain fixed.

## 1. Orders and the defect

Write `f;g` for execution order; matrix products below are functional order,
with target rows and source columns. An execution word AB means first the
reservoir A, then the probe B, hence functional order B'A. Put `q=(-1)^p`.
On AB the first dot is x (reservoir) and the second is y (probe), with
`xy=q yx`. On BA write u for the first (probe) dot and v for the second
(reservoir) dot. The specified comparison is

```
J:BA -> AB,
J=L(z_kappa M);j;z_(kappa+p)(ML)^-1,
J u=q y J,    J v=q x J.                              (1)
```

These are the same-factor dot transports in `HomSectorTransport.md` §4,
not an unsigned permutation of dots. The two z comparisons give parity p
to J; x,y,u,v,a and the crossing all have parity p. Scalars are even.
Set `F=diag(x,u)` and `S=diag(y,v)`. The library's `slide_right` and
`slide_left` in `OddMath/SKM/RouquierData.lean` say, respectively,

```
t;secondDot - q firstDot;t = 1,
secondDot;t - q t;firstDot = 1.
```

In functional order these are **S T-q T F=1** and **T S-q F T=1**.
They are not `T F-q S T=1` and `F T-q T S=1`.

Define the historical rational coefficient

```
a=(x-y)^-1                         (p=0),
a=(x-y)(x^2-y^2)^-1                 (p=1).
```

Nilpotence of x and invertibility of y make these denominators units.
Direct multiplication gives

```
a x-q y a=1,    x a-q a y=1,
y a-q a x=-q,   a y-q x a=-q.                         (2)
```

For odd p the first two numerators are `x^2-y^2`; for even p they
are x-y. The last two follow by multiplying the first two by -q and
rearranging. Therefore the old matrix
`Told=[[a,J],[-J^-1 a^2,-J^-1 a J]]` satisfies the required slides with
right side **-q**, not 1. At p=0 this is -1; at p=1 the error disappears.
This is not fixed by renaming functional AB as execution AB while keeping
its dots and mates unchanged.

## 2. The repaired two-strand matrix

Put `s=-q`, `b=s a`, `c=-J^-1 a^2`, `d=-J^-1 b J`. The proposed matrix is

```
Tnew = [[-q a,          J],
        [-J^-1 a^2,    q J^-1 a J]].                 (3)
```

On AB, (2) gives `y b-q b x=1` and `b y-q x b=1`. On BA, conjugating
`v d-q d u` by J gives `-q(x b-q b y)=1`, and conjugating
`d v-q u d` gives `-q(b x-q y b)=1`. Thus both diagonal slides hold.
For the upper-right entries use `y J-q J u=0` and `J v-q x J=0`.
For the lower-left entries use `u=q J^-1 y J`, `v=q J^-1 x J` and
commutation of a^2 with both x and y. In particular

```
v c-q c x = -q J^-1(x a^2-a^2 x)=0,
c y-q u c = -J^-1(a^2 y-y a^2)=0.
```

The commutation is immediate in the even case; in the odd case
`a^2=(x^2+y^2)(x^2-y^2)^-2`, a rational expression in central squares
inside this two-dot algebra. No global central-localization claim is used.
Since b^2=a^2 and d=-J^-1 b J, the four entries of Tnew squared are

```
b^2+J c=0,             b J+J d=0,
c b+d c=0,             c J+d^2=0.                   (4)
```

For example `c b+d c=-J^-1 b^3+J^-1 b^3=0`. This proves both slides
and the square symbolically with the actual transport (1). Given J, the
AB slide determines b uniquely by the nilpotent/invertible Sylvester
argument; the square then forces d and c. The same-sector blocks already
have the factor slides and square and are untouched. Distinct-colour
cross-sector entries are untouched as well.

## 3. What the diagonal gauge does, and does not, establish

There is a useful comparison with a *consistently old-sign* family, not
with the inconsistent old matrix plus the fixed factor crossings. For
any coloured sector word P let

```
G_P=product_i (-q_i)^(number of pairs B_i before A_i in P).
```

This is an even scalar involution, preserving all dots, parity and integer
shifts. An adjacent equal-colour cross-sector swap has target/source G
ratio `s_i=-q_i`. All same-sector swaps and all distinct-colour swaps
have ratio one. If every equal-colour crossing of a comparison family
is first multiplied by s_i, then conjugation by G gives exactly (3)
on cross-sector pairs: the diagonals acquire s_i, and each swapping
entry acquires s_i twice and is unchanged. On same-sector pairs this
operation instead gives **s_i times the old factor crossing**.

Consequently this is compatible with the fixed factors only when the
comparison family uses `s_i times the fixed factor crossing` to begin
with. It does not authorize negating the specified factors in the result.
The old text used fixed factors and the opposite-sign even cross diagonal,
so its claimed single global comparison was not established.

For the purely even rational comparison in `NondegeneracyProof.md`, the
old Demazure expression is `(x_1-x_2)^-1(1-swap)`. Its negative has the
fixed slides. After the preceding sign transport, the equal-colour factor
in the old inversion gauge changes from `-(x-y)^-1` to `+(x-y)^-1`.
The extra G is scalar and does not spoil any *proved* dot or same-sector
intertwining of that gauge. The needed factor/Demazure comparison must
use this negative Demazure convention on all same-colour pairs.

This explains the local repair, but is not a proof of the full braid.
For an iii word both sides of the homogeneous braid acquire `s_i^3=s_i`.
For iij or ijj each braid path crosses the repeated-colour pair once,
so both paths acquire the same s_i or s_j. For iji, i distinct from j,
each path also has exactly one equal-colour crossing, hence its braid
**difference** acquires s_i. A dot-polynomial correction on the same
idempotent is unchanged by G. Thus a comparison presentation must have
braid correction s_i times the fixed correction before transport; one
cannot just negate equal-colour generators in the *same* multicolour
presentation with Q unchanged. Distinct-colour squares are unchanged.

Remaining obligation: compare the rational embedding, its same-sector
factor generators, and its mixed-colour braid correction with the fixed
library presentation (including the direction of the Q difference
quotient), then verify the localization and gauge comparison. The odd
rational/Clifford comparison and central-localization source gaps remain
open. No braid is inferred from two-strand checks, and no change of Q,
factor convention or research route is made here.

## 4. Literal mates, normalized mates and the residual

Retain **historical variables C,D**, namely the literal partial mates of
the old diagonals a and `-J^-1 a J`. Their finite ordered expressions are
`HomCentralFeedback.md` (3)–(5), carried over from the central calculation
at `d6587276724195731cf007c99b754d941f091dec`. In execution order,

```
C=sum_r q^r cap_B(-r-1);cup_A(r),
D=-sum_s q^(s+1) cap_A(s);cup_B(-s-1).
```

Linearity of the partial mate, with the same adjunctions and comparison
maps, gives the literal new entries

```
Cnew=-q C,    Dnew=-q D,
Knew=[[0,Cnew],[Dnew,0]]=-q [[0,C],[D,0]].             (5)
```

Thus C,D are also the cross-sector blocks of the **normalized new mate**
`-q sigma_new`, since `(-q)^2=1`. They are not the literal new blocks.
This reconciles the convention in `FusedFeedbackComparison.md` (9) with
the direct historical mate computation; no cup or cap is rescaled.
In particular the two swapping partial mates in `HomSwappingMates.md`
are unchanged, as their upward entries J and `-J^-1 a^2` are unchanged.

Keep the whole sector augmented matrices and their inverses fixed,
including `c(k)`, `gamma(0)=q`, all dotted windows and intrinsic left
closures `b_(s,r)=U_r;f;V_s`. With `I=diag(I_A,I_B)`, the feedback is

```
Tfeedback=I_B;Cnew;I_A;Dnew=I_B;C;I_A;D.
```

Hence `HomCentralFeedback.md` (10)–(12) and its fixed-content nilpotence
argument are unchanged, conditional on the stated probe augmented inverse.
No identification of intrinsic left closures with right closures is made.
But set `Anew=1+Knew I`, `Bnew=1+I Knew`: all-height residuals are

```
Snew_+=[w a0-w I Anew^-1 Knew a0; -b0 Anew^-1 Knew a0],
Snew_-=[b0 z-b0 Knew Bnew^-1 I z, -b0 Knew Bnew^-1 a0]. (6)
```

These are functional-order products on the parity-completed sums, with
exactly the original positive/negative identity windows. Keeping old K
in (6) would be wrong even though the feedback is unchanged. In fact
if `G0=diag(1,-q)` on the central A/B sectors, then
`Knew=G0 Kold G0^-1` and `Anew=G0 Aold G0^-1`; this does not identify the
residuals unless their window maps are transported too. Here the specified
window maps are retained, not gauged away. Computation of w,z and residual
inversion, integer word-shift coherence, full (TC), fusion and separation
remain open. The separate `HomProbeMatrix.md` supplies the probe-sector
comparison conditional on the specified factor local inverse data.
