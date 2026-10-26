# Execution-order braid normalization

**Status: written mathematical comparison, not a Lean theorem.** This is
conditional on the two-strand construction in `CrossingNormalization.md` and
on the stated factor actions. The headline calculation is the exact
execution-order braid correction with the fixed polynomial Q. Its downstream
use is to compare a localized crossing with the fused action without
mistaking a reversal of strand order for a change of Q. The even rational
calculation below supplies that sign comparison. It does not construct the
odd localized sector comparison or prove the full fused action.

## 1. Two strand orders, not two choices of parameters

Products of operators are functional order; the rightmost operator acts
first. Let x,y,z be the dots in **execution** positions 1,2,3. Thus the
functors are applied first at position 1, then 2, then 3. The SKM displayed
strand order is the reverse: its left, middle, right dots are z,y,x.
This is the same order reversal used in `DeformedMixedBraid.md` §1.

Write p=|i|, h=|j|, q_i=(-1)^p, s_i=-q_i. On the displayed word iji, the
fixed relation in `QuiverHecke/MixedRelations.lean`, `braid_iji`, and in
`SKM/Presentation.lean`, `relation` at `braidEq`, has correction

```
C_ij(x,y,z) = sum_(r,s) c_(r,s) sum_(0<=b<r)
               (-1)^(p(h+b)) x^(r-1-b) y^s z^b.              (1)
```

Here `Q_ij(u,v)=sum c_(r,s) u^r v^s`, with exactly the support of the
fixed scalar datum, including its pure terms. The term r=0 contributes
nothing. The support restrictions are `pr=0`, `hs=0` modulo two, separately.
The ordered products in (1) are functional products, as in `braid_iji`.

Let B_ex be execution-position 121 minus 212, keeping chronological order
within each three-crossing path. Execution 121 is displayed 212, and vice
versa. Therefore its required value is

```
B_ex = -C_ij(z,y,x) = s_i C_ij(x,y,z).                       (2)
```

The second equality is an identity in the skew-dot algebra, not a renaming
of commuting variables. For one summand set a=r-1-b. Reordering
`z^a y^s x^b` to `x^b y^s z^a` costs
`(-1)^(pab+phs(a+b))`. The second exponent vanishes by hs=0. Relabel
b as r-1-a. The resulting sign differs from `(-1)^(p(h+a))` by
`(-1)^p`, since pr=0. This proves (2) for every allowed exponent.

Consequently the execution-order correction is:

| repeated colour i | middle colour j | B_ex |
|---|---|---|
| even | either parity | `-sum c sum x^(r-1-b)y^s z^b` |
| odd | even | `sum c sum (-1)^b x^(r-1-b)y^s z^b` |
| odd | odd | `-sum c sum (-1)^b x^(r-1-b)y^s z^b` |

The last row retains the sign from the middle odd colour. In particular
“unchanged for odd i” means unchanged relative to (1), which already
contains that sign. For iii, iij and ijj the correction remains zero.

There is no square-parameter change: execution ij has displayed colours
ji and dots y,x. Its square is `Q_ji(y,x)=Q_ij(x,y)`. Separate parity
support ensures that ordering these monomials introduces no extra sign.
Thus (2), the fixed square Q, and the reversed slides belong to one
consistent presentation. Comparing the execution braid to **+C** for even
i would compare different presentations. This is not an automorphism
obtained by negating equal-colour generators of the displayed presentation.

## 2. Exact even rational calculation

Work over the rational function field in x,y,z in characteristic zero
(or wherever the displayed denominators are units), with permutation
operators acting by substitution. Fix two colours i<j. Use

```
D_a = (x_a-x_(a+1))^-1 (s_a-1)       on equal colours,
tau_a = s_a                         on source colours ij,
tau_a = Q_ij(x_a,x_(a+1)) s_a        on source colours ji.   (3)
```

In the last line the coefficient is in the **target** ij coordinates.
These conventions give the square Q on both source words. In particular
`y D-D x=1` and `D y-x D=1`: (3) is the negative of the historical
Demazure operator. No factor crossing is rescaled in the resulting action.

Put `S=s_1 s_2 s_1=s_2 s_1 s_2`. For source iji the chronological paths
in functional operator order are

```
L = [Q_ij(x,y)/(x-z)] (S-1),
R = [Q_ij(x,y) S-Q_ij(z,y)]/(x-z).
L-R = [Q_ij(z,y)-Q_ij(x,y)]/(x-z).                       (4)
```

Thus L-R is exactly (2), not its negative. Expansion of each monomial of
Q gives the first row of the table. The iij and ijj paths agree by
`D_a f = s_a(f) D_a + (s_a(f)-f)/(x_a-x_(a+1))`; the two derivative
terms cancel. For iii the ordinary divided-difference braid applies to
D: changing the sign of all three factors changes both sides equally.
Alternatively expand `(s_a-1)/(x_a-x_(a+1))` in the six permutation
operators; the two expansions agree coefficient by coefficient.

Equations (3)–(4) were also expanded symbolically with an uninterpreted
function Q: iii and iij have zero difference, and iji has only the
identity-permutation coefficient displayed in (4). This is an algebraic
check of the written calculation, not a finite-height proof of fusion.

## 3. Even sector gauge and the direction of distinct-colour maps

In stable factor-dot coordinates on AB,BA for one even colour, write
`a=(x-y)^-1`. The rational shuffle block from (3) and its diagonal gauge are

```
T_rat = [[-a,a],[-a,a]],   g=diag(1,a),
g T_rat g^-1 = [[-a,1],[-a^2,a]].                       (5)
```

Replacing the matrix unit by the specified even J:BA→AB gives exactly
the proposed corrected matrix. The off-diagonal entries, not only their
product, fix the direction of this gauge.

For distinct colours use a separate symbol `U_ij:A_i B_j→B_j A_i` for the
specified unit interchange. The return map is `Q_ij U_ij^-1`, evaluated
in the appropriate source coordinates. This is the direction specified
by the distinct-colour paragraph of `NondegeneracyProof.md`; it is NOT
the direction assigned to the equal-colour symbol J. Conflating these two
uses of “J” reverses the gauge factor.

If the raw rational AB→BA coefficient in (3) is P (either 1 or the
appropriately evaluated Q), set the inversion-gauge ratio `g_BA/g_AB=1/P`.
Then the two gauged coefficients are 1 and Q. The equal-colour ratio is
instead a, as in (5). For a word take the product of these pair factors
over B-before-A inversions. In the even case these factors commute.
For two same-sector equal-colour strands the opposite-sector inversion
factors are symmetric in the two dots, hence commute with D. For two
same-sector distinct-colour strands the permutation transports their
inversion factors exactly, hence the same-sector crossing is unchanged.
This gives the even comparison with fixed factor conventions, provided
the factor rational realizations and shuffle identifications are supplied.

The gauge can be computed in the full rational field, where Q is also
invertible. Its final crossing entries are 1,Q,a,a² and the fixed factor
crossings; no Q inverse survives there. This does not prove that the
smaller algebra localization used for fusion is injective or central.
A claim about that smaller localization needs its own argument.

## 4. What the super comparison still has to prove

Equation (2) resolves the correction sign for even, odd and mixed parity;
it does not identify the odd Mackey blocks. In particular the formal
comparison described in `CrossingNormalization.md` §3 has the right
braid sign **when its input correction is (1) and its output is read in
execution order**. Scaling by s_i changes the correction to (2).
The fixed same-sector factors must be compared in that same order.
No scalar scaling inside a single fixed presentation is being asserted.

For the odd case a commuting scalar inversion gauge is not justified.
The specified J is odd when both colours are odd, and the odd equal-colour
rational coefficient is odd. Moving either across another homogeneous
entry has a sign. An even-case product of rational factors is therefore
not a proof of a super-sector gauge, even though a² has the required
commutations with its own two dots.

The exact outstanding comparison is a family of homogeneous sector
identifications H_P, with their shifts specified, such that for every
adjacent pair

```
H_target T_localized H_source^-1 = T_fixed,              (6)
```

where the equal-colour cross block is
`[[-q_i a,J],[-J^-1 a²,q_i J^-1 a J]]`, the distinct-colour blocks have
unit direction U and return direction Q U^-1, and same-sector blocks
are the fixed factors. The H_P must use the content-shifted comparisons,
not replace them by unsigned permutation operators. Three-strand
compatibility must retain all their Koszul signs. `HomSectorTransport.md`
§4 derives J for one colour and records the change of content shift for
different colours; it does not specify or prove (6) for all multicolour
words. The existence of a rational representation satisfying the abstract
relations (`Realization/Functor.lean`, `rep`) is not that comparison.

Hence there is **no normalization obstruction forcing a change of Q**
in (2)–(5). The even sign issue has a local comparison repair, not a new
research route. The unresolved odd/mixed obligation is (6) and the
localization step, rather than an unexplained sign in the iji correction.
No change to the fixed factors, swapping maps, dots or scalar datum is
made. Historical C,D, their normalized mates, conditional feedback
nilpotence, and the open residual inversion remain as in
`CrossingNormalization.md`; none is inferred from this braid calculation.