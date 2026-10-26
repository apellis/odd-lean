# Parity-shift removal and the first factor-transport equation

**Status: proposed calculations, not a localized-action identification or a Lean theorem.**
The headline calculation is a signed odd AAB braid component together with the
forced two-sector comparison formula. Its downstream use is to test the
sector-identification equation in `ExecutionBraidNormalization.md` without
substituting a commuting scalar gauge for a homogeneous comparison. The
remaining factor-transport equation is displayed explicitly below. No Q,
factor crossing, dot, adjunction or corrected mixed entry is changed.

## 1. Content, rather than weight, determines the shifts

Let c be the parity of the initial reservoir content. In an execution word w,
a probe step B_j has shift

```
kappa_j(w) = p(j) (c + sum_(A_i preceding B_j) p(i)).       (1)
```

Removing a reservoir strand has the same effect modulo two as adding it.
This is precisely `homContentShift` and `homContentShift_add_single` in
`OddMath/SKM/RouquierHomContent.lean`. The functor of a B_j step is
`S_kappa M_j`, not M_j. The reservoir step is L_i. In particular a local
exchange changes kappa by p(i)p(j), not by p(i) alone for different colours.

There is an explicit shift-removal map for every word, before any rational
crossing comparison is made. Write F_w for the shifted functor, R_w for the
same word in raw L and M functors, and r_w:F_w -> R_w. Starting with the
identity, append execution steps by

```
r_(w A_i) = L_i(r_w),
r_(w B_j) = z_kappa(M_j F_w); M_j(r_w),                  (2)
```

where a semicolon denotes first the left map, then the right map. The second
line has source `S_kappa M_j F_w` and target `M_j R_w`. Its parity is the
sum of the kappa values encountered in w B_j. Inverses reverse these exact
composites. Associators are even and are suppressed here only.

This is a homogeneous removal, not an even identification. With
`S_t(f);z_t=(-1)^(t|f|) z_t;f`, consecutive bare removals obey

```
z_1(S_1 X);z_1(X) = -xi_1(X).                         (3)
```

Replacing (2) by an unsigned collapse of all shifts loses (3).
`homParityShiftCommute_pi` in `RouquierHomContentCoherence.lean` supplies
the same negative self-interchange.

For A_i and B_j let kappa=p(j)c, kappa'=kappa+p(i)p(j).
The cross-sector comparison in the BA -> AB direction is

```
J_ij = L_i(z_kappa M_j); j_ij; z_kappa'(M_j L_i)^-1.     (4)
```

Here j_ij:L_i M_j -> M_j L_i is the even raw associator comparison.
The inverse reverses (4). Thus |J_ij|=p(i)p(j). For equal colour this is
exactly the specified J, with kappa'=kappa+p. For different colours the
specified unit direction AB -> BA uses J_ij inverse. Formula (4) is not a
statement that both directions of the crossing are units: the other
crossing has its fixed Q factor.

For an odd single colour the shifts on AAB, ABA, BAA are respectively
c, c+1, c. In functional notation their functors are

```
S_c M L L,   L S_(c+1) M L,   L L S_c M.               (5)
```

Consequently neither of the two successive J maps can be replaced by the
same unsigned interchange. Formula (2) retains their different boundaries.

## 2. Why the odd scalar inversion gauge fails already for dots

On an odd mixed pair put xy=-yx and

```
a=(x-y)/(x^2-y^2).
```

The squares in this paragraph are central in the skew-dot algebra. Direct
multiplication gives

```
a x-x a = 2xy/(x^2-y^2),
a x+x a = 2x^2/(x^2-y^2).                             (6)
```

Thus conjugation by a neither preserves the reservoir dot nor negates it
in general. A parity shift can supply a sign, not either nonzero correction
in (6). The even proposal diag(1,a) therefore cannot simply be reused for
odd colours, even with a sign assigned to each inversion. This is an
obstruction to that proposal, not an obstruction to the corrected crossing.

## 3. The forced two-sector formula is not multiplication by a

Use functional products in this and the following sections. Suppose the
localized sector AB has been identified with the Hom sector by a dot
intertwiner h. Let k be the **BA -> AB entry of the localized crossing**,
not an unsigned permutation. The equation for the specified upper-right
entry J forces, uniquely,

```
H_AB=h,                 H_BA=J^-1 h k.                (7)
```

This follows by solving `h k H_BA^-1=J`; it does not posit a new comparison
axiom. If h is even then H_BA is even: k and J both have parity p. Their
signed transports of either dot cancel, so (7) preserves dots provided h
does. This is the missing distinction from (6).

For odd colour the localized diagonal is a once its dots and slides are
identified. Its zero square forces the return entry l to satisfy
`k l=-a^2` and the other diagonal to be `-k^-1 a k`. Consequently (7)
transports the whole two-sector crossing to

```
[[a, J], [-J^-1 a^2, -J^-1 a J]].                     (8)
```

For either parity the identical argument with b=-q a gives the corrected
matrix `[[-q a,J],[-J^-1 a^2,q J^-1 a J]]`.
On a nilpotent-reservoir/invertible-probe pair, both x^2-y^2 and x^2+y^2
are units by finite geometric series. Both diagonal squares are therefore
units. The two diagonal equations of the zero square are `k l=-a^2` and
`l k=-d^2`; these give both a right and a left inverse for k, which agree.
Thus k is invertible wherever the localized sector decomposition and its
square relation exist. This
argument uses only mixed denominators, not inverses of differences of two
reservoir dots. The distinct-colour square remains Q: conjugation transports
Q by the dot comparison, and introduces no replacement polynomial.

Equation (7) is a forced formula, **not a construction of h or k on the
Hom family**. The existing `Realization/Generators.lean` defines its
crossing as `gam * dres * sig`, with Clifford factors and reflected
rational coefficients; it does not provide an AB/BA decomposition of the
Hom functors. Its `Coefficients.lean` uses a total quotient ring, whereas
nilpotent reservoir dots cannot be obtained by simply evaluating arbitrary
fractions in that ring. A regular-module representation is therefore not
by itself a value for h. Formula (7) identifies exactly which off-diagonal
operator must be compared, rather than guessing its coefficient to be a.

## 4. One odd three-strand component closes without a scalar gauge

Take execution AAB of one odd colour, reservoir dots x,z and probe dot y.
They anticommute pairwise. Write D for the fixed reservoir crossing,

```
D^2=0,   D x+z D=1,   D z+x D=1,   D y=-y D,
f=(z-y)/(z^2-y^2),     g=(x-y)/(x^2-y^2).              (9)
```

Let J_23:ABA -> AAB be the shifted comparison in (4), at the appropriate
content. The AAB -> AAB component of execution 121 minus 212 is

```
D f D - f D f + J_23 a_(12,ABA) J_23^-1 f^2
  = D f D - f D f - g f^2.                            (10)
```

There are exactly two paths in the 212 component: the all-diagonal path
and the excursion to ABA and back. The latter uses return entry
`-J_23^-1 f^2`, explaining the plus sign before the conjugate in (10).
Conjugation of the probe dot by J contributes a minus, and moving the odd
J past the spectator reservoir dot contributes a second, separate minus
on that dot. Thus the odd rational function a_(12,ABA) becomes -g.
Omitting the spectator sign does not give (10).

For completeness the needed rational slide is derived, rather than
assuming a polynomial realization of D. Set s(x)=-z, s(z)=-x, s(y)=-y.
The relations (9) extend as `D h=s(h)D+delta(h)` with twisted Leibniz rule
`delta(uv)=delta(u)v+s(u)delta(v)`. Inverting only the mixed denominator
and using delta(z)=1, delta(y)=0 gives

```
s(f)=-g,
delta(f)=1/(z^2-y^2)
         +(x-y)(z-x)/((x^2-y^2)(z^2-y^2))
        =-f g.                                       (11)
```

The last equality follows by ordered multiplication from

```
x^2-y^2+(x-y)(z-x)=-(z-y)(x-y).
```

Therefore `D f=-g D-f g`. Substitution in (10) leaves
`f^2 g-g f^2=0`, since `f^2=(z^2+y^2)/(z^2-y^2)^2`.
This proves this component from the fixed slides, the shifted J transports
and the corrected matrix. It is neither a proof of every iii component
nor a proof of iij/iji coherence. The numerator identity and final
commutator can also be checked by exact increasing-order skew-polynomial
multiplication; no finite-height matrix model is needed.

## 5. Exact remaining comparison at the first repeated-factor boundary

Start with a putative sorted-sector identification h on AAB. Let
`k_23:ABA_local -> AAB_local` and `k_12:BAA_local -> ABA_local` be the
localized upper-right entries; let J_23 and J_12 be their fixed counterparts
from (4). Successive applications of the forced equation (7) give

```
H_ABA = J_23^-1 h k_23,
H_BAA = J_12^-1 J_23^-1 h k_23 k_12.                  (12)
```

All maps have their indicated sector boundaries. Their order is essential.
The first repeated-factor transport test after these two mixed exchanges is

```
D_fixed,BAA J_12^-1 J_23^-1 h k_23 k_12
   = J_12^-1 J_23^-1 h k_23 k_12 D_local,BAA.          (13)
```

Here D acts on the adjacent reservoir pair in BAA; the initial sorted
comparison must separately intertwine the adjacent reservoir pair in AAB.
Equation (13), with (4), (5) and the specified source k entries substituted,
is the concrete unevaluated equation. It cannot be replaced by symmetry
of a product of commuting inversion factors. Calculation (10) removes one
possible diagonal obstruction but does not evaluate (13).

The analogous distinct-colour transports must additionally retain the
unit AB -> BA direction and its Q return, and the execution iji correction
of `ExecutionBraidNormalization.md`. These have not been evaluated here.
No factor/Q replacement is indicated by (6) or (10). What is missing is the
sorted localized-module/Hom identification and its factor intertwining,
followed by (13) and the remaining multicolour components, not a new scalar
sign convention. Integer word shifts and the smaller-localization comparison
also remain open. None of the mate, residual, or nondegeneracy conclusions
is inferred from these calculations.
