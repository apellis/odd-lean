# Mixed-colour Hom interchange and repeated outer colours

**Status: proposed component derivation, not a Lean theorem.** The headline
result is the execution-order braid correction on the sectors `A_i B_j A_i`
and `B_i A_j B_i`, for `i != j`, with both colour parities and all reservoir
contents retained. Its downstream use is the repeated-outer-colour relation
for the prescribed Hom crossings. The calculation also gives paired
interchange for a general homogeneous reservoir crossing of degree
`p_r p_s`. It does **not** verify every sector of iji, or the complete
multicolour fused action. The remaining components are specified in §6.

## 1. Fixed conventions and admissible parameters

A word is in execution order; functors compose in functional order.
Semicolons mean first the left map, then the right map. Products of
operators are functional products. A Hom object X has no parity; a
homogeneous morphism `f:X->Y` has an arbitrary parity d.

Use the factor actions, the same-colour reservoir normalization
`-(-1)^p` of `HomPrincipalMate.md`, and the probe Theta transport of
`PairedHomInterchange.md`. A `RouquierFamily` alone is insufficient:
`RouquierData.cross_mem` supplies degree `p_r p_s`, but the family interface
only bundles the same-colour braid. Whenever an all-one-factor multicolour
relation is used, it is a relation of the given factor action, not a
consequence of that interface alone.

The source relation is Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Definition 1.5, with its parameter restrictions in §1;
compare `QuiverHecke/MixedRelations.lean`, `braid_iji`. Put

```
p=p_i, h=p_j, q=(-1)^p, epsilon=(-1)^(ph),
Q_ij(u,v)=sum_(r,s) c_(r,s) u^r v^s,
C_ij(x,y,z)=sum_(r,s) c_(r,s) sum_(0<=b<r)
                  (-1)^(p(h+b)) x^(r-1-b) y^s z^b.
```

Only coefficients with `pr=0` and `hs=0` contribute. These are separate
restrictions: `Scalars.s_eq_zero`, its symmetric counterpart from `s_symm`,
and `Datum.even_of_odd` for the pure terms. They are stronger than merely
saying Q has total parity zero. For disconnected colours Q is the single
constant `t_ij`, not a sum of two constant pure terms. The correction is
then zero. No coefficient is declared nonzero without the source's support
conditions. The ground ring is the library's purely even commutative ring,
with 2 invertible when odd colours occur.

The required execution correction, as derived in
`ExecutionBraidNormalization.md`, is

```
B_ex = path(121)-path(212) = -C_ij(z,y,x) = -q C_ij(x,y,z).    (1)
```

No change of Q is involved. The calculations below use factor slides and
polynomials only; they invert neither Q nor any same-reservoir difference.

## 2. Distinct-colour shifted interchange

At reservoir content beta write `b=p(beta)`. Let `L_i=homPre(E_i)` and
`M_j=homPost(E_j)`, with every edge indexed by its own content. Set

```
t=p_j b, v=t+p_i p_j,
j_ij(X):L_i M_j X -> M_j L_i X,
J_ij(X)=L_i(z_t(M_j X));j_ij(X);z_v(M_j L_i X)^-1
       : B_j A_i X -> A_i B_j X.                         (2)
```

Here j is the specified inverse associator and is even. The inverse of
(2) is the reversed word of inverse maps. Both inverse identities are
adjacent cancellations, not exchanges of homogeneous maps. Since
`S_t(f);z_t=(-1)^(td) z_t;f`, the naturality sign of J is
`(-1)^((t+v)d)=(-1)^(p_i p_j d)`. Thus (2) acts on the full Hom categories.

For distinct colours the **unit crossing** is

```
U_ij=J_ij^-1 : A_i B_j -> B_j A_i;
return crossing = Q_ij(x_A,x_B) J_ij : B_j A_i -> A_i B_j,   (3)
```

with Q in the target coordinates. This separates the direction of U from
that of J. It is the directed convention of
`ExecutionBraidNormalization.md`, not an identification of the equal-colour
matrix's upper-right J with U. Separate support of Q makes its transport
through J unsigned. In contrast, transport of either local dot through J
has coefficient `(-1)^(p_i p_j)`; a spectator dot of degree e has coefficient
`(-1)^(p_i p_j e)`. These follow from the two z comparisons and super
interchange, respectively. J is not a dot-commuting scalar gauge.

For equal colours the block remains exactly
`[[-q a,J],[-J^-1 a^2,q J^-1 a J]]`. No entry of that block is changed here.

## 3. Paired comparison across factor crossings

### Two reservoir strands, one probe strand

Allow reservoir colours r,s and probe colour j. Put
`P=L_s L_r`, `P'=L_r L_s`, with the corresponding changed edges, and let
`C:P->P'` be the reassociated specified factor crossing. Its degree is
`d=p_r p_s`; this is not replaced by p_r or p_s. Set

```
t=p_j b, v=t+p_j p_r, w=t+p_j(p_r+p_s),
R0=P(z_t(M_j X)),       R2=z_w(M_j P X).
```

Moving B_j past the two A strands using (2) gives

```
K_P : B_j A_r A_s -> A_r A_s B_j,
K_P=R0;jA_P;R2^-1,                                     (4)
```

where `jA_P` is the pair of inverse associators. The intermediate
`L_s(z_v^-1);L_s(z_v)` cancels adjacently. Use the corresponding formula
with P' for the exchanged reservoir word. Pentagon coherence identifies
jA with reassociation across the composite reservoir edge. After inserting
C, associator naturality gives

```
C_(M_j X);jA_P' = jA_P;M_j(C_X).
```

There is no sign here: only C is nonidentity and homogeneous; all
associators and identity whiskers are even. Moving C past R0 in the first
full path costs `(-1)^(td)`; moving it through R2 in the second costs
`(-1)^(wd)`. These agree because

```
(w+t)d = p_j(p_r+p_s)p_r p_s = 0 in Z/2.                (5)
```

Consequently

```
C_(S_t M_j X);K_P' = K_P;S_w M_j(C_X).                 (6)
```

This proves a paired comparison for different as well as equal reservoir
colours, without assuming its desired shifted equation. For `r=s=i`,
w=t and the common sign is `(-1)^(t p_i)`. The reservoir normalization
remains inside C on both sides.

### Two equal probe strands, one reservoir strand

Now let the probes have colour i and reservoir colour j. Put
`k=p_i b`, `u=k+p_i p_j`, `Q=M_i' M_i`, and retain the prescribed even map

```
Theta_t(Z)=S_t M_i'(z_t(M_i Z));z_t(Q Z),
Theta_t=(-1)^t z_t(M_i' S_t M_i Z);M_i'(z_t(M_i Z)).
```

For the pair `B_i B_i A_j -> A_j B_i B_i`, write
`R0=L_j(Theta_k(X))`, `R2=Theta_u(L_j X)`. Direct expansion of the two J's
cancels the intermediate inverse pair. Moving the remaining degree-k map
past z_u contributes `(-1)^(uk)`; replacing the bare double removal by
Theta contributes `(-1)^k`. Hence the pair is

```
K = (-1)^(uk+k) R0;jB;R2^-1
  = (-1)^(k p_i p_j) R0;jB;R2^-1.                     (7)
```

For the raw probe crossing `B:Q->Q`, of degree p_i, use exactly
`Bhat_t=Theta_t;B;Theta_t^-1`. Both boundary R maps are even. The two
paths, crossing before or after K, therefore reduce to the same scalar
in (7) times the associator-naturality identity
`L_j(B);jB=jB;B_(L_j X)`. This proves the paired equation for these
boundaries. Setting j=i recovers the sign in `PairedHomInterchange.md`;
setting p_j=0 makes the paired coefficient 1, even when p_i=k=1.

The identification of this equal-probe Theta with the prescribed beta/xi
transport is proved in `PairedHomInterchange.md`; it is not an additional
gauge choice or a further hypothesis.

These calculations are component arguments. They do not assume a braid
for J. In both (6) and (7) the factor crossing is fixed before the
comparison is computed.

## 4. Direct paths on A_i B_j A_i

Fix i != j. Write

```
W=A_i A_i B_j, V=A_i B_j A_i, Z=B_j A_i A_i,
J1:V->W, J2:Z->V, D=T_1|W, E=T_2|Z.
```

All J's are (2) at their own contents. Equation (6) says
`D J1 J2=J1 J2 E`. Coordinates on W are x,z,y in execution order: x,z
belong to the two reservoir strands and y to the probe. Naming x,y,z by
colour strand rather than sorted position avoids a commuting substitution.

Transport both full paths V->V by J1. Using (3), the chronological paths
are

```
121: V --J2^-1--> Z --E--> Z --Q J2--> V,
212: V --Q J1--> W --D--> W --J1^-1--> V.
```

Their exact transported functional products are

```
J1 path(121) J1^-1 = Q_ij(x,y) D,
J1 path(212) J1^-1 = D Q_ij(z,y).                       (8)
```

Q in the first line is evaluated at the *target* first i strand; Q in
the second is evaluated at the *source* second i strand. Swapping these
arguments would change the sign of the correction.

The fixed reservoir slides, including the spectator sign, give

```
D f=s(f) D+delta(f),
s(x)=q z, s(z)=q x, s(y)=(-1)^(ph) y,
delta(x)=-q, delta(z)=1, delta(y)=0,
delta(fg)=delta(f)g+s(f)delta(g).                       (9)
```

Separate support of Q implies `s(Q(z,y))=Q(x,y)`. For each allowed
monomial with r>0,

```
delta(z^r y^s)=sum_(b=0)^(r-1) q^b x^b y^s z^(r-1-b).
```

The y movement is unsigned because hs=0. Relabeling b and using pr=0,
(8) minus its second line is

```
-delta(Q(z,y))
 = -q sum_(r,s) c_(r,s) sum_(b=0)^(r-1)
                       q^b x^(r-1-b) y^s z^b.         (10)
```

Every monomial on the right has parity p. Transport by J1 of degree ph
changes it by `(-1)^(ph*p)=epsilon`, including the spectator transport.
Thus undoing J1 in (10) yields precisely `-q C_ij(x,y,z)` on V, not the
formula with the middle-colour sign omitted. No division by x-z occurs.

There are no other output sectors from this input: the equal-colour
crossing encountered in either path has both strands in A, and the
other crossings are the single-entry maps (3).

## 5. Direct paths on B_i A_j B_i

Use instead

```
W=A_j B_i B_i, V=B_i A_j B_i, Z=B_i B_i A_j,
J1:V->W, J2:Z->V, D=T_2|W, E=T_1|Z.
```

Equation (7) supplies `D J1 J2=J1 J2 E`, with the nontrivial paired sign
retained on both sides. On W the execution coordinates are y,x,z. The
two complete paths now have the forms

```
121: V --Q J1--> W --D--> W --J1^-1--> V,
212: V --J2^-1--> Z --E--> Z --Q J2--> V.
```

Using `Q_ji(y,x)=Q_ij(x,y)`, their transports are respectively

```
D Q_ij(x,y),             Q_ij(z,y) D.                  (11)
```

For the fixed probe crossing, (9) applies to its first and second probe
dots x,z, with y the spectator. The difference is `delta(Q(x,y))`.
Leibniz expansion before reordering gives

```
delta(x^r)=-q sum_(b=0)^(r-1) q^b z^b x^(r-1-b).
```

Reordering z past x has sign `q^(b(r-1-b))`. Its combined exponent
`b+b(r-1-b)=br-b^2` equals b modulo two whenever p=1 and r is allowed;
for p=0 there is no sign. Moving y into ordered position adds no sign
because hs=0. Hence this difference is again (10). Undoing the degree-ph
map J1 again contributes epsilon. The result on V is (1).

This accounts for the whole output column from B_i A_j B_i. It uses the
same prescribed even Theta transport as §3, not a redefinition of the
probe crossing to force a braid.

## 6. Exact coverage and outstanding comparisons

The two mixed iji input sectors proved above are ABA and BAB. AAA and BBB
are the given factor relations once their prescribed factor transports
are in place; they are not new consequences of RouquierFamily. The four
remaining mixed input sectors are AAB, ABB, BAA, BBA. They have different
sectors on the two outer i strands. In these cases the middle equal-colour
crossing uses the full corrected 2-by-2 block, so its diagonal and swapping
paths must both be retained. The outputs for AAB lie in {AAB,BAA}, those
for BAA in the same pair; those for ABB and BBA lie in {ABB,BBA}.
The diagonal braid difference must be (1) and every off-diagonal difference
must be zero. Those two 2-by-2 identities have not been expanded here.

For precision, if `T_a(w)` is the whole prescribed adjacent-crossing map
on colour word w, including its sector matrix, the unevaluated test is

```
T_1(s_2 s_1 w) T_2(s_1 w) T_1(w)
 - T_2(s_1 s_2 w) T_1(s_2 w) T_2(w)
 = diag_sector(-q C_ij)                         for w=iji. (12)
```

The tests for iij, ijj and pairwise-distinct ijk are the same typed path
difference with zero right side. Their mixed-sector entries are not
claimed proved by this note. In particular (6) handles a general
reservoir crossing but is not a substitute for all of (12).

The remaining different-probe-colour coherence has a concrete component
form. For probe colours r,s at reservoir parity b, the word-removal map is

```
Theta_(r,s;b)(X)=S_(p_s b) M_s(z_(p_r b)(M_r X));
                 z_(p_s b)(M_s M_r X).
```

Its degree is `b(p_r+p_s)` and need not be zero. One must compare the
*prescribed* BB crossing `B_r B_s -> B_s B_r`, of degree `p_r p_s`, with
`Theta_(r,s;b);B_raw;Theta_(s,r;b)^-1`, and evaluate the two paired-J paths
at b and b+p_a. Merely invoking the even Theta calculation for equal
probe colours does not establish this comparison. The AA comparison (6)
is available; this different-BB comparison and the rational mixed-block
entries remain explicit obligations, not new premises of a fusion theorem.

All equations in §§2–5 hold at arbitrary admissible starting content b.
A word prefix changes b to its own content; a suffix applies the same
superfunctor to both sides. Even associators rebracket the maps. Since the
equalities were derived on arbitrary homogeneous Hom morphisms, this
whiskering retains the signs and gives every external word context for
these two sectors. No faithful polynomial realization is used.

The mixed block in §2 requires only the mixed reservoir/probe denominators
already justified by finite geometric series. Neither the polynomial
calculations here nor the stated remaining tests license inversion of
same-reservoir differences, numerical specialization of dots, or a new
faithfulness hypothesis. Full multicolour relations, integer word shifts,
localization comparison, augmented inverses, fusion and separation remain
outside the result proved in this note.