# Tensor mates and principal feedback in separated fusion

**Status: written calculations, not Lean theorems.** The tensor calculation
below determines the sign in the principal feedback once the sector maps
have the prescribed tensor support. It also computes partial mates of the
square rational coefficient from cups and caps. It does **not** establish
the missing comparison from the content-shifted Hom construction to these
tensor coordinates, or a fused action. In particular this is not a closure
of A2-b. The distinction is material even with the accepted graded factor
action, signed F triangle and fixed-content reservoir bounds.

The inputs used are `DeformedGradedAction.md`, `SignedFTriangle.md` and
`DeformedReservoirBound.md`. The existing reduction under audit is
`NondegeneracyProof.md` §§3 and 5.1–5.4 and `FusionReservoirLemma.md`.
The historical `FusedCapWindows.md` at commit
`9029e6cefa101d5bc73dcf7f4a1c036c6981a273` is used only to locate the
transport problem. The historical `FusionResidualMatrix.md` at commit
`d6cb482` contains the positive-total elimination, not a proved coordinate
comparison. Neither historical note is an additional action hypothesis.

## 1. Conventions, shifts and the unfilled comparison

Composition of maps is right to left. Words in the mate calculation retain
the repository's execution order. Thus an even right adjunction has
`eta_a:1 -> E_a F_a`, `eps_a:F_a E_a -> 1`.
Write `p=p(i)`, `q=(-1)^p`. Tensor composition is

    (f tensor g)(f' tensor g') = (-1)^(|g||f'|) ff' tensor gg'.       (1)

Integer degree is not parity. A parity-p invertible probe dot is permitted;
no integer grading, finite dimension, or nilpotence is required of the probe.

For raw factor maps set

    X_a=F_a E_a,  Y_a=E_a F_a,
    sigma_a:X_a -> Y_a,  R_a:Y_a -> X_a,
    u_a(r):1 -> Y_a,     v_a(s):X_a -> 1.

Here R is the principal inverse component of the augmented matrix, never
an inverse of the bare sigma. The parities are

    |sigma_a|=|R_a|=p,   |u_a(r)|=rp,   |v_a(s)|=sp.                 (2)

Negative indices in this note occur only on probe dots and have their
integer parity modulo two. The factor right cups and caps are even.
To use the normalized mate `sigma'=-q sigma`, transport the **whole**
augmented matrix by scaling its Y target by `-q`: u also scales by `-q`,
R and the negative inverse cap b by `(-q)^(-1)`, while v and the positive
inverse cup a are unchanged. Below we instead keep the **literal** factor
matrices and right cups/caps throughout. The series C,D in (9) are blocks
of the normalized fused mate; the literal off-diagonal blocks are -q times
these series. Scaling only sigma would invalidate its inverse identities.

Here are the required shifted types, not choices of arbitrary gauges.
If the actual sector source has shift `(delta_a,epsilon_a)`, the even
matrix is on

    X_a[delta_a,epsilon_a],  Y_a[delta_a,epsilon_a+p],
    P_(a,s)=1[delta_a-d(1-h_a+2s), epsilon_a+sp],       0<=s<h_a,
    N_(a,r)=1[delta_a+d(1+h_a+2r), epsilon_a+(r+1)p],   0<=r<-h_a.  (3)

Our shift convention is `Hom^0(Z[l,e],W[m,f])=Hom^(l-m,e-f)(Z,W)`.
Equation (3) follows from the cup/cap degrees in `DeformedGradedAction.md`,
including the extra p on the Y target. It does not determine delta or
epsilon for a Hom realization.

For that realization the specified functors are more precise than a bare
`E_A directsum E_B`. On `Hom(T(-muP),W(muM))`, put

    kappa=p(i) contentParity(betaP),  S=Pi^kappa,
    L_B=homPost(E_B) followed by S,
    R_B=S followed by homPost(F_B),
    L_A=homPre(E_A),
    R_A=homPre(F_A) followed by Pi^sigma,
    sigma=p(i)(h_A+1) on the factor edge.                         (4)

The letter R in (4) denotes a functor, not the inverse component in (2).
The factor left adjunction needed by (4) is now supplied mathematically by
`SignedFTriangle.md`: normalize its cap by
`c(h)^(-1)`, where `c(h)=(-1)^(sigma sigma)e(h)`, with `e(h)=1` for h<0
and `e(h)=q` otherwise. Keep its cup unchanged. This is not a Lean
`LeftZigzags` construction. The B adjunction is the given even right
adjunction composed with `S adjoint S`, whose counit is `xi:S S -> Id`.
In particular its dotted counit is literally

    w_B,t(Y)=S.map(c_t(S(Y))) ; xi_Y,
    c_t(Z)=((Z F_B) whisker x_B^t) ; alpha ; (Z whisker eps_B) ; rho. (5)

Here only this display uses `;` for execution-order composition. Removing
one S with the parity-kappa comparison zeta costs `(-1)^(kappa tp)`
when moved past a t-fold dot. Removing both with the even xi does not.
Thus (5) is not the unshifted factor cap without a transport theorem.

**Missing comparison (TC).** Construct the coupled decompositions from
(4), and evaluate their cup–crossing–cap maps, with the normalized A left
adjunction above and B counit (5). Prove that their restrictions are the
supported tensors in (9) below and that their sector-swapping blocks are
the shifted transports of the partial mates in §3. Specify the zeta/xi
maps and the integer shifts if retaining a homogeneous precursor. This
includes the rational crossing normalization, not just an isomorphism of
underlying functors. `RouquierCoupled.lean` takes its swapping entries as
inputs and proves a slide, not their formula, square, braid or invertibility.
The accepted factor action does not supply (TC).

## 2. Sector support comes from bending, not invertibility

Let `t_cd^ab:E_c E_d -> E_a E_b` be an upward block, with all adjacent
weights understood. Its partial mate has the exact type and formula

    P(t_cd^ab):F_a E_c -> E_b F_d,
    P(t)=(eps_a E_b F_d)(F_a t F_d)(F_a E_c eta_d).                (6)

Associators and unitors in (6) are the canonical even ones. Insert the
sector inclusions/projections in the three factors of the full mate.
The diagonal unit and counit kill all terms except precisely (6). All
inclusions/projections are even; hence this restriction creates no sign.
This proves the following support table for any diagonal sector adjunction:

| upward block | mixed source | mixed target |
|---|---|---|
| AA -> AA | X_A | Y_A |
| BB -> BB | X_B | Y_B |
| AB -> AB | X_A | Y_B |
| BA -> BA | X_B | Y_A |
| BA -> AB | F_A E_B | E_B F_A |
| AB -> BA | F_B E_A | E_A F_B |

In particular the last two rows do not couple to X_A, X_B, Y_A or Y_B.
If those are all upward blocks, mixed cross summands are already block
diagonal; they do not create extra Schur corrections to the central block.
This is a support statement, not an assertion that the last two maps are
invertible. It remains valid with the sector functors (4), before removing
any shifts. It is obtained by projecting the actual definition of the mate.

## 3. A partial mate calculation that does prove invertibility

There is a useful unconditional local calculation in the *untwisted*
external tensor product of the two factor adjunctions. Let j interchange
the independent E_A and E_B functors. It is the canonical **even** tensor
interchange, with no content-dependent zeta identification. Its partial
mate is the canonical interchange of F_A and E_B (respectively F_B and
E_A). To see this, substitute j in (6), use external interchange to put
the A unit and A counit adjacent, and contract the A right snake. The B
factor is an identity. For the other direction contract the B snake.
Units and counits are even, so both calculations have coefficient one.
The inverse is the reverse interchange, whose composite contracts the
same snake. This proves invertibility by cups and caps, not by the false
principle that a partial mate preserves arbitrary isomorphisms.

Let X be a nilpotent reservoir dot and Y an invertible probe dot, both of
parity p. On the upward tensor block `XY=q YX`. For p=1 their squares
commute with both dots. If X^n=0, the even-colour formula is

    (X-Y)^(-1)=-sum_(0<=r<n) X^r Y^(-r-1).

For the odd colour, choose m with X^(2m)=0 and put Delta=X^2-Y^2. Then

    Delta^(-1)=-sum_(0<=r<m) X^(2r)Y^(-2r-2),
    a=(X-Y)Delta^(-1)
      =sum_(0<=r<m) [X^(2r)Y^(-2r-1)-X^(2r+1)Y^(-2r-2)],
    a^2=(X^2+Y^2)(X^2-Y^2)^(-2).                              (7)

The first equality telescopes after multiplication by Delta. The second
uses that Y commutes with X^(2r). The square uses XY+YX=0. In particular
X^2+Y^2 is also a unit, by its terminating geometric series. No inverse
of X is introduced.

Bending changes (7): it must not be copied unchanged to the mixed block.
Write Z=M_A(X) and W=M_B(Y) for right transposes. The even cups/caps give

    M_a(fg)=(-1)^(|f||g|)M_a(g)M_a(f),
    M_a(x^r)=q^(r(r-1)/2) M_a(x)^r.                            (8)

These follow by moving f past M(g) once in the expanded cap, then the
right snake; this is the transposition law of `SignedFTriangle.md`.
In particular an odd square bends to **minus** the square. On the
commuting even polynomial algebra generated by X^2,Y^2, partial bending
therefore substitutes X^2 -> -Z^2 when A is bent, or Y^2 -> -W^2 when B
is bent. It preserves products on that algebra. It also preserves the
inverse of an even unit: bend the two inverse identities; there is no
sign and the commuting images commute. This derives the finite rational
substitution, rather than postulating a rule for rational diagrams.

Consequently the partial mate of a^2 attached to canonical j is, after
the canonical mixed interchange,

    A bent:  (Y^2-Z^2)(Z^2+Y^2)^(-2),
    B bent:  (X^2-W^2)(X^2+W^2)^(-2)                         (p=1).

For p=0 these formulas are respectively `(Z-Y)^(-2)` and `(X-W)^(-2)`.
An initial minus sign on `-j^(-1)a^2` remains a minus sign. Each displayed
coefficient is invertible: Z is nilpotent by (8); W is invertible by
bending the two inverse identities (for p=1, `M(Y^(-1))=-W^(-1)`);
the remaining factors are invertible-probe powers times 1 plus or minus
a nilpotent commuting ratio. Thus this class of partial mates is invertible
by a direct calculation.

**Boundary:** raw j is even and cannot itself be the parity-p same-colour
crossing entry when p=1. The content shift in (4) supplies the missing
parity, but its zeta transport must be calculated. The calculation above
proves the raw tensor lemma, not that an unspecified odd J has the same
partial mate. The precise missing equality is (TC), including these square
sign changes. Upward invertibility alone supplies none of it.

## 4. Ordered mixed series and the supported feedback sign

This section gives a proved tensor calculation with an explicitly
unfilled application hypothesis (TC). Suppose the central blocks of the
normalized mixed mate, in the raw tensor coordinates of §1 with literal
factor right cups/caps, are

    C:X_B -> Y_A = sum_r q^r u_A(r) v_B(-r-1),
    D:X_A -> Y_B = -sum_s q^(s+1) u_B(-s-1) v_A(s).             (9)

Their tensor meaning is important: for example the rth term of C is
`(u_A(r) tensor 1)(1 tensor v_B(-r-1))`, while the sth term of D is
`(1 tensor u_B(-s-1))(v_A(s) tensor 1)`. These are ordered composites,
not unsigned tensor products in both orders.

The slide proves (9) *for the sector cups/caps*: if U is the relevant
nilpotent reservoir dot and V the invertible probe dot, solving
`CV-qUC=u_A v_B` by repeated substitution gives
`C=sum q^r U^r u_A v_B V^(-r-1)`. The remainder is killed by U^n=0.
The target-probe equation similarly gives D. Uniqueness follows by
iterating the homogeneous equation n times. Left and right composition
commute as operations on Hom even when U,V are odd; no unsigned
commutation of the underlying dot maps is used. Identifying these sector
cups/caps with the factor-supported tensors in (9) is exactly the part
not obtained merely by this Sylvester argument.

Put `K=-q [[0,C],[D,0]]`, the off-diagonal correction to the literal
factor sigma, and `R=diag(R_A,R_B)`. Principal elimination of `1+KR`
against its upper-left identity gives

    1-T on Y_B,     T=(-q D) R_A (-q C) R_B=D R_A C R_B.        (10)

Both diagonal identities in this step are identities, not factor crossings.
The tensor-supported coefficient of (10) is exactly

    T=-sum_(s,r) q^(rs) b_A(s,r) tensor H_B(s,r),
    b_A(s,r)=v_A(s) R_A u_A(r),
    H_B(s,r)=u_B(-s-1) v_B(-r-1) R_B.                          (11)

Here is every sign in (11). Before grouping, the coefficient is
`-q^(r+s+1)` and the word is

    u_B(-s-1) [v_A(s) R_A u_A(r)] v_B(-r-1) R_B.

Move only the initial B cup past the bracketed A closure. Their parities
are `(s+1)p` and `(r+s+1)p`. The new exponent is
`p[(r+s+1)+(s+1)(r+s+1)]`, equal modulo two to `prs`: first remove
`2p(r+s+1)` to obtain `p s(r+s+1)`, then remove `p s(s+1)`.
Both removed integers are even. No other factors are reordered.
The parity of H_B is `(r+s+1)p`, the same as b_A, so every tensor in (11)
is even. Neither b_A nor H_B is required to be even individually.

For a product of n terms of (11), the additional sign from (1) is

    (-1)^(sum_(j<k) |H_j| |b_k|),

and the reservoir factor is the ordered product `b_1 ... b_n`.
This is the exact place where the accepted joint nilpotence applies.
Each b_A is an endomorphism of `1_(betaA)`: its cup, principal inverse and
cap return to the same content. Intermediate functors can visit adjacent
contents, but a *whole closure* starts and ends at betaA. Equation (11)
acts on `1_(betaA) tensor Y_B`, so repeated feedback never changes betaA.
Every term is a positive reservoir closure of degree `2d(r+s+1)`.
By `DeformedReservoirBound.md`, choose n with `2dn>M_betaA`; then every
reservoir product and hence T^n is zero. This proves invertibility of
`1-T` and therefore of **only the principal block** `1+KR` under (TC).

No bound on the probe, nor a uniform bound on all contents of one weight,
is used. On an infinite content fiber invert componentwise. These are
parity-even natural inverses. A claim that they form a single homogeneous
integer-degree-zero transformation additionally requires the homogeneous
transport in (TC); it is not imposed on the ungraded specialized probe.

## 5. Augmented elimination with every identity summand

Work now in the even shifted category (3), after whatever transports have
actually been proved. Set

    P=Pos(h_A) disjoint_union Pos(h_B),
    N=Neg(h_A) disjoint_union Neg(h_B),
    X=X_A directsum X_B,  Y=Y_A directsum Y_B.

Use the same letters P,N for their sums of shifted identities. The two
factor augmented isomorphisms, at arbitrary individual heights, combine as

    Phi=[sigma u; v 0]:X+N -> Y+P,
    Phi^(-1)=[R a; b 0]:Y+P -> X+N.                           (12)

For example `sigma R+u b=1`, `R sigma+a v=1`, `v R=0`,
`sigma a=0`, `b sigma=0`, `v a=1`, `b u=1`. These follow by multiplying
(12), including its empty summands. No bare crossing has been inverted.

For total H=h_A+h_B>=0 let F be the fused cap window indexed by `Fin H`,
and let w:X->F be its **actual** cap row. The central fused map is
`[sigma+K;w]`. Adjoin an identity on N and shear its Y row by u. After
precomposition by (12), the resulting map from Y+P is

    [1+KR   Ka]
    [ wr    wa] : Y+P -> Y+F+N.
    [ b      0]

With A0=1+KR invertible, the exact residual is

    S_+=[wa-wr A0^(-1)Ka; -b A0^(-1)Ka]:P -> F+N.             (13)

Thus in source-row notation its rows are `Pos h_A disjoint_union Pos h_B`
and columns are `Fin H disjoint_union Neg h_A disjoint_union Neg h_B`.
The cardinalities agree because `h_a=h_a^+-h_a^-`. At total zero opposite
nonzero heights still leave a residual matrix. Equation (13) is not an
identity matrix, and its invertibility has not been proved here.

For H<=0 one need not guess a super-opposite sign. Let G have indices
`Fin(-H)` and let z:G->Y be the actual fused cup column. The central map
is `[sigma+K,z]:X+G->Y`. Stabilize by an identity on P, shear the P row
by v, and **postcompose** by Phi^(-1). Direct multiplication gives

    [1+RK   Rz   a] : X+G+P -> X+N.
    [ bK    bz   0]

Put B0=1+RK. It is invertible whenever A0 is, with
`B0^(-1)=1-R A0^(-1)K`; multiplication verifies both inverse identities.
Eliminating X gives the negative-total residual

    S_-=[bz-bK B0^(-1)Rz, -bK B0^(-1)a]:G+P -> N.             (14)

Its source-row indices are `Fin(-H) disjoint_union Pos h_A disjoint_union
Pos h_B`, and its target-column indices are `Neg h_A disjoint_union Neg h_B`.
All matrix products (12)–(14) are compositions of even maps on shifted
objects; there is no hidden super transpose or use of ordinary centrality.
This is the dual *elimination formula*, not a construction or comparison
of z by a reflected fusion action.

## 6. Relation to the even proof and remaining obligations

The formulas of `Categorification/TwoRep/RouqCoproduct.lean` were inspected:
`isIso_lift_of_schur` first multiplies by the labelwise augmented inverse,
then inverts its principal block using `gam`, and only afterwards appeals
to `schurPos`. Its defining expression is

    matB0 * (W * [1,0]) - matB0 * (T * (matE0 * [0,1])).

`schur_const_eq` identifies that matrix with `crtMatrix`, not an identity.
`RouqCoproductBubbles.lean` proves closure nilpotence by low-window
annihilation and the bubble-product expansion. The present calculation
instead uses the accepted fixed-content graded bound only after (11).
It does not import the even commutative identity-endomorphism ring into
the super case.

The smallest new tensor calculation above is the square-sign substitution
in §3, together with the explicit supported feedback sign `-q^(rs)` and
its fixed-content proof in §4. Their application boundary is not optional:

1. Prove (TC) for the content-shifted functors (4), including the mate of
   the prescribed odd swapping entry, not just raw j. In particular give
   the comparison of both sector adjunctions with the normalized factor
   maps used in (9). This is the first unfilled map-level assertion.
2. Prove the chosen rational crossing has all required fusion relations;
   factor action and a coupled slide alone are not a fused action.
3. Compute w and z and their inverse-window coordinates with all shifts.
   Then prove, if valid, `S mod J=L H Q` for the actual residual (13) or
   (14), an explicitly controlled ideal and specified coordinate changes.
   Nilpotence of T proves none of that residual comparison.
4. Keep truncation-compatible joint coefficient/PBW separation and the
   regular bubble-coordinate identification separate from inversion.

No new Lean declaration, full principal-feedback identification for the
Hom action, all-height fused inversion, or nondegeneracy theorem is claimed.
