# Central feedback in the content-shifted Hom construction

**Status: written component calculation and conditional nilpotence, not a Lean
theorem.** The historical diagonals
in §2 did not satisfy the fixed even-colour slides. Their literal mates
C,D are retained as historical variables. `CrossingNormalization.md`
repairs the diagonals by -q, so the literal new mates are
`Cnew=-q C`, `Dnew=-q D`; C,D are normalized new mates. Feedback is
unchanged, but §6 uses Knew in every residual. The factor maps and
swapping entries are unchanged.
This note computes the two central partial mates of the diagonal entries
of the specified upward matrix. It factors their feedback through the
normalized-left reservoir closures, rather than identifying left closures
with right ones. The nilpotence argument uses only the integer grading of
the reservoir. It does not construct a homogeneous graded fused action.

Inputs are the normalized adjunction formulas of `HomSectorTransport.md`,
the principal and whole-window comparison of `HomPrincipalMate.md`, and
the fixed-content coefficient quotient of `DeformedReservoirBound.md`.
The swapping-mate evaluations in `HomSwappingMates.md` are not inputs.
Their support separation is needed only to pass from the central block
to a statement about the full mixed map.

## 1. Four common coordinates

Use execution order `f;g`; products in displayed matrices below instead
use the usual target-row/source-column convention. Fix reservoir content
beta, weight lambda, height k, and colour i. Put

```
p=p(i), q=(-1)^p, d=d_i, sigma=p(k+1),
kappa=p contentParity(beta),
X=F_- E_-, Y=E_+ F_+,
U_r:1_lambda -> X, V_s:Y -> 1_lambda, f:X -> Y,
c=c(k)=(-1)^sigma e(k), e(k)=1 (k<0), e(k)=q (k>=0),
alpha_r=(-1)^(sigma r p),
beta_s=(-1)^(sigma(1+s p)) c^-1,
gamma=gamma(k)=q^k (k!=0), gamma(0)=q.
```

The reservoir Hom height is **-k**. U uses the edge of bottom height
k-2, while V and its normalization c use the edge of bottom height k.
Both edge parities are sigma. This does not replace c(k) by c(k-2).
Let P_Z(H)=Z H, and let M,N be probe postcomposition by E_B,F_B.
The four mixed objects, with their specified coordinate maps, are

```
A_source=L_+ S_sigma K_+ H,
 A_s=L_+(z_sigma(K_+H)):A_source -> P_Y(H),
A_target=S_sigma K_- L_- H,
 A_t=z_sigma(P_X(H)):A_target -> P_X(H),
B_source=S_kappa M N S_kappa H,
 B_s=(-1)^kappa z_kappa(M N S_kappa H);M N(z_kappa H)
       :B_source -> M N H,
B_target=N S_kappa S_kappa M H,
 B_t=N(xi_kappa(MH)):B_target -> N M H.                 (1)
```

A_s,A_t have parity sigma; B_s,B_t are even. Their integer degrees are
zero wherever a graded precursor exists. No object H has an assigned
parity. In particular B_s is the **xi-normalized** comparison, not the
bare pair of z's. The rules are

```
S_t(g);z_t=(-1)^(t|g|) z_t;g,
xi_t=(-1)^t z_t(S_t -);z_t.
```

Write u_B(n):Id->NM and v_B(n):MN->Id for the raw dotted probe cup
and cap. Negative n means powers of the invertible probe dot, not powers
of a transposed dot. The four transport formulas are exactly

```
cup_A(r);A_t = alpha_r P_(U_r),
cap_A(s) = beta_s A_s;P_(V_s),
cup_B(n);B_t = u_B(n),
cap_B(n) = B_s;v_B(n).                                (2)
```

These formulas use the actual even sector units and counits. In particular
the reservoir cap includes both c^-1 and the extra output-shift sign
(-1)^sigma. The probe's two shifts cancel by xi, including its sign.
They hold for all displayed dot indices, not just the finite windows.

## 2. Derive the central series from the upward entries

This paragraph fixes the normalization independently of the slide prose.
As in `HomSectorTransport.md` and `HomSwappingMates.md`, AB means first
A then B (functional order B'L), BA means first B then A (functional
order LB). J:BA->AB is the specified map

```
J=L(z_kappa M);j;z_(kappa+p)(ML)^-1.
```

Let x be the reservoir dot and y the probe dot on AB. They satisfy
xy=q yx. Each dot acquires q under conjugation by J; squares do not.
The historical diagonal entries were a on AB and -J^-1 a J on BA,
where products in this sentence are in ordinary right-to-left order.
For x nilpotent and y invertible their finite expansions are

```
a=-q sum_(r>=0) q^r x^r y^(-r-1),
-J^-1 a J=sum_(r>=0) q^r x_BA^r y_BA^(-r-1).          (3)
```

For p=0 this is the geometric inverse of x-y. For p=1 it is the
expansion of (x-y)(x^2-y^2)^-1 into its even and odd x powers.
Every monomial has total exponent -1, hence conjugation contributes q;
the initial minus then gives the second formula. The sums terminate at
a bound for x on the finitely many reservoir edges concerned. There is
no series in a nilpotent probe dot, and no global bound over a weight fiber.

For an upward execution word E_a E_b, the partial mate of its identity
is cap_a;cup_b. Placing a power of the first-strand dot before that
identity puts it before cap_a; placing a power of the second-strand dot
after it puts it after cup_b. This is exactly
`homMateEquiv_left`, `homMateEquiv_right`, and `rouquierMate_id` in
`OddMath/SKM/RouquierMate.lean`. Linearity then applies to (3).
The potential reordering sign between x^r and y^(-r-1) is
q^(-r(r+1))=1. No strand dot is replaced by its right transpose, so no
factor q^(r(r-1)/2) is introduced.

Denote the **historical literal partial mates of (3)** by C and D. Their types
and finite ordered series are

```
C:B_source -> A_target
  = sum_r q^r [cap_B(-r-1);cup_A(r)],
D:A_source -> B_target
  = -sum_s q^(s+1) [cap_A(s);cup_B(-s-1)].             (4)
```

In the common coordinates (1), this gives

```
C_raw=B_s^-1;C;A_t
     =sum_r q^r alpha_r [v_B(-r-1);P_(U_r)],
D_raw=A_s^-1;D;B_t
     =-sum_s q^(s+1) beta_s [P_(V_s);u_B(-s-1)].      (5)
```

Every term of (5) has parity sigma+p. Intermediate maps in these
composites are evaluated at the object produced by the preceding map;
only even associators are suppressed. In particular the B cup in the
second line is evaluated after the A cap has returned to content beta.

**Normalization correction.** Equations (3)–(5) preserve the historical
calculation, not a claim that its upward entries satisfy the library slides.
Already p=0 gives `P(a)=-sum_s cap_A(s);cup_B(-s-1)` and the old upward
slide has right side -1. `CrossingNormalization.md` supplies the proposed
repair `a -> -q a`, `-J^-1 a J -> q J^-1 a J`, with J and
`-J^-1 a^2` fixed. By linearity the literal corrected mates are
`Cnew=-q C`, `Dnew=-q D`. Thus C,D in (4) are precisely the normalized
corrected mates, agreeing with the convention of `FusedFeedbackComparison.md`
(9). The coordinates of Cnew,Dnew are -q times (5); no shift-removal
map, cup or cap changes. The two-step feedback is unchanged; the residual
must instead use Knew as in §6. This is a proposed local normalization
repair, not a full braid or fusion comparison.

## 3. Use the whole reservoir inverse, not just its principal entry

The actual reservoir diagonal mate has coordinate gamma P_R, R=-sigL.
With the ordered triangular window changes T_+,T_- of
`ReversedReservoirMatrix.md`, let

```
Psi_+=[R,U], Psi_+^-1=[f;vtilde]                 (k>0),
Psi_-=[R;V], Psi_-^-1=[f,utilde]                 (k<0).
```

The actual matrices and inverses in these coordinates are

```
M_+=Psi_+ diag(gamma,diag(alpha_r)),
M_+^-1=diag(gamma^-1,diag(alpha_r^-1)) Psi_+^-1,
M_-=diag(gamma,diag(beta_s)) Psi_-,
M_-^-1=Psi_-^-1 diag(gamma^-1,diag(beta_s^-1)),
M_0=gamma R, M_0^-1=gamma f.                           (6)
```

Here r<k and s<-k in the corresponding finite windows. Thus the
principal inverse A_target->A_source, denoted I_A, satisfies

```
A_t^-1;I_A;A_s=gamma P_f.                              (7)
```

Every other component is also rescaled by its matching reciprocal in
(6). The identity summands are, in raw shifted coordinates,

```
Y[0,sigma] -> X[0,sigma+p],
k>0: Anew_r=1[d(1-k+2r),(r+1)p],
k<0: Bnew_s=1[-d(1+k+2s),sp].                         (8)
```

Their parity lifts use z, not underlying-module identities. The T_+
and T_- changes are ordered antitriangular changes of the inverse
original windows. No commutativity or inverse of the bare crossing is
used. At zero both windows are empty and gamma(0)=q is retained.

For the probe let I_B:B_target->B_source be the principal component
of its **specified augmented inverse**, and keep the exact coordinate

```
Rcal_B=B_t^-1;I_B;B_s : NM -> MN.                      (9)
```

No identification of (9) with an unshifted right-factor R_B is needed
below. This avoids concealing a second normalization choice in the
symbol R_B. The input needed here is the probe sector's augmented
isomorphism, obtained from its factor action with its specified parity
transport; no invertibility of its bare crossing is asserted. If only
an untransported probe factor matrix has been supplied, identifying
that matrix with the sector matrix is still an input, not a conclusion
of this note. Formula (9) makes that boundary explicit. A single
checkable sufficient comparison, with all dotted windows already fixed
by (2), is

```
B_s^-1;P(T_BB);B_t = post(sigma_B).                    (B)
```

Here sigma_B is the literal probe mixed mate, and T_BB is its prescribed
same-sector upward crossing transported to S_kappa M S_kappa M. For
example the canonical even word-removal map is
`Theta=S_kappa M(z_kappa(M-));z_kappa(M M -)`; transporting the factor
crossing means `T_BB=Theta;post(t_B);Theta^-1`.
Equation (B), if verified for that prescribed convention, transports the
whole probe augmented matrix and makes (9) exactly post(R_B).
This note **does not prove (B)** or replace it by uniqueness of adjoints.
Its feedback nilpotence conclusion needs the actual probe augmented
inverse, but not equality (B) or any chosen raw formula for that inverse.
Thus where that inverse is not already available, (B) is the precise
remaining sector-comparison obligation, not a restatement of (TC).

`HomProbeMatrix.md` proves (B) by the explicit four-strand comparison and
transports every inverse identity component. For that prescribed factor
action, the needed augmented inverse is therefore supplied and
`Rcal_B=post(R_B)`. The factor local inverse data remain hypotheses.

The maps B_s and B_t identify the probe source and target functors with
MN and NM on all homogeneous morphisms, since they are even natural
isomorphisms. Consequently Rcal_B is supernatural of parity p. This
is the only property of (9), besides its type and inverse-matrix origin,
used in the closure argument. In particular the argument does not need
a guessed sign for its comparison with a raw probe inverse.

## 4. Exact closure factorization and its sign

The principal feedback on B_target is the ordered composite

```
T=I_B;Cnew;I_A;Dnew=I_B;C;I_A;D.
```

Substitute (5), (7), and (9) and conjugate by B_t. Its (s,r) term is

```
-q^(r+s+1) alpha_r beta_s gamma
 [Rcal_B;v_B(-r-1);P_(U_r);P_f;P_(V_s);u_B(-s-1)].   (10)
```

In particular the reservoir segment is precisely

```
b_(s,r)=U_r;f;V_s : 1_lambda -> 1_lambda,
|b_(s,r)|=p(r+s+1), deg b_(s,r)=2d(r+s+1)>0.           (11)
```

The two sigma contributions cancel in its parity and its opposite
height contributions cancel in its integer degree. These are the
intrinsic **left** closures; they have not been identified with
v_A(s) R_A u_A(r) for the unreversed right adjunction.

Put H_(s,r)=Rcal_B;v_B(-r-1);u_B(-s-1):NM->NM. Move only the
final probe cup across the reservoir segment in (10). Its parity is
(s+1)p, so the exchange costs (-1)^(p(s+1)(r+s+1)). The resulting
coefficient and ordered common-coordinate formula are

```
B_t^-1;T;B_t
 = -sum_(s,r) q^(rs) alpha_r beta_s gamma
       [H_(s,r);P_(b_(s,r))]
 = -gamma c^-1 sum_(s,r)
       (-1)^(p r s+sigma(1+p(r+s)))
       [H_(s,r);P_(b_(s,r))].                         (12)
```

P_b in this display acts at the output NMH. This is the explicit
Hom-action version of a reservoir/probe supported expression, rather
than an identification of the Hom category with an external tensor
product. If (9) is separately identified with a raw probe inverse,
(12) becomes the corresponding tensor formula with that same inverse.
No such additional identification is required to multiply (12).

Indeed for any homogeneous reservoir identity endomorphism b of parity
e, b_H=P_b(H) is a supernatural endomorphism of the identity on the Hom
category. Postcomposition by M,N preserves it: MN(b_H)=b_(MNH),
NM(b_H)=b_(NMH), with even reassociations. Supernaturality of Rcal_B
therefore gives the interchange with sign (-1)^(pe). The same argument
for the dotted probe cup and cap gives their usual parity signs.
It follows that H_(s,r) interchanges with P_b with sign
(-1)^(p(r+s+1)e). This establishes the support property needed for
products, even without evaluating (9) as a raw tensor-factor map.
The individual b and H need not be even; their composite in (12) is even.

For completeness the exponent reduction is

```
p(r+s+1)+p(s+1)(r+s+1) = p r s  (mod 2),
alpha_r beta_s=(-1)^(sigma(1+p(r+s))) c^-1.
```

This leaves the cap normalization, both window dot signs, and the
exceptional principal scalar visible. They are not absorbed into a
renaming of right reservoir cups/caps.

## 5. Fixed-content nilpotence needs only the reservoir grading

Work over the homogeneous finite coefficient quotient of
`DeformedReservoirBound.md`, with its factor-action hypotheses. At
this fixed content beta its reservoir algebra has upper integer support
M_beta. The intrinsic closure (11) is a homogeneous natural identity
endomorphism of the graded reservoir category, hence a supercentral
element of that algebra. Products of n such closures have degree at
least 2dn. Choose n>0 with 2dn>M_beta. Every ordered product of n of
the closures (11) vanishes, including its action on arbitrary modules.

Expand the nth power of (12). The sums are finite because of reservoir
dot nilpotence on the specified adjacent edges. Use the interchange
proved after (12) to move all reservoir closures together. Each summand
is a sign and scalar times a probe-coordinate composite and a product
of n closures **at the same content beta**. It vanishes by the preceding
bound. Thus T^n=0 and (1-T)^-1=sum_(j<n) T^j componentwise.

This proof does not assume finite-dimensional Hom spaces. It imposes
no integer grading or nilpotence on the localized probe, and no bound
uniform on the possibly infinite fiber of one weight. Parity-even
componentwise inverses assemble wherever the content-preserving family
is defined; a single globally terminating geometric series is not claimed.

In particular the unresolved coherent integer word shift
`delta_AB-delta_BA=-2d` is **not necessary for this nilpotence proof**.
The present swapping coefficients still have degrees 0 and -4d rather
than a common -2d. The proof uses the integer degree of b inside the
reservoir factor, not the degree of T or of the whole fused crossing.
It proves no homogeneous graded fused action and supplies no integer
regrading by a silent gauge.

## 6. The remaining residual, with the corrected literal entries

In the parity-completed category let the two specified augmented sector
matrices combine as

```
Phi=[sigma0 u;v 0]:X0+N0 -> Y0+P0,
Phi^-1=[I a0;b0 0]:Y0+P0 -> X0+N0,
X0=A_source+B_source, Y0=A_target+B_target,
I=diag(I_A,I_B), Knew=[0 Cnew;Dnew 0]=-q [0 C;D 0].
```

P0 has indices Pos(-k) disjoint_union Pos(h_B); N0 has indices
Neg(-k) disjoint_union Neg(h_B). All component scalings in (6) are
included in these matrices. The usual extra parity shifts make all
matrix entries even. This packaging does not claim a coherent integer
shift for the full fused action.

Eliminating the first diagonal identity of Anew=1+Knew I leaves 1-T.
Hence the preceding result makes Anew invertible, under the specified
sector augmented-isomorphism input. For total H=-k+h_B>=0, let w be
the actual fused cap row to F indexed by Fin H. The residual is

```
Snew_+=[w a0-w I Anew^-1 Knew a0; -b0 Anew^-1 Knew a0]
       :P0 -> F+N0.                                 (13)
```

For H<=0, let z:G->Y0 be the actual fused cup column with G indexed
by Fin(-H), and Bnew=1+I Knew. Then Bnew^-1=1-I Anew^-1 Knew, and

```
Snew_-=[b0 z-b0 Knew Bnew^-1 I z, -b0 Knew Bnew^-1 a0]
       :G+P0 -> N0.                                 (14)
```

These are typed residual formulas, not inverses to residual matrices.
Their w,z and their comparison with an invertible coefficient matrix
remain uncomputed here. The normalization correction after (5) matters
in (13)-(14): it cannot be discarded merely because the feedback is
unchanged. `CrossingNormalization.md` supplies the two-strand correction;
`HomProbeMatrix.md` supplies the probe comparison. Computing the residual
windows and proving their inversion remain separate obligations.
No full (TC), fusion relations, separation, or nondegeneracy theorem is
claimed. The new comparison is specifically (5), (7), (10)-(12), with
its fixed-content nilpotence argument and the stated probe-sector input.
