# Swapped Hom assembly and finite-colour passage

**Status: proposed conditional written theorem, not a Lean theorem.** Given
precisely the factor models listed in §1, the prescribed swapped Hom maps
satisfy the entire finite-colour parity-supercategory presentation. Section 5
assembles the four distinct-colour mate inverses, including their normalized
left and mixed-sector signs. Section 6 derives the vacuum coordinates and
all-height bubble formulas, with recovery on admissible bounded windows.
Neither existence of the factor models nor nondegeneracy is concluded here.
The arbitrary-colour conclusion in §8 remains conditional on finite-colour
detecting models; it does not construct an infinite-colour Hom action.

The presentation being tested is Brundan–Ellis, *Super Kac–Moody
2-categories*, arXiv:1701.04133v2, Definition 1.5, (1.7)–(1.14), with the
parameters of (1.2)–(1.4). Its exact library version is
`OddMath/SKM/Presentation.lean`, `Rel` and `relation`. The source allows
infinite colour sets and a supercommutative ground ring. Here the factor
inputs require symmetrizability, homogeneous parameters, and a purely even
field k with 2 invertible. These are restrictions of this construction,
not extra conditions in the cited definition. Both even and odd colours,
and connected mixed data, are retained.

## 1. Fixed factors and literal weight categories

**Factor hypotheses (the complete input list).** Work over a purely even
field k with 2 invertible. The finite restricted Cartan superdatum has
positive integral symmetrizers and the original admissible homogeneous Sc:
leading coefficients are units, the disconnected polynomial is one constant,
and a supported Q_ij monomial u^m v^n has p_i m=p_j n=0 in Z/2.
The following are hypotheses on factors, not on fused maps.

* **F1 — Full factor models.** Supply the content-indexed all-supermodule
  actions of the specified full-ELV cyclotomic kernels, with algebra
  parameters `parameterTwist Sc` and action parameters Sc. They satisfy
  every factor relation of `Presentation.Rel`, including distinct-colour
  inverses and both whole same-colour augmented inverses at every height.
  E is induction, F restriction, their right unit inserts the corner
  identity and their counit multiplies. Dots are signed right multipliers;
  crossings are R_tau for unequal colours and -R_tau for equal colours.
  Coefficient specialization and quotient identify these kernel maps,
  their compositions and their whole inverses by balanced tensor maps.
  These are the models of `DeformedActionAssembly.md`,
  `DeformedMixedBraid.md` and `DeformedGradedAction.md`, not an abstract
  rank-one `RouquierFamily` or a chosen splitting of the fused mate.
* **F2 — Probe and left adjunction.** T is the specialization of
  `InvertibleDotProbe.md`: at odd i its algebra polynomial is
  (u^2-1)^(M_i), with P_i=2M_i>0, and at even i it is (u-1)^(P_i),
  P_i>0. All adjacent signed probe dots are units. Use the inverse-defined
  left cups/caps of its full factor action and their derived normalized
  left adjunction, with c(h) and the two edge heights as below;
  `SignedFTriangle.md` and `HomSectorTransport.md` derive its triangles.
  No independent choice of left adjunction or left/right cyclicity gauge
  is allowed. T_0=k. No integer grading on T is required.
* **F3 — Fixed reservoir and closures.** W is the full-ELV reservoir over
  Abar=A/(c_a^(L_a)), with one fixed homogeneous coefficient quotient for
  the entire content tower. A is the super tensor product of its colour
  coefficient rings; distinct exterior delta_i remain independent and
  delta_i chi_(i,N_i/2)=0 is retained at positive even odd-colour cutoff
  (N_i=0 has no delta_i). The positive-degree even coefficients c_a have
  fixed L_a>=1. Each content algebra is finite-dimensional with finite
  integer support; dots have degree 2d_i>0. The reservoir unit, cap,
  principal inverse and windows have the degrees (G6)–(G8) of
  `DeformedGradedAction.md`. Homogeneous identity transformations are
  supercentral multipliers, and their positive-degree ideal is jointly
  nilpotent at each fixed content, including finite parity-shifted
  identity matrices. These are the factor estimates proved in
  `DeformedReservoirBound.md`; arbitrary open reservoir words are not
  declared coefficients. The action target is all parity-supermodules,
  not just finite modules. The graded kernels and closures supply these
  bounds after forgetting integer grading.
* **F4 — Weight and support data.** Retain formal nonnegative contents,
  zero categories at absent contents, the whole original weight group X,
  and the pairing-extension cutoff choice described below. All factor
  edges, append maps, units and caps carry their own content and weight
  labels. The target has parity completion and finite biproducts; use
  the super-enriched products of (A1), in a sufficiently large universe.

In particular no fused braid, fused partial-mate inverse, fused augmented
inverse, vacuum identification, or bubble value is an input predicate.
The written factor references explain the intended supply of F1–F4;
this theorem does not assert their existence or their Lean implementation.

Fix a finite colour set J with the restricted Cartan matrix, parity,
symmetrizers and parameters. Do not replace the original weight group X by
a quotient or by its coroot coordinates. For the factor construction use
the pairing extension and the cutoff choice of `SwappedHomInversion.md`:
apply `ProbeReachability.md` to -μ, obtaining

    ΛP - ΛR = (μ,0).

Let T be the specialized unit-dot probe of `InvertibleDotProbe.md`, and W
the reservoir of `DeformedReservoirBound.md`. Fix its coefficient truncation
once for the entire tower, not separately at each content. The untruncated
factor input is `DeformedActionAssembly.md`, `DeformedMixedBraid.md` and
`DeformedGradedAction.md`. Its algebra parameters are `parameterTwist Sc`;
its action parameters are the original Sc. Denote the probe and reservoir
module categories at formal contents b,c by T_b,W_c, and their weights by
-ΛP+α(b), -ΛR+α(c).

Use the two-supercategory of k-linear supercategories, superfunctors and
supernatural transformations, with parity completion. One can choose a
larger universe for these Hom categories. Put

    H_(b,c) = SFun_k(T_b,W_c),
    wt(b,c) = ΛP-ΛR-α(b)+α(c),
    C_λ = product_(b,c nonnegative, wt(b,c)=λ) H_(b,c).       (A1)

Objects are arbitrary families, not finite-support families. A homogeneous
map of parity r is a family all of whose entries have parity r; arbitrary
maps are the sum of their two parity parts. This is the super-enriched
product, with finite biproducts taken componentwise. Empty fibres have the
zero category. Absent contents also mean zero categories and zero functors.
Formal content, not its image under α, controls every predecessor operation.
Thus (A1) is meaningful even if positive contents have root image zero.

The interpretation on X uses C_(λ,0). More generally all objects of the
pairing extension are included, and the original presentation maps into
this one by λ↦(λ,0), with α_i↦(α_i,0). Heights at these images remain the
original heights. There is no claim that every such category is nonzero.

At an input component (b,c), the raising summands are

    A_i = pre(E_i^T): H_(b,c) -> H_(b-i,c),
    B_i = S_(p_i P(b)) post(E_i^W): H_(b,c) -> H_(b,c+i),    (A2)

where P(b)=Σ_j p_j b_j in Z/2. These are precisely
`homContentPreE` and `homContentPostE`, with T on the precomposition side.
For example the pre edge in (A2) is T_(b-i)→T_b, not T_b→T_(b+i).
Both changes raise wt by α_i.

Their right adjoints, on the reverse edges, are

    R_A = S_σ pre(F_i^T),    σ=p_i(h_i(-ΛP+α(b-i))+1),
    R_B = post(F_i^W) S_(p_i P(b)).                         (A3)

The first uses the normalized *left* adjunction of T and the second the
right adjunction of W. Use `HomSectorTransport.md` (4), (6), not a common
unsigned tensor adjunction. In particular, writing z_t:S_t→Id,

    S_t(f);z_t = (-1)^(t|f|) z_t;f,
    ξ_t = (-1)^t z_t(S_t(-));z_t,
    β_(L,t) = z_t(L(-));L(z_t^-1).                          (A4)

A semicolon means chronological composition. In the pre component, if
u,v are the raw left unit and normalized left counit, the even unit and
counit are u;z_σ^-1 and (-1)^σ L(z_σ);v. The normalization is
c(k)=(-1)^(p_i(k+1))e(k), with e(k)=1 for k<0 and e(k)=(-1)^p_i
for k≥0, at the bottom weight of the appropriate edge. In the post
component they are u;N(ξ_κ^-1) and S_κ(v(S_κ(-)));ξ_κ.
All edge labels, rather than only the central weight, enter these formulas.

Define E_i on (A1) by summing the two incoming components at each output,
and F_i by the two reverse edges (A3). Each output receives at most two
summands. Consequently both functors exist on the product, without an
infinite coproduct in an individual H_(b,c). The unit has the diagonal
sector units and zero off-sector entries; the counit has the diagonal
sector counits and zero off-sector entries. On each E or F summand the
triangle reduces to its sector triangle. Orthogonal biproduct projections
kill the other terms. This proves the global even right adjunction.
It is not necessary to bound the size of a weight fibre.

## 2. Prescribed upward maps and local finiteness

Dots are the inherited pre dot and the shifted post dot, with the action
of S on homogeneous maps retained. Precomposition reverses the two factor
slots. Its equal-colour crossing is -(-1)^p times the inherited factor
crossing. Distinct-colour pre crossings are the inherited reversed-label
crossings, not their inverses. The post same-sector crossings are the
specified β/ξ word transports of the factor crossings. At unequal colours
r,s the even comparison is

    S_(p_s P(b))(β_(M_s,p_r P(b))^-1);c_(p_s P(b),p_r P(b)),

where c_(1,1)=ξ. Removing it by a bare double z changes its sign and is not
an alternative definition.

For the mixed sector, let J_ij:B_j A_i→A_i B_j be

    L_i(z_t(M_j(-)));j_ij;z_(t+p_i p_j)(M_j L_i(-))^-1,
    t=p_j P(b),                                           (A5)

where j is the inverse associator. Its degree is p_i p_j. For i≠j the
unit direction A_i B_j→B_j A_i is J_ij^-1; the reverse is Q_ij J_ij,
with Q evaluated in the target dot coordinates. For equal colour, in
row/column order AB,BA the crossing is exactly

    [ -q a             J           ]
    [ -J^-1 a²         q J^-1 a J   ],   q=(-1)^p,          (A6)
    a=(x-y)^-1                       (p=0),
    a=(x-y)(x²-y²)^-1                (p=1),

where x is the pre probe dot and y the post reservoir dot. In particular
neither swapping entry is changed when the nilpotent side is exchanged.

At each fixed reservoir content the relevant dot is nilpotent, uniformly
on all reservoir modules, because its multiplier belongs to a finite
integer-graded algebra and has positive degree. This uses the fixed tower
truncation. Thus the denominators in (A6) have finite geometric inverses
in powers of y, since x is a unit. The odd squares commute. The same proof
applies to Q(x,y): its y-free term is a unit times a permitted power of x,
and the rest is a nilpotent commuting perturbation. No Q of two reservoir
dots or crossing of two equal-colour factor strands is inverted.

These are identities of natural transformations, not merely pointwise
inverses depending on a test module. They therefore assemble over (A1).
The length of a terminating series may vary with c. Parity is fixed, so
this variation does not violate the homogeneous-product convention.
A finite word of length n has at most 2^n sector paths; every output has
only finitely many predecessors. Each rational entry and each same-colour
inverse has finite sector support. Composing two such matrices still has
finite sums in every entry. These observations prove the local-finiteness
needed for all the proposed generator maps, including the inverse of
`SwappedHomInversion.md`; they assert no uniform nilpotence over all contents.

## 3. Exact relation dictionary

The following is a dictionary to `Presentation.relation`, not merely to
`RouquierFamily`. In particular the latter does not contain the mixed
KLR or distinct-colour inverse relations.

| Source relation | Assigned map and written proof |
|---|---|
| (1.7), `quadEq` | Same-sector factor square; mixed square of (A6), the four cancellations of `CrossingNormalization.md` (4). |
| (1.7), `quadZero`, `quadNe` | Same-sector factor square after slot reversal/βξ transport; mixed products of J^-1 and QJ. Separate exponent support makes Q transport unsigned. For disconnected colours Q is the single constant t_ij. |
| (1.8), `slideLEq`, `slideREq` | Pre crossing coefficient -q gives the two constants +1; post transport preserves the factor slides; the four mixed entries are the slides of `CrossingNormalization.md` (2)–(3). |
| (1.8), `slideL`, `slideR` | Reversed factor slides, transported post slides, and the two signed dot intertwinings of (A5). |
| (1.9), `braid`, iii | `ThreeStrandSectorBraid.md` with `PairedHomInterchange.md`; same-sector factor braid. |
| (1.9), `braid`, iij/ijj/distinct ijk | All sector path sums of `MixedColourRemainingBraid.md` (9)–(16), including the symmetric-Q divided-difference cancellation. |
| (1.9), `braidEq` | `MixedColourSectorBraid.md` and `MixedColourBlockCompletion.md`, with `ExecutionBraidNormalization.md` (2); all-one-sector transport as below. |
| (1.10), `zigE`, `zigF` | The diagonal finite-sum adjunction in §1. |
| (1.11), `sigmaL` | The *defined* unit–crossing–counit word, not an independently selected splitting map; project it by (A8) below. |
| (1.12), `invNe₁`, `invNe₂` | The four block-permutation entries and their two-sided inverses in §5. Upward Q invertibility alone is not this relation. |
| (1.13), `invP₁`–`invP₅` | Entire positive augmented map and inverse of `SwappedHomInversion.md` (13), (16), (17), extracting components as in §4. |
| (1.14), `invM₁`–`invM₅` | Entire negative augmented map and inverse there, (14), (16), (17). |
| `dcupZero`, `dcapZero` | Assign zero outside their indicated finite height windows. |

For completeness the all-pre transport does not require a new parameter
twist. Reversing two slots exchanges their dots; in a Q monomial each
exponent times its own colour parity is zero, so reordering the supported
powers has no sign. The distinct crossing squares remain Q. Reversing
three slots exchanges the two braid paths. In a corrected iji path there
is one equal-colour crossing, contributing -q_i. Reversing the ordered
correction contributes q_i, as the relabeling l↦r-1-l in
`ExecutionBraidNormalization.md` shows. Their product is -1, exactly the
path exchange. In zero-correction braids both paths have the same scalar.
For postcomposition the coherent even word comparisons simply transport
the factor relation. Their explicit two-strand representatives are the
β/ξ comparisons above; the paired-J calculations check the mixed paths.
These arguments keep the original Sc, including both leading coefficients.

For the corrected displayed relation, the coefficient of the ordered
term with l dots on the right i, s on j, r-1-l on the left i is
(-1)^(p_i(p_j+l)) Q_ij[r,s]. This is the chronological layer order of
`relation (.braidEq i j λ hij)`. The execution difference is its reversed
negative, not the displayed positive expression on renamed variables.
All distant commutations are super interchange in the target; each local
entry is supernatural of its declared parity. External prefixes change
b,c, and external suffixes apply the same superfunctors. No parity is
assigned to an object of H_(b,c).

## 4. Same-colour inverse generators, including height zero

Let H=h_i(λ), S=E_iF_i, T=F_iE_i, s:S→T the literal mate, v_n:S→1 the
literal dotted caps and u_n:1→T the literal dotted cups. Use the homogeneous
parity lifts of `SwappedHomInversion.md`, with all of its α_n, β_n, γ(k)
and identity windows. Its whole inverse is the written consequence of F1–F4 proved in
`SwappedHomInversion.md`, not an additional theorem hypothesis and not a
consequence of the kernel-checked principal words alone.

At H≥0 let [r,a] be the inverse of [s;v]:S→T⊕1^H. At H≤0 let [r;b]
be the inverse of [s,u]:S⊕1^(-H)→T. Undo the prescribed parity lifts and
set

    lcross(i,i)=-r,       dcup(i,n)=a_n (0≤n<H),
    dcap(i,n)=b_n (0≤n<-H).                               (A7)

For H≥0 the two inverse products read r s+Σ a_n v_n=1_S,
s r=1_T, v_m r=0, s a_n=0, v_m a_n=δ_mn in functional order.
Substitution of -r gives respectively `invP₁` through `invP₅`, with the
signs in the library. For H≤0 they read s r+Σ u_n b_n=1_T,
r s=1_S, r u_m=0, b_n s=0, b_n u_m=δ_nm. These give `invM₁` through
`invM₅`. These are products of the *whole* matrices, not principal-block
inverse assertions. At H=0 both define -s^-1 and agree by uniqueness.
The nonempty residual windows at equal nonzero factor heights must still
be inverted; `SwappedHomInversion.md` §5 treats these, retaining γ(0)=q.
The scalar zero-height rule does not discard those residuals.

## 5. Distinct-colour inverses and the conditional action theorem

Fix i≠j and take L_a,L_b,L_c,L_d to be the A/B raising edges. For an
upward entry t:L_c L_d→L_a L_b in execution order, the projection of the
literal mate is

    M(t) = (R_a L_c ◁ η_d);
           (R_a ◁ t ▷ R_d);
           (ε_a ▷ L_b R_d)
         : R_a L_c -> L_b R_d.                            (A8)

Every unit and counit is the one of §1 at its own edge. Even sector
projections select exactly this entry. Distinct-colour crossings exchange
sector labels, so these four entries form a block permutation, not the
same-colour central two-by-two block. Their upward inputs are the pre/pre
crossing, post/post crossing, J^-1 and QJ.

### Pre/pre

`SwappedDistinctPreMate.md` (1)–(15) evaluates the prescribed reversed-label
factor crossing, not its inverse. In that note's edge notation put
k=h_i(nu), d=d_ij, sigma=p_i(k+1), and

    g(h)=1 (h>0), g(h)=(-1)^(p_i(h+1)) (h<=0),
    delta_ij(k)=t_ij (-1)^(p_i p_j sigma) g(k-d)/g(k).

Its endpoint removals C,D both have parity sigma. For the factor maps
ell_ij=lcrossL i j and s_ij=sigmaL i j, its coordinate identity and inverse
are

    C^-1;M_pre;D=delta_ij(k) pre(ell_ij),
    N_pre=delta_ij(k)^-1 D;pre(s_ij);C^-1.              (A9)

Both products are identities by the factor `invNe₁`, `invNe₂` and adjacent
C,D cancellation. The scalar includes both the normalized-left height
window and the pitchfork sign; it is not just gamma(k). Its inverse uses
t_ij^-1. The proof's formal-content cover provides source bubble scalars
without imposing their existence on X, and those auxiliary scalars cancel.

### Post/post

This uses the **distinct-colour** factor mate of
`DeformedActionAssembly.md` §§3–4, whose explicit inverse is J^-1 rho^-1
there, not the same-colour principal component in `HomProbeMatrix.md`.
Fix probe content b and put k_i=p_i P(b), k_j=p_j P(b), a=k_i+k_j.
Write M_j=post(E_j^W), N_i=post(F_i^W). The two Hom words are
S_(k_j) M_j N_i S_(k_i) and N_i S_(k_i) S_(k_j) M_j.
Their even comparisons to S_a M_j N_i and S_a N_i M_j are respectively

    E_src=S_(k_j)(beta_(M_j N_i,k_i)^-1);c_(k_j,k_i),
    E_tar=N_i(c_(k_i,k_j));beta_(N_i,a)^-1,
    c_(1,1)=xi, c_(0,t)=c_(t,0)=1.

Whiskers are at the indicated word endpoints. Expand (A8) with the post
unit and counit (A4), and the even upward word transport of
`MixedColourBlockCompletion.md` (3). Each inserted inverse comparison
cancels the next comparison; the S_(k_i)^2 pair cancels using xi from
the unit and cap. Reassociation and beta naturality leave the factor
unit–crossing–cap word, under S_a. The only possible residual crossing
sign is (-1)^(a p_i p_j)=1, since
P(b)(p_i+p_j)p_i p_j=0. Thus, writing s_W for that factor distinct mate,

    M_post=E_src;S_a(post(s_W));E_tar^-1,
    N_post=E_tar;S_a(post(s_W^-1));E_src^-1.

Both products cancel adjacently to identities. This also explains why a
bare pair of z removals, instead of xi, would not give this transport.
No normalized-left factor comparison or same-colour matrix component is
being substituted for the distinct right mate.

### Mixed sectors

Index the imported mates of `SwappedDistinctMixedMates.md` by their
ordered pair: U_kl=M(J_kl^-1), V_kl=M(Q_kl J_kl). Its (2) types U_kl
as a block of s_lk, but V_kl as a block of s_kl. Thus the mixed blocks
of the fixed s_ij are **U_ji and V_ij**, not U_ij and V_ij.

For V_ij retain that note's (i,j) square and D_s,D_t from (1)–(6):
p=p_i, q=p_j, r=pq, t=q P(b), u=t+r,
sigma=p(h_i(-Lambda_P+alpha(b-i))+1). Its raw interchange is
h_A:post(E_j) pre(F_i) -> pre(F_i) post(E_j).

For U_ji exchange i and j throughout the imported U calculation. To
keep its content square separate, write b_U,c_U for its local contents:

    D0_U=H_(b_U,c_U),       C0_U=H_(b_U-j,c_U),
    D1_U=H_(b_U,c_U+i),     C1_U=H_(b_U-j,c_U+i),
    L_U=pre(E_j^T),        M_U=post(E_i^W), N_U=post(F_i^W),
    t_U=p_i P(b_U),        u_U=p_i P(b_U-j)=t_U+r,
    T_U=N_U S_(t_U),       T'_U=N_U S_(u_U).

Here L_U maps D_s_U to C_s_U, and T_U,T'_U lower the reservoir i edge.
Functionally U_ji:L_U T_U -> T'_U L_U maps D1_U to C0_U. For H in D1_U
the imported coordinate maps and even raw interchange are explicitly

    C_s^U=L_U N_U(z_(t_U)(H)),
    C_t^U=N_U(z_(u_U)(L_U H)),
    h_B^U:L_U N_U -> N_U L_U.

Thus the same universally quantified calculation (8)–(15), instantiated
at (j,i) for U and at (i,j) for V, gives

    (C_s^U)^-1;U_ji;C_t^U=beta_U h_B^U,  beta_U=(-1)^(t_U r),
    D_s^-1;V_ij;D_t=alpha h_A;G,         alpha=(-1)^(sigma u),
    U_ji^-1=beta_U C_t^U;(h_B^U)^-1;(C_s^U)^-1,
    V_ij^-1=alpha D_t;G^-1;h_A^-1;D_s^-1.             (A13)

Both raw interchanges are even associators. Crucially, in V_ij,
**QJ bends the pre unit-probe strand**. On its raw target KM,

    Z_H=a_(KH);K(d_(KH));K(v_H),
    G(Z,Y)=sum_(m,n) a_mn (-1)^(p binom(m,2)) Z^m Y^n,
    Q_ij(X,Y)=sum_(m,n) a_mn X^m Y^n.                  (A14)

The a,v are the specified normalized-left probe unit and cap, Z is their
transpose of the probe dot, and Y is the surviving reservoir dot. This
is not a surviving probe dot with a transposed reservoir dot. The transpose
law gives Z^-1=(-1)^p Z(d^-1). Both dot powers in every supported monomial
have parity zero; their **integer exponents** need not both be even.
The signed power (-1)^(p binom(m,2)) is retained even on this support.

Let A be G's Y-free leading unit, H=G-A and E=A^-1 H. If Y^N=0, then
E^N=0 and

    G^-1=(sum_(ell=0)^(N-1) (-E)^ell) A^-1.           (A15)

Both products are identities in the commuting supported-power algebra.
The dotless residual signs alpha,beta_U and the monomial transpose signs
are part of the prescribed mates, not adjustable normalizations.

### Componentwise assembly and theorem

Let P_src,P_tar be the even direct-sum permutations separating the four
supports. Equations (A9), the post/post formula, and (A13) give

    P_tar s_ij P_src^-1=diag(M_pre,M_post,U_ji,V_ij),
    lcross(i,j)=P_src^-1 diag(N_pre,N_post,U_ji^-1,V_ij^-1) P_tar.

Multiplication in either order is the identity: orthogonal sector
projections remove off-diagonal entries and the four diagonal products
are the two-sided identities already proved. All entries have parity
p_i p_j. Zero/absent supports satisfy the same identities with their zero
identity. Section 2 ensures that these finite-support inverse matrices
assemble over every product weight fibre, even when its size and the
contentwise nilpotence exponents are unbounded. This proves both
`invNe₁` and `invNe₂` for the prescribed fused mate.

**Conditional finite-colour swapped superaction theorem (written).**
For every finite J, original weight group X, external weight mu and
factor data F1–F4, (A1)–(A6), the even diagonal right adjunction, (A7)
and the preceding distinct inverse define a k-linear parity-superaction
of the entire J-colour presentation of Brundan–Ellis Definition 1.5,
with original Sc and original heights. It acts on C_(lambda,0) at every
lambda in X. Its inverse generators obey the finite height windows,
including agreement of the two same-colour definitions at height zero.

Proof. Section 1 constructs the objects, E,F and even adjunction;
§2 constructs homogeneous natural generator maps with locally finite
matrix products. The table in §3 discharges every constructor of `Rel`:
all square and slide cases, all uncorrected and corrected braids, both
zigzags, the two distinct inverses just proved, all five products in each
same-colour height regime from §4, and both out-of-window zero rules.
`sigmaL` is a defined word, not an extra constructor or an extra premise.
Super interchange holds in the target. Consequently the assignment kills
the linear contextual ideal and factors through the presented category.
No factor relation of the desired fused action was assumed. ∎

## 6. Surviving vacuum blocks are forced by the construction

The support calculation uses only the specified upward maps. By §5
these maps now belong to the conditional full presentation action. On T_0-supermodules let

    V(M)=Abar ⊗_k M,

as a functor to W_0, and put all other components of the object of C_(μ,0)
equal to zero. Here Abar is the fixed reservoir coefficient quotient and
T_0=k. The map on a homogeneous input u of parity r is
 a⊗m↦(-1)^(r|a|)a⊗u(m).

An A step decreases nonnegative probe content. Starting at b=0 it therefore
lands in the absent predecessor and is zero. A B step leaves b unchanged.
Consequently every upward sector path containing A is zero, including
ones preceded by arbitrarily many B steps. On the only surviving path
b=0 throughout, so κ_i=p_i P(0)=0, all z/β/ξ comparisons there are identity,
and every B functor, dot and crossing is literally reservoir postcomposition.
Mixed entries cannot connect this all-B path to another sector count.

For a displayed source word t, put ν=reverse(t). Multiplication of the
induction kernels gives

    V_t(M)=(B_(content(t)) e_ν) ⊗_k M,
    b⊗c ↦ b append_i(c),      z ↦ z⊗e_ν.                 (A10)

Balancing and the right idempotent give both inverse identities. No
flatness assertion is involved. The kernel dot is R_x(z)=(-1)^(|x||z|)zx;
the crossing is R_τ for distinct colours and -R_τ for equal colours.
These are exactly the surviving maps, because the all-B restriction
just proved contains no rational mixed term and no parity-removal factor.
For chronological multipliers b_1,...,b_l their value on z is

    (-1)^((Σ|b_j|)|z|+Σ_(j<k)|b_j||b_k|) z b_1...b_l.    (A11)

A signed left-module map φ:B e_ν(s)→B e_ν(t) of parity r is recovered from
b=φ(e_ν(s)) by φ(z)=(-1)^(r|z|)zb. Therefore its corner is
 e_ν(s) B e_ν(t), and evaluation of φ_b;φ_c is (-1)^(|b||c|)bc.
Evaluation of transformations V_s→V_t at k has the same inverse: extend
φ by φ⊗id; naturality against the maps k→M given by homogeneous vectors
forces that extension. This proves the corner identification, not merely
an equality of dimensions. Coefficients act by L_a=R_a, since a is
supercentral.

Equations (A10)–(A11) and this evaluation are precisely the word, signed
corner and generator formulas used in `SwappedVacuumCoordinates.md`
§§2–3 and (7). They are now consequences of the explicit upward assignment,
not a separate `VacuumIdentification` premise. The same formulas therefore
evaluate morphisms of the full quotient under F1–F4. Their signed affine
presentation equivalence and inverse-ideal bound apply on the admissible
windows of that note; no equality with the raw first-boundary ideal is used.

### All-height normalized bubble corollary

Let P_i,N_i be the probe and reservoir levels at the vacuum, so
H_i=P_i-N_i=h_i(mu), and P_i=2M_i for odd i. Write
C_i(z)=sum chi_(i,r) z^r and E_i(z)=sum e_(i,r) z^r for raw reservoir
coefficients (constant coefficient 1). Under F1–F4, at **every** sign of H_i,

    odd i: sum betaD(e_r)(V) z^r = L_(C_i(-z)/(1+z)^(M_i)),
           oddBubble_i(V)=(-1)^(N_i+1) L_(delta_i),
    even i: sum beta(e_r)(V) z^r = L_(E_i(-z)/(1-z)^(P_i)). (A16)

L on a formal series means coefficientwise left multiplication.
`SwappedVacuumBubbles.md` proves H_i>0 using the extreme inverse column.
`SwappedVacuumNonpositiveBubbles.md` proves H_i<0 using the extreme inverse
row and H_i=0 using the principal inverse; it computes the odd image
before applying the elementary/complete symmetric-function identity.
These are the full matrices of §4, not forward mate projections. The odd
probe signed dot satisfies (x^2+1)^(M_i)=0, although its algebra polynomial
is (u^2-1)^(M_i). Both proofs retain all exterior directions and the
positive even-cutoff ELV relation. Zero-level variants require such factor
inputs separately; F2 here uses the cofinal positive probe levels.

On an upward word, source placement of b in (A16) acts by L_b on its
reservoir kernel: (-1)^(|b||z|) z b a=b z a. Hence these are normalized
word-Hom bubble values, not just equalities on a vacuum vector.

### Bounded vacuum corollary and its separate consumer

For any mixture of height signs define theta on the **untruncated**
coefficient polynomial/exterior algebra by the right-hand series in
(A16) and delta_i↦(-1)^(N_i+1)delta_i. Its inverse sends

    odd: C_i(z) -> (1-z)^(M_i) C_i(-z),
    even: E_i(z) -> (1+z)^(P_i) E_i(-z),
    delta_i -> (-1)^(N_i+1)delta_i.

Both preserve parity and the increasing coefficient-weight filtration,
and commute with the source-order involution sigma. They are not asserted
to preserve any finite ELV quotient. Let F_d, q_K, coordK and the k-linear
splitting L_d be exactly those of `SwappedVacuumCoordinates.md` §§6–7.
Choose N0<=N_i and truncation powers with

    d+2 choose(length(s),2)<N0,
    L_a coefficientWeight(c_a)>=N0.                     (A17)

The same fixed truncation is used throughout the tower. The square and
recovery are

    coordK(act(alpha(f))(bubbles(a)(vacuum(s))))
        =q_K(sigma(theta(a) tensor f)),
    recover=q_first o theta^-1 o sigma o inclusion(F_d) o L_d o coordK,
    recover(act(alpha(f))(bubbles(a)(vacuum(s))))
        =q_first(a tensor f),             a tensor f in F_d. (A18)

This follows by composing the signed-coordinate lemma with the two
height-range bubble lemmas: theta,theta^-1,sigma preserve F_d and
L_d splits q_K on F_d. It needs no raw coefficient-linearity of recover,
no quotient automorphism theta, and no arbitrary-Hom base change.
Cofinal cutoffs and sufficiently high fixed coefficient powers supply
these observations for each prescribed finite window. This is the bounded
vacuum result, not a completed detecting-family consumer: packaging and
using admissible observations is separate from the action theorem.
In particular the existing total-window interface is not filled by
setting inadmissible zero windows to zero; those still contain identities
and crossing-only diagrams. No such kernel-compatibility extension is proved.

## 7. Finite-colour compatibility without a base-change Hom claim

Here is the cheaper passage to arbitrary I. It uses a finite action for
each required finite support, not one global Hom action. There are two
different compatibility statements to distinguish.

First fix finite J⊆K and compatible cutoff data on K. Let A_J,A_K be the
reservoir coefficient algebras, with identical powers used to truncate
shared generators. Their presentations give

    A_K = A_J tensor^s A_(K\J),
    B^K_β = A_K tensor_(A_J) B^J_β       (supp β⊆J).     (A12)

The same statement without truncation holds. Each extra-colour algebra
has augmentation sending its positive generators to zero. Thus inclusion
A_J→A_K has a left inverse and does not kill independent coefficients.
The ELV relations involve only their own colour, including δ_i χ_(i,m)=0
at positive even odd-colour cutoff. They introduce no cross-colour quotient.
For the probe the specialized coefficient algebra is k on both sides.

To prove (A12), present both sides by the coefficients, word idempotents,
dots and crossings at content β. Every word uses only J, so all affine
and first-position relations are the same. The two namesake generator
maps are inverse. For i∈J and supp(β+i)⊆J this identification commutes
with append_i. Consequently it identifies the induction kernels, the
restriction corners, and their balanced tensor products. On pure tensors
the comparison is the multiplication-of-coefficients map, with the super
balancing sign; its inverse inserts 1. Associativity of multiplication
makes it coherent for successive append operations. Units, counits, dots
and crossings are the same insertion/multiplication maps. The prescribed
inverse matrices commute with this identification by uniqueness of a
two-sided inverse. This is an exact cross-support comparison of the factor
functors on extended modules, not a dimension or flatness argument.

It does **not** identify A_K⊗Hom(M,N) with Hom(A_K⊗M,A_K⊗N) for arbitrary
modules or superfunctors. To compare a finite diagram within a K-action,
restrict to the content blocks with support in J but keep coefficients
A_K. Then the smaller coefficient-extended tower is literally the same
presented tower as those K blocks. Its Hom categories are taken between
these same categories; pre/post functors, parity shifts, and all rational
maps agree. Bounds may be chosen differently, but finite inverse formulas
agree by uniqueness. There is no base change of an arbitrary Hom space in
this comparison. Contents using K\J give other components of the K-action;
restriction to the J-supported components is preserved by J-labelled edges.

Second, the presentation itself has a directed finite-support property.
Keep the **whole X** and all its weights when restricting colour labels to
J. The restricted datum uses h_i:X→Z and α_i∈X unchanged, not a smaller
root-span weight group. Inclusion J⊆K sends every generator to its namesake.
The height windows of every inverse relation are unchanged. Thus it sends
each defining relation and each of its contexts to the same relation in K.
It defines a functor on presented categories. Faithfulness of this functor
is not assumed.

## 8. Finite derivations suffice for arbitrary-colour detection

**Finite-witness lemma (written).** If a finite linear combination d of
diagrams is zero in the I-colour presentation, there is a finite J⊆I
containing the colours of d and a derivation that d is zero using only
J-coloured diagrams, while retaining the original weights in X.

Proof. The linear contextual ideal is generated by finite sums of scalar
multiples of contextual instances of defining relations and super
interchange. Its generation is finitary: membership is a finite expression
using addition, scalar multiplication, composition and whiskering. Equally,
an inductive congruence proof uses a finite proof tree. Take the union of
the colours of every generator diagram and every left/right context in
that expression or tree. Each word, layer list and defining relation is
finite; inverse windows have finite integer length. Hence the union J is
finite. The same expression is valid in the J presentation, since α,h,
parameters and all weight labels have been retained. This includes colours
introduced and later removed by cups or caps, not only colours visible on
the boundary of d. No projection deleting those cups is used. ∎

For a proposed nonzero coefficient-affine combination f, also include the
finitely many colours appearing in its coefficient monomials. Coefficient
inclusion into any larger finite support is split by augmentation of the
new polynomial and exterior generators. The affine diagram part at fixed
content has the identical generator/relations presentation, since dots
and crossings never create colours. Thus f remains nonzero on enlarging
support; in coefficient coordinates this is the split coefficient map
tensored with the unchanged affine module, not an assumed injection of
full SKM Hom spaces.

Suppose, conditionally, that every finite restricted datum has the required
bounded detecting observations at every original λ, on the same action
and with normalized bubbles. If the image of f were zero in the I-colour
SKM category, apply the finite-witness lemma to that zero equality, then
enlarge its finite set to include f's coefficients. Apply the detecting
observation for this enlarged finite datum, with cutoff and homogeneous
coefficient truncation sufficiently large for f. It annihilates the finite
derivation but does not annihilate f, a contradiction. This proves the
arbitrary-colour implication from the finite-colour detection assertion.
It does not assume that an action for the original smaller support extends
to I, or that a chosen test object is compatible under all enlargements.

The auxiliary pairing extension can be made after choosing the finite
witness support. Its first coordinate is still the entire X. Mapping
λ to (λ,0) preserves every region and relation in that finite derivation.
Cofinal cutoffs are selected for all colours in this finite witness, not
just for the upward boundary word. This is why outside-colour cup/cap
contexts cause no exception.

All reservoir bounds used in this argument are those for one fixed finite
alphabet and one coefficient quotient chosen for its entire tower.
A global quotient that truncates only the initially active colours is not
being used. No claim of finite dimension for an infinite-colour coefficient
algebra, and no uniform joint nilpotence from such a claim, is needed.
One must not change the coefficient algebra with β and then assume append
compatibility: (A12) only proves it for a fixed common presentation.

## 9. Scope of the remaining work

The target of Definition 1.5 is a parity-superaction. The probe
specialization is not integer graded. `ReservoirVacuumEvaluation` and
`FusedFixedWeightFamily` in `ReservoirVacuumDetection.lean` demand linear
actions and bounded affine-coordinate laws, not a standard integer-graded
fused action. The independent reservoir grading suffices for the finite
series above and for the nilpotent closed-coefficient ideal used in
`SwappedHomInversion.md`. Requiring a full integer-graded fusion would be
a stronger package and is not inferred here.

The conditional action theorem has no remaining local presentation relation:
§5 closes the distinct pre/pre, post/post and both mixed mate entries; §4
uses the whole same-colour inverse, not just its principal components.
All-height normalized vacuum bubbles and the admissible-window recovery
are now the written corollaries (A16)–(A18). The exact predicate ledger is:

| Conclusion | Hypotheses beyond the datum and base field | Boundary |
|---|---|---|
| Finite-colour parity-superaction | F1–F4 only | Full factor existence and their implementation are not inferred. |
| All-height normalized vacuum bubbles | Same F1–F4, the specified vacuum | No extra bubble or vacuum-identification predicate. |
| Admissible bounded recovery | F1–F4 and the explicit inequalities (A17) | A k-linear splitting on the bounded image, not a total zero-window extension. |
| Arbitrary-colour detection implication | Finite-colour detecting models at every original weight and every required finite window, as stated in §8 | Finite-witness passage only; neither global Hom base change nor an infinite-colour action. |

The bounded-observation consumer and its detection conclusion remain
separate. No nondegeneracy theorem, full integer-graded fused action,
raw coefficient-preserving global quotient isomorphism, or Lean proof
of this assembly is asserted. Existing kernel-checked principal mate
comparisons do not formalize the whole matrices or their assembly.
