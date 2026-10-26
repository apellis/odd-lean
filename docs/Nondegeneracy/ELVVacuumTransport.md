# ELV vacuum transport: coefficient repair and orientation boundary

**Status: proposed written mathematics, not a Lean theorem or an accepted
vacuum comparison.** This audits the route at commit
`0ff8a979490399ff6104caf5fbcf52a69914a0c1`. There is an explicit, invertible
all-colour coefficient repair. It preserves the exact coefficient ideal,
including the even-cutoff exterior relation, and bounded coefficient
detection. It does not supply the missing Hom orientation. The natural
position-reversing super-opposite generator candidate also exchanges the
first and last cyclotomic boundaries. Those boundaries cannot silently be
identified. The investigation stops at that concrete comparison obligation;
it does not replace the specified action.

## 1. Exact coefficient pullback, for every cutoff

Fix the cutoff function N. Write A_inf for the polynomial/exterior model
of `SYM`, and J_N for `SYM.elvCoefficientIdeal`. For an odd colour i use
one-based chi_(i,r), chi_(i,0)=1, and delta_i. Define theta_N on generators:

    even colour i:  e_(i,r)       |-> e_(i,r),
    odd colour i:   chi_(i,r)     |-> (-1)^r chi_(i,r),
                    delta_i       |-> (-1)^(N_i+1) delta_i.       (1)

The exponent N_i+1 is convenient at N_i=0; it is equivalent modulo two
to N_i-1. On the code's zero-based odd elementary generator e i r, the
sign is (-1)^(r+1). No two exterior generators are identified.

The polynomial universal property and the exterior universal property
extend (1) to a k-superalgebra automorphism of A_inf. Its square is the
identity on every generator, hence on the algebra. This argument applies
to arbitrary colour sets: every expression has finite support. Both parity
and the independent positive integer grading are preserved.

Here is the image of EVERY defining coefficient relation:

* An even-colour elementary generator beyond rank N_i is fixed.
* An odd-colour chi_(i,r) beyond rank floor(N_i/2) is multiplied by (-1)^r.
* For N_i=2m, delta_i chi_(i,m) is multiplied by (-1)^(m+1).
  At N_i=0 this is the relation delta_i itself, not a missing generator.
* For N_i=2m+1 there is no top exterior relation to introduce.

Thus theta_N(J_N) is contained in J_N by applying theta_N to each
sandwich a r b in its two-sided span. Applying the involution again gives
the reverse inclusion. In particular

    theta_N(J_N)=J_N,
    theta_N : A_inf/J_N -> A_inf/J_N is an involution.       (2)

This is equality of the actual coefficient ideals, not an isomorphism to a
larger exterior quotient or a change of cyclotomic coefficients by fiat.

For detection, each polynomial/exterior basis monomial is multiplied by a
unit sign. Its coefficient weight and integer degree are unchanged.
Consequently theta_N and its inverse preserve `CoefficientAtMost d` and
`CoefficientAtLeast d`. If the quotient map is injective on the bounded
span, its composite with theta_N is injective there too. This holds even
when theta_N varies with N: each individual kernel on that bounded span is
zero. The balanced schedules keep each N_i parity fixed, so their delta
signs in fact agree across the schedule. No flatness or faithfulness of a
factor action is used. This proves preservation of coefficient detection;
it is not yet a categorical bubble-coordinate statement.

## 2. Derivation of the cutoff-dependent delta sign

Let x be the odd dot of colour i and work first in the free coefficient-dot
superalgebra, with x a = (-1)^|a| a x for homogeneous a. Put

    q(n)=(-1)^(n(n-1)/2).

Its super-opposite has b^sop c^sop=(-1)^(|b||c|)(cb)^sop.
In the coefficient matrix category, multiplication is endomorphism order;
chronological composition satisfies

    (a tensor f);(b tensor g)=(-1)^(|a||g|) ba tensor (f;g).

Send x^sop to the coordinate dot y and a^sop to theta_N(a).
For a homogeneous coefficient a this gives the precise local formula

    (a x^j)^sop |-> q(j) theta_N(a) tensor y^j.             (3)

Indeed (x^j)^sop=q(j)(x^sop)^j. Reversing a and x^j in the super-opposite
introduces (-1)^(|a|j); multiplying y^j after the coefficient in the target
introduces the same sign. They cancel. This is why an extra sign depending
on the parity of a must NOT be appended to (3).

Write c_d=chi_(i,d/2) for even d and
c_d=delta_i chi_(i,(d-1)/2) for odd d. The literal code polynomial is

    f_N(x)=sum_(j=0)^N (-1)^(N(j+1)) c_(N-j) x^j.         (4)

For N=2m this is C(x^2)+delta_i x(C(x^2)-chi_m)/x^2;
for N=2m+1 it is (x-delta_i)C(x^2). These are exactly the assembly's
polynomials after placing coefficients on the left.

Demanding that (3) send f_N to a unit multiple of the same monic polynomial
forces the multiple to be q(N). For d=N-j=2r, the required exponent is

    binom(N,2)-binom(N-2r,2) = r  (mod 2).

For d=2r+1 it is

    binom(N,2)-binom(N-2r-1,2) = N-1+r  (mod 2).

These identities follow by expanding the binomial coefficients. Hence
chi_r must acquire (-1)^r and delta_i must acquire (-1)^(N-1), proving (1),
rather than extrapolating the cutoff-two example. Term by term,

    f_N(x)^sop |-> q(N) f_N(y).                            (5)

For an even colour all dots and coefficients here are even, and its literal
alternating elementary polynomial is unchanged. N=0 gives 1 on both sides.
The inverse of (3) has the same generator signs and q(N)^2=1, so (5) proves
both inclusions of the polynomial-generated ideal in this local algebra.
At odd N=2 it reads chi_alg -> -chi_coord and delta_alg -> -delta_coord;
at odd N=3 the delta sign is +1. These signs retain the whole exterior
coefficient, not merely its delta=0 specialization.

A supplementary exact integer check tested the termwise parity identity
for all 0<=j<=N<=64 (2145 terms), with no failures. The proof is the two
identities above, not that finite test.

## 3. One explicit global candidate, and its boundary problem

The factor algebra is R_A(S), S=`parameterTwist Sc`. The prescribed
transformations are R_x and epsilon_ij R_tau, where
R_b(z)=(-1)^(|b||z|)zb and epsilon_ij=-1 for i=j, +1 otherwise.
There is no freedom here to choose the equal-colour crossing sign.

For a word nu of length n, write rev(nu) for its reversed list. The natural
candidate matching execution order has the following generator table:

    e_nu^sop             |-> e_rev(nu),
    (x_r e_nu)^sop       |-> y_(n+1-r) e_rev(nu),
    (tau_r e_nu)^sop     |-> epsilon_(nu_r,nu_(r+1)) times
                            the crossing rev(s_r nu) -> rev(nu),
    (a e_nu)^sop         |-> theta_N(a) e_rev(nu).          (6)

The crossing is at positions n-r,n+1-r in the target. Its endpoints are
reversed because super-opposite reverses the two matrix corners. The list
reversal is separate from that vertical reversal. (6) is a CANDIDATE
presentation map, not a theorem that a particular action is faithful.

Why list reversal cannot simply be omitted: in ordinary matrix order the
equal-colour relations read, with s=(-1)^p,

    tau x_1-s x_2 tau=1,     x_1 tau-s tau x_2=1.

These are the relations explicitly recorded in `GlobalSlideAlgebra.lean`.
Super-opposite, followed by x_r -> y_r and tau -> -t, sends the first
left-hand side to -s(y_1 t-s t y_2)=-s, not 1 in general. In particular
it fails for an even colour. With x_1 -> y_2, x_2 -> y_1 the image is
-s(y_2 t-s t y_1)=1, as required. Choosing a different crossing to avoid
this test would cease to compare the prescribed factor generators.

The affine parameter requirement for (6) is precisely the mixed quadratic
sign (-1)^(p(i)p(j)+p(i)floor(r/2)+p(j)floor(s/2)). The reverse-label and
ordered corrected-braid computations are recorded in
`DeformedActionAssembly.md` §6 and `DeformedMixedBraid.md` §§2–3. Those
written calculations are evidence for this candidate; this note does not
promote them, or the smaller `RouquierFamily` interface, to a newly checked
full presentation equivalence. An explicit inverse presentation map and
compatibility with the concrete tensor functors are still required.

Even GRANTING that affine equivalence, (6) has the following exact images
of the full ELV generators, obtained without any crossing reduction:

* Coefficient-ideal entries go to coefficient-ideal entries, by (2).
* A first-position odd f_(N_i) at i::tail goes to q(N_i) times the
  LAST-position f_(N_i) at rev(tail)::i, by (5).
* A first-position even polynomial goes to the corresponding
  LAST-position polynomial, without a sign.

Therefore the resulting two-sided ideal is the last-boundary ELV ideal,
not a demonstrated copy of `ELVRelationSpan` with its first boundary.
Under the granted affine equivalence both inclusions follow: map a
sandwich into the last-boundary ideal; every last-boundary generator is
the image of its reversed first-boundary generator times q(N_i), a unit.
This gives a precise conditional full-ideal statement, not a silent
replacement of the target quotient. Right append also becomes left prepend.

The boundary distinction is genuine. Specialize all deformation parameters
to zero, take two distinct even colours i,j with one Cartan edge and
Q_ij(0,0)=Q_ji(0,0)=0, and take N_i=1,N_j=0. In content i+j the first-boundary
quotient kills e_ji. It has a nonzero representation with e_ij=1, e_ji=0,
all dots zero and both crossings zero: every affine relation and both
first-boundary relations hold. The last-boundary ideal instead contains
e_ij. Thus the two ideals are unequal in the same indexed algebra. This
uses a permitted zero cutoff and a nonzero even ground field; an all-cutoff
claim must include it. Reversal may relate different indexed quotients;
it is not an identity of the old quotient or of its word coordinates.

## 4. Which Hom family and which vacuum?

The actual typed definitions inspected are `homWeightSector`,
`homContentPreE`, `homContentPostE`, and the canonical
`homContentPreAdjunction ... T.leftAdjoints`. No declarations literally
named `actualRouquierHomContent` or `normalizedHom` were found in this
checkout; those descriptions must not be mistaken for additional proved
transport theorems. They give

    Hom(T(-muP), W(muM)),
    L_A=pre(E_T),  L_B=parityShift post(E_W).

For the unreversed lowest-weight towers C_R(-Lambda_R+beta_R) and
C_P(-Lambda_P+beta_P), taking T=C_R and W=C_P puts the content-zero
vacuum at (muP,muM)=(Lambda_R,-Lambda_P). The sum of sector labels is
Lambda_R-Lambda_P, the required reservoir-minus-probe convention.
But pre(E_R) decreases beta_R, so at the reservoir boundary its first
upward step is zero. Post(E_P) increases probe content. Neither coefficient
pullback (1) nor a module super-opposite changes these functor endpoints.

Swapping the towers gives the desired support pattern: the probe is the
input of the extension-by-zero vacuum, so pre(probe induction) is zero,
and reservoir post(induction) grows beta_R. However its zero-content
labels are (Lambda_P,-Lambda_R), with total Lambda_P-Lambda_R. This is
minus the stipulated external weight, not the old weight with new names.
Formal contents beta_R,beta_P must be retained even if external weights
coincide. Correcting this sign requires an actual action transport and a
comparison of its generators, not a relabelling of coroot values.

There IS a proved full-presentation symmetry worth using, rather than
inventing a multicolour reversal from rank-one data. `chevalleyTwo` sends
lambda to -lambda and E_i to F_i, F_i to E_i, into `TwoSOp`. Its exact
generator images, from `chevL` and `chevC`, are:

| generator | image, read in the reversed 2-morphism direction |
|---|---|
| dot | downward dot |
| crossing i,j | -(-1)^(p(i)p(j)) downward crossing j,i |
| right cup / right cap | right cap / right cup |
| mixed left crossing i,j | minus mixed left crossing j,i |
| inverse cup / cap with n dots | (-1)^(n p(i)) inverse cap / cup |

It preserves the independent integer degree. Applied to an actual full
action C, its reflected object is C(-lambda) in the super-opposite target,
and its upward functor is the OLD restriction, not the OLD induction.
Consequently applying Chevalley to the swapped Hom action to repair its
external weight also changes the upward word whose vacuum coordinates are
being requested. It does not establish the old induction square.

The normalized precomposition adjunction has an additional fixed obligation:
with h the reservoir source height, sigma=p(i)(h+1), and
c=(-1)^(sigma^2)*(1 if h<0 else (-1)^p(i)), its unit uses leftCup followed
by output parity removal; its counit uses (-1)^sigma c^-1 leftCap with
the specified parity comparison. `HomSectorTransport.md` (4)–(5) and
`RouquierNormalizedHomAdjunction.lean` prove these formulas. Chevalley's
right cup/cap exchange cannot be identified with them by dropping c, sigma,
or the output comparisons. A right transpose also sends an odd n-th dot
power to q(n) times the n-th power of the transpose.

Thus the exact remaining orientation task is to give one full-action
transport with these weight labels and cup/cap conventions, identify its
content-zero vacuum and upward words with the required first-boundary
rows, and show that its dots/crossings become the specified coordinate
generators. The existing Chevalley theorem supplies a full symmetry, but
not this module/vacuum comparison. No new full multicolour action is
asserted from `RouquierFamily` alone.

## 5. Balanced kernel and stopping point

Once a compatible first-boundary transport has really been supplied, the
candidate kernel is fixed, not chosen by dimension:

    B_i(s,u)=C(s,J_i u),
    kappa([b tensor m])=b;J_i(m),
    iota(h)=[h tensor 1_t],

where J_i is right append and C is the EXACT first-boundary ELV quotient.
The balancing identity (b;J_i a);J_i m=b;J_i(a;m) proves descent and both
inverse identities. Postcomposition by a generator g then commutes with
kappa by associativity. This is the square already justified for the
representable kernel, not for the factor's signed multiplier. Candidate
(6), in contrast, naturally produces the last-boundary/prepend version.
Neither its kernel nor its coordinate indices may be substituted here
without the missing comparison.

The coefficient action to compare, if the generator transport succeeds,
is the pullback: the coordinate coefficient a corresponds to the factor
coefficient theta_N(a). Equation (2) makes this invertible and detection
preserving. Coefficient preservation over the identity was an unnecessary
strengthening, not a user requirement; its cutoff-two failure is repaired
algebraically by (1). The orientation and boundary obligations are not.

**Stop/research decision:** an existing-route continuation must first prove
that the actual reversed Hom vacuum realizes the required first-boundary
append kernel, including the preceding generator and adjunction table.
If this requires replacing the factor action, changing the external-weight
convention or the headline theorem, or postulating a new full-action
reversal, that is a new research steer for Alex, not authorized by this
repair. This note implements none of those alternatives. No integer-graded
probe is required; reservoir positivity is retained. No normalized bubble,
fusion, or nondegeneracy claim follows.

## Internal definitions audited

* `SKM/BubbleELVCoefficients.lean`: `elvMonicCoefficient`, `evenMonicCoefficient`.
* `SKM/BubbleELVSpecialization.lean`: `ELVCoefficientRelation`, `elvCoefficientIdeal`.
* `SKM/BubbleCoefficientGenerators.lean`: polynomial/exterior generator coordinates.
* `QuiverHecke/CoefficientExtension.lean`: `coefficientHom_comp`.
* `QuiverHecke/WeightedCoefficientSeparation.lean`: `deformedCyclotomic`.
* `QuiverHecke/ELVCyclotomicSeparation.lean`: `ELVGenerator`, `ELVRelationSpan`.
* `QuiverHecke/CyclotomicAction/ParameterTransport.lean`: parameter signs and involution.
* `QuiverHecke/CyclotomicAction/GlobalSlideAlgebra.lean`: both equal-colour slides.
* `QuiverHecke/Algebra.lean`, `AlgebraMaps.lean`: corner and opposite conventions.
* `SKM/RouquierHomContent.lean`, `RouquierNormalizedHomAdjunction.lean`.
* `SKM/ChevalleyBase.lean`, `Chevalley.lean`, `ChevalleyTwo.lean`.

The surrounding written comparisons read were `ELVVacuumGeneratorComparison`,
`RegularVacuumComparison`, `DeformedActionAssembly`, `DeformedGradedAction`,
`DeformedMixedBraid`, `HomSectorTransport`, and `ProbeReachability`.
