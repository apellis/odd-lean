# Cyclotomic probes with invertible dots

**Status: proposed written proof, not a Lean theorem.** Under the full-action
hypotheses of `DeformedActionAssembly.md`, `DeformedMixedBraid.md` and
`DeformedGradedAction.md`, the specialization below supplies a parity-graded
probe action on all content blocks with invertible dots. No localization of
module categories or assumption that induction preserves a spectral subcategory
is used: the dots are already units in the specialized cyclotomic algebras.
The whole prescribed local inverse matrices specialize with the action.
This is a factor construction, not fusion or nondegeneracy.

## 1. Datum, coefficients and specialization

Fix a finite compatible colour support in a symmetrizable Cartan superdatum,
a nonzero purely even commutative ring k with 2 invertible, and the homogeneous
admissible SKM parameters Sc of the action notes. In particular, for distinct
colours, the algebra parameters Q of `parameterTwist Sc` satisfy

    Q_ij(u,0) = t_ij u^(-a_ij),       t_ij a unit,             (1)

and the corresponding statement in the other variable. Odd variables occur
only to even powers. Homogeneity with positive symmetrizers forces (1): with
v-exponent zero the weighted degree fixes the u-exponent uniquely. When
a_ij=0, Q is the single invertible constant, not a sum of two constants.
The parameter twist changes only signs and retains all these properties.
No assumption of finite type, simply-laced type or all-even parity is made.

Choose positive integers M_i and a dominant cutoff weight Lambda with

    N_i = 2 M_i  (i odd),       N_i = M_i  (i even).

If necessary use the pairing extension of `ProbeReachability.md`; do not
infer existence of this weight in the original lattice. The M_i may vary
by colour and may be chosen cofinally. Use the full ELV universal coefficient
ring A for these cutoffs, with its relations at even odd-colour cutoffs.
Define the parity-preserving coefficient map s:A -> k explicitly:

* At an odd colour, s(delta_i)=0 and
  s(chi_(i,r))=(-1)^r binom(M_i,r). Thus C_i(z) maps to (z-1)^M_i,
  and the ELV relation delta_i chi_(i,M_i)=0 maps to zero.
* At an even colour, send the coefficient of u^(M_i-r) to
  (-1)^r binom(M_i,r).
* On k and the fixed Q parameters use the identity.

Consequently the first-position relations become

    f_i(u)=(u^2-1)^M_i (i odd),    f_i(u)=(u-1)^M_i (i even). (2)

All coefficients are purely even. This is a specialization of the precise
ELV ring, not an unrestricted odd-coefficient deformation. In particular
inverting its even-cutoff constant coefficient would kill delta_i; retaining
that odd parameter in this probe is neither asserted nor needed.

For every content beta define

    B_beta = k tensor_A (R_A(beta)/(F_1))
           = R_k^(parameterTwist Sc)(beta)/(f_(nu_1)(x_1)e(nu)). (3)

The equality is the canonical presentation isomorphism: tensoring the
presentation imposes the specialized relations and their two-sided ideal.
No flatness is required. Put B_0=k and use zero for absent contents.

## 2. Finite generation, before any inverse assertion

The polynomials (2) belong to the purely even-coefficient KKO subfamily.
Use a purely even polynomial coefficient ring C over k, with independent
homogeneous coefficients for degree N_i at even colours and for a monic
polynomial in u^2 of degree M_i at odd colours. Over C the cyclotomic
algebra has monic dot annihilators at every position. This is KKO I,
arXiv:1206.5933v2, Lemma 7.3, in its homogeneous coefficient setting;
its proof uses Lemma 7.2 for equal colours and the monic leading Q term
for distinct colours. These statements and their proofs are read here
in that edition, Section 7.2. This invocation is within their even-coefficient
hypotheses, not an extension to arbitrary odd coefficients.

Combining these monic annihilators with the affine PBW spanning monomials
bounds every dot exponent; there are finitely many words and permutations
at fixed beta. Thus this algebra is a finite C-module. Specialize the
coefficients to (2). Its finite spanning set specializes to a finite
k-spanning set of B_beta. This proves finite generation, not freeness,
and requires no projectivity or flatness theorem. The earlier translated-KKO
freeness discussion in `CyclotomicDeformationProof.md` is stronger than what
is needed here. No freeness assertion for arbitrary exterior coefficients
is being used. Nothing in this step requires the specialization to preserve
the positive integer grading.

## 3. Propagation of dot invertibility over a field

First let k=K be a field of characteristic different from two. Fix beta of
height n and the finite-dimensional left regular module B_beta. On its
word summand V_nu=e(nu)B_beta, write x_r for left multiplication by the
r-th dot. These dots satisfy the algebra relations, before passage to the
signed-right action. Their squares commute with every dot and with each
other. Squares, rather than odd dots, are the commuting operators used below.

The constant coefficient of each f_i is a unit. The first-position relation
therefore gives a two-sided polynomial inverse to x_1 on each V_nu.
We prove by induction on r that x_r is invertible on every V_nu. This is
not an assertion that the first-position relation holds at position r.

Assume the result at r. For each word let

    W_nu = ker(x_(r+1)^(2d) : V_nu -> V_nu),

where d is large enough that this kernel stabilizes. The space W_nu is
preserved by both neighbouring dots, and by x_r^(-1), since they commute
with x_(r+1)^2. Put u=x_r, v=x_(r+1). On W_nu, u is invertible and v is
nilpotent. We show W_nu=0 separately in all three cases.

**Distinct colours i,j.** The crossing tau sends W_nu to the generalized
zero space for x_r^2 on V_(s_r nu), by the distinct-colour dot slides.
That space is zero by the induction hypothesis; hence tau W_nu=0.
But its square on V_nu is Q_ij(u,v). On W_nu this is a unit:
write Q_ij(u,v)=t_ij u^(-a_ij)+H. All monomials of H have positive
v-exponent. The permitted monomials lie in the commuting algebra generated
by u^(1+p(i)) and v^(1+p(j)), so

    (t_ij u^(-a_ij))^(-1) H

is nilpotent on W_nu. The finite geometric series gives the inverse of Q.
This includes the disconnected case H=0. Thus tau^2 cannot annihilate a
nonzero vector of W_nu, a contradiction. Notice the use of both the actual
Q admissibility and the nonzero/zero distinction; arbitrary Q would not do.

**Equal even colours.** Normalize T=-tau so that
Tu-vT=1=uT-Tv and T^2=0. Put phi=1+(v-u)T. The nilHecke identities give

    u phi=phi v,       v phi=phi u,       phi^2=1.           (4)

Thus phi maps W_nu to the zero generalized space of u^2, while being
injective. Again W_nu=0. Inverting tau itself here would be false.

**Equal odd colours.** Now T=tau, Tu+vT=1=uT+Tv, uv=-vu and T^2=0.
Put phi=(v-u)-(v^2-u^2)T. Then

    u phi=-phi v,      v phi=-phi u,      phi^2=u^2+v^2.     (5)

These are the polynomial identities `OddTwo.x_mul_phiOdd`,
`OddTwo.x_succ_mul_phiOdd`, `OddTwo.phiOdd_mul_phiOdd` in
`CyclotomicAction/Intertwiner.lean`; (4) is its `EvenTwo` counterpart.
The last equality in (5) uses uv+vu=0. No odd dot eigenvector is invoked.
The first two identities show that phi exchanges the two square operators.
It therefore kills W_nu, since u^2 is invertible. On W_nu its square
u^2+v^2 is invertible: u^2 is invertible, v^2 nilpotent, and they commute.
This forces W_nu=0.

Finite dimension now implies v is invertible on V_nu. This completes the
induction for every r, every word and every content. It does not assert
that every word summand is nonzero. No algebraic closure or splitting of
all joint spectra was used; the zero-primary kernel is defined over K.

For completeness, these operator inverses give algebra units. The global
position element X_r=sum_nu x_r e(nu) acts bijectively on the left regular
module. If X_r y=1, injectivity of left multiplication gives y X_r=1.
It commutes with word idempotents, so its inverse does too. Hence each
x_r e(nu) is a unit in its word corner. The inverse is homogeneous of the
same parity as the dot on that corner.

## 4. Descent to the stated base ring

Return to arbitrary nonzero k with 2 invertible. B_beta is finite over k
by Section 2. For any maximal ideal m, presentation base change identifies
B_beta tensor_k k/m with the same cyclotomic algebra for the residue datum;
leading coefficients remain units. Section 3 makes X_r a unit in this fibre.
The cokernels of L_(X_r) and R_(X_r) on B_beta are finite k-modules, and
right exact base change shows that their fibres vanish for every m.
They are zero: localize at m and apply Nakayama, then use vanishing at all
maximal localizations. Thus X_r has both a right and a left inverse in
B_beta, which coincide. The word-corner conclusion follows as above.
This descent is not a flatness argument and does not assume k is reduced.
The zero algebra causes no exception: its regular module is zero and all
stated inverse identities are identities with its zero unit.

## 5. Factor maps and preservation of the whole inverses

Apply the coefficient map s to the underlying superbimodule kernels of the
accepted deformed action, after forgetting their integer grading. At each
content the category is now all parity-graded left B_beta-modules. This is
not merely the subcategory of modules admitting a lifted integer grading.
The functors are the kernels

    E_i: B_(beta+alpha_i)e(beta,i) tensor_(B_beta) -,
    F_i: e(beta-alpha_i,i)B_beta tensor_(B_beta) -.

For composable kernels P,Q the explicit comparison is

    k tensor_A (P tensor_B Q)
      -> (k tensor_A P) tensor_(k tensor_A B) (k tensor_A Q),
    c tensor (p tensor q) |-> (c tensor p) tensor (1 tensor q).

Its inverse multiplies the scalar factors. These are even maps and respect
super balancing; all specialized scalars are even. Corner idempotents,
finite direct sums and parity shifts commute with this comparison. It is
coherent with reassociation by evaluation on pure tensors.

The unit remains tensor insertion and the counit remains multiplication.
The upward dot on a homogeneous kernel element z is

    D(z)=(-1)^(p(i)|z|) z x,
    D^(-1)(z)=(-1)^p(i) (-1)^(p(i)|z|) z x^(-1).            (6)

Indeed signed right multiplication by x followed by that by x^(-1)
is (-1)^p(i) times the identity. Thus both composites in (6) are the
identity, including the odd case. Distant odd dots are not required to
commute. Crossings remain R_tau for distinct colours and -R_tau for equal
colours, over `parameterTwist Sc` exactly as in the action assembly.
The corner inverses are ordinary-right linear with the same signed-left
linearity as the original dots, since an invertible homogeneous dot has
the same supercommutation with the old-strand image as its inverse.
Tensoring (6) with arbitrary modules gives inverse supernatural dot maps.
It also covers every strand of an iterated induction under the prescribed
multiplication contractions, not just the first or last strand of B_beta.

Let U_beta,i and V_beta,i be the FULL mutually inverse shifted matrices
from `DeformedMatrixComparison.md`, in either height regime, including
all identity summands. Define their specialized matrices by 1 tensor U
and 1 tensor V, under the comparisons just displayed. Then

    (1 tensor U)(1 tensor V)=1,    (1 tensor V)(1 tensor U)=1.

Their forward entries are precisely the specialized cup-crossing-cap mate
and dotted units/counits, since insertion, multiplication, signed dots,
crossings and their whiskerings commute with the comparison. Their inverse
entries are the specialized prescribed leftward crossings and distinguished
cups/caps, not a newly chosen abstract splitting. Both product identities
survive without exactness or flatness. The distinct-colour inverse maps
specialize in the same way. Entries outside the finite windows stay zero.
This supplies every local inverse at every content, including zero height.
All full-action presentation identities specialize as identities of kernel
maps, hence hold on every supermodule.

As in the action assembly, take products over contents with the same
weight -Lambda+beta, with zero at empty fibres. No root-independence
assumption is used. This constructs the full parity-supercategory factor
action, rather than only a `RouquierFamily` interface. It supplies the
invertible adjacent probe dots and whole local matrices required by the
conditional same-colour inversion and by `HomProbeMatrix.md`.

## 6. Nonzero scope and remaining obligations

The vacuum algebra is B_0=k, so its regular supermodule is nonzero.
For each chosen M_i>0 the one-strand algebra is k[u]/(f_i), free on
1,u,...,u^(N_i-1), and is nonzero as well. The odd generator has its stated
parity; its square is not set to zero by supercommutativity.
No claim is made that all higher blocks, all word idempotents, or every
external weight is nonzero. In particular the construction does not by
itself prove the A3 fused regular-vacuum identifications or reachability of
all content modules needed by a specified observation.

Since every dot is a unit already, universally adjoining its inverse does
not change these algebras or their kernels. This is why there is no separate
exact-localization/induction-commutation obligation in this construction.
The scalar specialization is not integer graded: positive-degree
coefficients have become nonzero constants. Only parity is retained for
this probe. The reservoir's independent bounded positive-grading arguments
must not be inferred from, or invalidated by, this probe specialization.

Remaining work: formalize the all-position unit proof and the specialized
full-action comparison; complete the coupled/fused action, normalized
bubble values and regular-word coordinate identifications required by A3.
The present argument neither constructs those comparisons nor proves
fusion, faithfulness, or nondegeneracy. Its action input is exactly the
accepted written deformed action under its admissibility hypotheses,
not an additional assumed localized action.