# Integer grading of the deformed lowest-weight action

**Status: written grading proof, not a Lean implementation.** This upgrades
`DeformedActionAssembly.md` and `DeformedMixedBraid.md` from their underlying
supercategory action to the standard integer grading. It uses their prescribed
maps and all-height inverses, not a new Mackey splitting. The grading function
is `SKM.gdeg` in `SKM/Grading.lean`; `SKM/Basic.lean` specifies its boundaries.

Sources read: KKO I, arXiv:1206.5933v2, §4 (the convention
`(qM)_a=M_(a−1)`) and §8 (unshifted induction and restriction); KKO II,
arXiv:1303.1916v2, §8.3 and Theorem 8.13 (the cyclotomic kernels and shifted
inversion profiles); Brundan–Ellis, arXiv:1701.04133v2, §1, “Gradings”,
(1.31) and the following degree table. KKO's cyclotomic coefficient conditions
are narrower than full ELV. Their theorem is not invoked to extend those
conditions: the full-coefficient bijectivity input is the written proof in
`DeformedMatrixComparison.md`.

## 1. Hypotheses and grading conventions

Keep the hypotheses and coefficient ring A of `DeformedActionAssembly.md`:
finite compatible support, a symmetrizable Cartan superdatum, purely even
commutative k with 2 invertible, and prescribed homogeneous parameters with
invertible leading coefficients. Give k integer degree zero. Write

    h_i(λ)=⟨h_i,λ⟩, a_ij=⟨h_i,α_j⟩,
    b_ij=d_i a_ij=d_j a_ji, d_i>0, b_ii=2d_i.

Thus a dot has degree 2d_i and an affine crossing degree −b_ij. Require
`Scalars.Homogeneous`, equivalently every nonzero Q monomial u^r v^s has
2d_i r+2d_j s=−2b_ij. Start the algebra with `parameterTwist Sc` as in the
assembly, retaining its reverse-label quadratic comparison. This sign-only
parameter transport preserves homogeneity and degree-zero leading units.

For clarity distinguish the odd deformation parameter δ_i from d_i. Give
δ_i degree 2d_i, χ_(i,r) degree 4d_i r, and the coefficient of x^(N_i−r)
in an even-colour monic polynomial degree 2d_i r. These assignments make
both odd ELV formulas homogeneous of degree 2d_i N_i:

    N_i=2m>0: C(x²)−xδ_i(C(x²)−χ_(i,m))/x²,
    N_i=2m+1: (x−δ_i)C(x²).

The relation δ_iχ_(i,m)=0 in the even-cutoff case is homogeneous;
N_i=0 means f_i=1 and no δ_i. All nonconstant coefficient generators
have strictly positive integer degree. Their super parities remain those
of ELV; integer degree modulo two is NOT their parity. The quotient ideal
is integer homogeneous: even when the sum of the first-position relations
has components of different degrees, multiply by its word idempotents to
obtain the individual homogeneous generators. Thus each B_β is bigraded.

Use (q^r M)_a=M_(a−r), with no action twist and no parity change. For a raw
homogeneous map f:M→N of degree t, the same vector map

    q^u M → q^v N has degree t+v−u.                    (G1)

In particular M→q^r N has degree t+r; it is degree zero when r=−t.
Integer shifts introduce no Koszul signs. Parity shifts and their action
twists are exactly those already fixed in the assembly.

## 2. Shifted kernels and coherent right adjunction

At λ=−Λ+β take E_i1_λ to be unshifted induction and set

    f_i(λ)=d_i(h_i(λ)−1),
    F_i1_λ=q^(f_i(λ)) Res_i1_λ.                       (G2)

Here Res_i1_λ is the kernel e(β−α_i,i)B_β, with zero for an absent
predecessor. No shift of E is needed. For an edge from λ to λ+α_i the
restriction kernel has shift f_i(λ+α_i)=d_i(h_i(λ)+1).
Transport the original tensor unit and multiplication counit as the SAME
vector maps. Formula (G1) gives

    deg η_(i,λ)=f_i(λ+α_i)=d_i(1+h_i(λ)),
    deg ε_(i,λ)=−f_i(λ)=d_i(1−h_i(λ)).               (G3)

Their degrees on the same edge cancel:

    deg η_(i,λ)+deg ε_(i,λ+α_i)=0.                    (G4)

Both maps remain parity even. In each triangle the vector formulas are
still pe=p and eq=q. A graded right adjunction here means precisely these
homogeneous units/counits of opposite degrees on each edge, not an
adjunction with degree-zero unit to the normalized F. In the degree-zero
skeleton the right adjoint to E_i1_λ is q^(−f_i(λ+α_i))F_i1_(λ+α_i).
This distinction prevents imposing a false degree-zero condition at all
weights.

There is a canonical degree-zero identification
(q^u P)⊗(q^v Q)≅q^(u+v)(P⊗Q), sending a pure tensor to the same tensor.
It has no sign; multiplication and reassociation preserve total degree.
Consequently contractions of iterated induction, unit insertion, and
counit multiplication remain the assembly's maps under every associator.
The signed-left/ordinary-right conventions and all parity whiskering signs
are unchanged. Composites acquire only their final-target minus
initial-source shifts: all intermediate shifts telescope. Thus transporting
the unit–crossing–counit composite does not select a different mate.

## 3. Both mixed directions, including equal colours

Put M_ij=E_j Res_i1_λ and N_ij=Res_i E_j1_λ for the raw kernels. Their
normalized versions are

    M'_ij=q^(f_i(λ))M_ij,
    N'_ij=q^(f_i(λ+α_j))N_ij.

The assembly's mate s_ij:M_ij→N_ij has degree −b_ij. The decisive equation
for EVERY i,j and λ is

    f_i(λ+α_j)−f_i(λ)=d_i a_ij=b_ij.                (G5)

Hence deg(s'_ij)=−b_ij+b_ij=0. For i≠j its inverse has raw degree b_ij
and normalized degree b_ij−b_ij=0. Interchanging i and j uses
f_j(λ+α_i)−f_j(λ)=b_ji=b_ij, so the other mixed direction is covered
without an assumption of simply-laced data. For i=j, (G5) is the shift
difference 2d_i; the raw degree −2d_i again becomes zero. Here the
leftward crossing is the prescribed inverse MATRIX component, with its
existing parity/sign normalization, not an asserted inverse to s alone.
It has degree zero by the matrix calculation below.

Upward dots and crossings involve only unshifted induction kernels.
Multiplication contractions and signed right multipliers therefore give
degrees 2d_i and −b_ij directly. This includes the equal-colour minus sign,
which changes neither degree nor parity.

## 4. Homogeneous matrices and their inverse components

Fix i and h=h_i(λ); abbreviate M'=E_iF_i1_λ and N'=F_iE_i1_λ. These are
q^(d_i(h−1))M and q^(d_i(h+1))N in the notation of
`DeformedMatrixComparison.md`. Dotted units and counits have degrees

    c_k=d_i(h+1+2k),    u_k:1_λ→N',
    e_k=d_i(1−h+2k),    v_k:M'→1_λ.                  (G6)

Here e_k denotes an INTEGER degree, not the sign bearing the same letter
in the comparison note. Both maps have parity kp(i). The mate has parity
p(i) and degree zero. The degree-zero, parity-even matrix profiles are
therefore exactly

    h≤0: Π^p M' ⊕ ⨁_(0≤k<−h) Π^(kp)q^(c_k)1_λ → N',
    h>0: M' → Π^p N' ⊕ ⨁_(0≤k<h) Π^(kp)q^(−e_k)1_λ. (G7)

The maps use the canonical parity transports of the comparison note;
no parity involution is tensored as a bare bimodule endomorphism. For h≤0,
(G7) is its first KKO profile shifted by d_i(h+1). For h>0 it is its
second profile with the common Π^p q^(−2d_i) source shift removed and
then shifted by d_i(h−1). Thus both integer and parity profiles agree
with the concrete source matrices, not just with the dimensions of a
hypothetical splitting.

The all-height proof gives bijections of the underlying kernels. A bijective
homogeneous map of degree (0,0) between direct-sum bigraded modules has
homogeneous inverse: decompose the unique preimage of a homogeneous vector,
and injectivity forces every wrong-degree component to vanish. This applies
over arbitrary coefficient rings and to zero modules. Hence the inverse
components in (G7), after undoing the displayed shifts, have degrees

    lcross i i: 0,
    dcup i k: −e_k=d_i(h−1−2k)       (0≤k<h),
    dcap i k: −c_k=−d_i(h+1+2k)      (0≤k<−h).       (G8)

Their parities are p(i), kp(i), kp(i), respectively, as already established.
Tensoring these kernel isomorphisms with any module preserves their inverses
and degrees; no flatness or projectivity hypothesis is needed.

There is no hidden nonzero-degree pivot. In `DeformedBoundaryDivision.md`
§5, γ is a sign times the inverse of the product of leading Q coefficients,
with multiplicities specified by β. Those coefficients are units in k,
which is in integer degree zero. Consequently deg γ=deg γ⁻¹=0.
The monic division is homogeneous: its moving variable has degree 2d_i,
and the leading coefficient of γφ_k is 1, so φ_k, when nonzero, has total
degree 2d_i(a+k), where a=−h. This follows also termwise by homogeneous
monic division of F t^k by S; a coefficient at moving power l has degree
2d_i(a+k−l). The corrected w_k terms are homogeneous because δ_i has the
same degree as one dot. In the negative-a kernel window the entries
H_(r,k)=φ_(r+k+1)−φ_(r+k)t have degree 2d_i(a+r+k+1).
The antidiagonal r+k=−a−1 therefore has degree zero and entry γ⁻¹,
exactly as required. Parity involutions preserve integer degree. This
checks the unit-triangular argument against (G7), rather than treating
“central even unit” as sufficient to infer integer degree zero.

## 5. Generator table, boundaries, and scope

Every degree below is at rightmost region λ and h=h_i(λ).

| generator | integer degree | parity |
|---|---|---|
| dot i | 2d_i | p(i) |
| cross i j | −b_ij=d_i D.d i j | p(i)p(j) |
| cup i | d_i(1+h) | 0 |
| cap i | d_i(1−h) | 0 |
| lcross i j | 0 | p(i)p(j) |
| dcup i k | d_i(h−1−2k) | kp(i) |
| dcap i k | −d_i(h+1+2k) | kp(i) |

Assign dcup zero outside 0≤k<h and dcap zero outside 0≤k<−h. Zero is
homogeneous in the specified degree and parity. At h=0 the window is
empty, and the mate alone is the isomorphism. At content height zero,
absent-content kernels are zero, and the same matrices, triangles and
degree calculations apply; no nonexistent predecessor is silently added.
The N_i=0 relation may kill a corner, which is covered by the same convention.

When several contents give the same λ, use the assembly's product over
those contents. Formula (G2) depends only on λ, so it is compatible with
every component and reindexing β↦β±α_i. No injectivity of the root-to-weight
map is used. Empty fibers have the zero category.

All underlying presentation relations already hold by the assembly and
mixed-braid proof. Their maps are unchanged, and the table agrees with
`SKM.gdeg`. The relations are homogeneous (`isHomogeneous_gdeg` records
this for the presentation). Thus the same generator assignment defines a
written integer-graded action on the graded all-module tensor target.
Integer shifts neither alter the accepted mixed quadratic/braid signs nor
remove any odd deformation coefficient. The graded target has homogeneous
natural transformations with finite sums of bidegrees, and degree-zero
tensor associators; it is not obtained by identifying parity with degree.

For a subsequent Hom degree-window argument, this supplies the standard
integer degrees and positive degrees of the deformation generators, which
must be retained under Hom/precomposition transport. It does not establish
boundedness or local finiteness of Hom spaces of arbitrary modules, a fused
action, a degree-window detection estimate, a left adjunction, normalized
bubble coordinates, or nondegeneracy. Those are separate obligations.
