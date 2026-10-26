# The deformed Rouquier matrix and its polynomial boundary

**Status: proposed matrix-level reduction, not an action theorem or a Lean
result.** The missing input is a deformed Mackey boundary calculation and its
comparison with the prescribed tensor adjunction, not an abstract decomposition
of functors. The negative-height argument below identifies an explicit unit
pivot matrix. It is conditional on the stated boundary identities.

## 1. Source, coefficients, and orientation

The sources are KKO II, arXiv:1303.1916v2, §8.3 and Theorem 8.13, and KKO I,
arXiv:1206.5933v2, §9, diagram (9.5), Proposition 9.3, equations (9.9)–(9.12),
Lemma 9.5 and Theorem 9.6 (pp. 48–54). KKO II recalls the construction; the
polynomial boundary and its maps are in KKO I. Neither source states the
multicolour full-ELV extension used here.

Use the coefficient superalgebra A and f_j of
`DeformedProjectiveResolution.md`: at odd colour and N=2m>0 it has
`d_j χ_(j,m)=0` and `f_j=C_j(x²)−xd_j q_j(x²)`; at N=2m+1 it has
`f_j=(x−d_j)C_j(x²)` without that coefficient relation. Tensor the different
colour factors superly, retaining products of different d_j. The purely even
ground ring has 2 invertible, the datum is compatible and symmetrizable, and
the homogeneous KKO parameters have the required unit leading coefficients.
No fraction field or flatness over the exterior algebra is used.

Put B=R_A^Λ(β), D=R_A^Λ(β−α_i), C=R_A^Λ(β+α_i), and p=p(i).
An absent β−α_i means the corresponding corner is zero. Write

    M=B e(β−α_i,i) ⊗_D e(β−α_i,i) B,
    N=e(β,i) C e(β,i),
    a=⟨h_i,Λ−β⟩,                 h=−a.

KKO's E is restriction and F is induction. In the intended lowest-weight
convention, E is induction, F restriction, and λ=−Λ+β. Composition in
`RouquierData.lean` is left-to-right. Thus M is `F₁ ≫ E₁` and N is
`E₂ ≫ F₂` at the middle block. KKO's positive a is the **negative** h
case of `SuperRouquierLoc`.

These are tensor kernels, not Hom kernels requiring a chosen trace. The
induction–restriction unit inserts the corner identity; its counit multiplies
the two adjacent factors. This adjunction exists on all modules without a
Frobenius hypothesis. Restricting the appropriate functors to projectives
requires projectivity of the relevant restriction kernels on the appropriate
side. The proposed right-projectivity resolution alone does not prove the
opposite-side assertion, a reverse adjunction, or `LeftZigzags`.

## 2. Which matrix has to invert?

Fix the actual even units η and counits ε, the prescribed induction dot x,
and the same-colour crossing t of the upward presentation. Let

    s = rouquierMate(η,ε,t) : M → N,
    c_r = (F₁ ◁ x₁^r) ≫ ε₁ : M → B,
    u_r = η₂ ≫ (x₂^r ▷ F₂) : B → N.

The powers are vertical powers, not powers of a rotated dot. The mate is
exactly the ordered insertion of η₂, then t on the two induction strands,
then ε₁, with the associators in `SKM.rouquierMate`. Its parity is p;
`c_r` and `u_r` have parity rp. The required maps are precisely

    h≥0:  [s ; c_0 ; … ; c_(h−1)] : M → N ⊕ B^h,
    h≤0:  [s, u_0, …, u_(−h−1)] : M ⊕ B^(−h) → N.       (R)

Each summand carries the parity shift of its entry when the map is viewed
in the even category. These are `invPos` and `invNeg` in
`OddMath/SKM/RouquierData.lean`, not a new action interface. At h=0 they
both require invertibility of s.

Here is the source matrix before translating conventions. Set
`M♯=Π_i q_i^(−2) M`. KKO's crossing map is the descent of

    F(a₀⊗π_i b₀)=a₀ τ_n⊗b₀.

The polynomial inclusion is `j(t^r b₀)=x_(n+1)^r⊗b₀`. On the affine
crossing summand define the source contraction and dot operator

    E(a₀⊗π_i b₀)=a₀ φ^p(b₀),
    X(a₀⊗π_i b₀)=(−1)^p a₀ x_n⊗π_i φ^p(b₀).           (C)

Here φ is total parity, including coefficients. KKO I (9.9) is the identity
`F(z)t_i=F(Xz)+j(Ez)`. The source choices in Theorem 9.6 are

    a≥0:  [F̄,j(1),…,j(t^(a−1))] : M♯ ⊕ ⨁_(r<a) Π_i^r q_i^(2r)B → N,
    a<0:  [F̄ ; E ; EX ; … ; EX^(−a−1)] : M♯ →
                 N ⊕ ⨁_(r<−a) Π_i^(r+1) q_i^(−2r−2)B.       (K)

The rows in the second line must descend to the cyclotomic M♯; this is
part of the comparison, not permission to apply an arbitrary map to a
quotient. The displayed Π and q shifts are exactly the source shifts.
Removing the common source Π_i changes the row parities from (r+1)p to
rp, as required in (R). The ungraded `SuperRouquierLoc` records parity,
not the integer q-grading; forgetting q is not forgetting Π.

The even reference `CyclotomicAction/KangKashiwara.lean` transports
`ConcreteAdjunction.loc` using separate `unit_compat`, `counit_compat`,
`dot_compat`, and `cross_compat` from `Comparison.lean`; its crossing is
`sameCross = −ψ`, not ψ. KKO II §8.3 puts induction's signed right
multipliers in a super-opposite endomorphism algebra. Consequently (K)
is **not yet literally (R)** merely by interchanging the letters E,F.
One must evaluate the fixed tensor unit/counit and signed crossing on
homogeneous simple tensors, and prove that under the Π-identifications:

* F̄ is the mate s with its specified scalar/sign normalization;
* j(t^r) is u_r with its specified dot normalization;
* the rows EX^r, after the deformed dot conversion below, are c_r.

A fixed unit scalar on the crossing and invertible triangular operations on
the dot window preserve invertibility. An unspecified bimodule automorphism
does not identify the prescribed action. In particular this document does
not assert these three comparison equations already hold in Lean.

## 3. The boundary map supplied by the resolution

In KKO I (9.5), L₀ is the e(β,i)-corner of K₀ and L₁ the same corner
of K₁. Their column decompositions have crossing submodules L₀′,L₁′
and polynomial quotients V₀,V₁. Write C₀:L₀→V₀ for the PBW polynomial
projection and B₁:L₁→V₁ for longest-crossing coefficient extraction.
The proposed deformed square-resolution proves neither column diagram
merely by proving K₁→K₀ injective. The additional requirement is

    C₀ P = A_∂ B₁,                                  (B)

with the top quotient equal to M♯ and middle quotient equal to N.
All modules here retain the old algebra actions and KKO's shifts
`Π_i^(N_i+p(β))`, `T_i^N_i`. Once this diagram is exact, its snake map gives

    0 → ker A_∂ → M♯ → N → coker A_∂ → 0.             (S)

Use a polynomial basis v_k of V₁ and put φ_k=A_∂(v_k). The source proof
requires the following strengthened polynomial conclusion, not just QP:

    φ_k=0 for a+k<0;
    γ φ_k=t^(a+k)+terms of smaller t-degree for a+k≥0, (L)

where γ is one fixed central even unit, the inverse leading coefficient
specified in KKO I (9.6). A possible semilinear coefficient identification
must be included in v_k, not silently suppressed. KKO obtains (L) by
Lemma 9.5: divide the ordered norm expression by the monic product

    S_i=Σ_ν ∏_(ν_b=i)(t^(1+p)−x_b^(1+p))² e(ν).

The QP repeated-odd factor is `t²+x_b²`; it is **not** S_i and it is
not the square of g. The proof uses both the longest-crossing extraction
and the first-order defect of A_∂. These are extra information beyond the
norm identity and a B[t²]-projective resolution.

## 4. Inversion after the boundary identities: no flatness needed

Here is the matrix argument over B itself, allowing zero divisors.
Assume the exact diagram, (L), and the source recurrence, in its correctly
translated coordinate,

    ψ_(k+1)=Xψ_k,       φ_(k+1)=Eψ_k+φ_k t,
    P(z_k)=F(ψ_k)+j(φ_k),       B₁(z_k)=v_k.           (D)

For a≥0, the leading terms in (L) make A_∂ injective: a nonzero finite
sum of v_k b_k has a largest index, whose leading coefficient is a unit
times b_k. Polynomial elimination gives a unique representative of degree
<a in its cokernel. The prescribed j(t^r), 0≤r<a, lift these representatives
in N. Thus the first matrix (K) is bijective, not merely an unspecified
splitting of (S). Its inverse first extracts the polynomial remainder and
then uses the unique preimage under F̄ of the residual element.

For a=−m<0, (L) gives a surjective A_∂ and
`ker A_∂=⊕_(k<m) v_k B`: the images with k≥m have distinct leading
terms and span V₀ by elimination. The snake injection sends v_k to the
class κ_k of ψ_k (choose this common sign for the snake map). Evaluate
the cap rows on this **specified** kernel basis:

    H_(r,k)=EX^r ψ_k=Eψ_(r+k)=φ_(r+k+1)−φ_(r+k)t.

It follows that

    H_(r,k)=0 if r+k<m−1,
    H_(r,k)=γ^(−1) if r+k=m−1.                       (T)

Reverse the kernel columns. This is triangular with diagonal γ^(−1),
so multiplication by γ gives diagonal one. The remaining triangular part
is strictly triangular of size m, hence nilpotent; its inverse is the
finite geometric sum, with factor order retained. No determinant,
commutative B, field, or B-freeness over A is necessary.

This proves the second matrix (K) invertible: for a desired (n,b), choose
any lift z of n through F̄, then add the unique element of ker F̄ whose
cap vector is b−(EX^r z)_r. The result is independent of the chosen lift.
Its bijectivity and the bimodule property of the specified matrix give a
bimodule inverse. This is the missing matrix-level content of an abstract
kernel/cokernel splitting. At a=0 there is no remainder window and (S)
identifies F̄ as an isomorphism.

## 5. First deformed step and the precise remaining local identity

There is a useful refinement of the square-resolution at an odd moving
colour. Put η=p(i)p(β), r=p(i)N_i (so here p(i)=1), and ε=η+r.
Use its tensor coordinates K₁=H e(i,β)⊗_R Π^ε B, with unchanged right
B-action. Define the corrected moving operator

    ρ(h₀⊗π^ε b)=
       (−1)^η h₀ (x₁+2(−1)^r d_i)⊗π^ε φ(b).        (U)

This has the same balance check as the usual moving dot: both x₁ and d_i
supercommute with homogeneous old elements; φ acts on all of B. It is
therefore well defined on the balanced module. The relation
`x₁ f_i=f_i(x₁−2d_i)` and `d_i f_i=(−1)^r f_i d_i` give

    (x₁+2(−1)^r d_i) f_i = f_i x₁.

The moving-dot slide through T, modulo the old cyclotomic submodule,
then proves the exact intertwining law

    P(ρz)=(Pz)t_i,             ρ²z=z s, s=t_i².       (U1)

Indeed both sides of the first equality are
`(−1)^η h₀ f_i(x₁)x₁ T⊗φ(b)`; omitted-crossing terms lie in the old
ideal by the P-balance argument. The second uses d_i²=0 and
x₁d_i=−d_i x₁. Thus the corrected unsquared operator is available before
any cyclotomic freeness assertion. It uses +2d_i at even cutoff and
−2d_i at odd cutoff; copying one sign into both cases is wrong.

What remains is to transport (U) through **both columns of (9.5)**,
not just to square it. Precisely, show that ρ preserves L₁′, identify its
induced operator ρ̄ on V₁ by longest-crossing extraction, and prove (B)
and the polynomial defect identity

    A_∂(ρ̄ v)−A_∂(v)t_i = E ψ(v)                   (U2)

where a chosen PBW lift z of v satisfies
`Pz=Fψ(v)+j(A_∂v)`. With ρ-compatible lifts, (U1) and the affine
identity `F(z)t_i=F(Xz)+j(Ez)` force (U2) and the corresponding ψ
recurrence. But identifying ρ̄, its ordered polynomial basis, and its
interaction with S_i is necessary before importing Lemma 9.5's degree
bound. Square-linearity alone gives no first-order degree bound.

For the even-cutoff odd cap coordinate used in `ActionReview.md`, the
conversion Y=X−2D, with XD=−DX, D²=0 and ED=−R_d E, gives

    EY^(2b)=EX^(2b),
    EY^(2b+1)=EX^(2b+1)+2R_d EX^(2b).

This is a homogeneous row operation with square-zero off-diagonal part,
hence inverse obtained by changing its sign. It cannot supply (U2) or
(L); it only changes coordinates after those statements are proved.
Odd cutoffs must retain their coefficient parity twist as well.

Thus the precise outstanding calculation is the descended, coefficient-
sensitive first-order boundary (U2), its monic division identity (L),
and the tensor comparison in §2. There is no demonstrated need for a new
Frobenius trace to perform this matrix inversion on all modules. A reverse
adjunction or restriction to projectives still needs its own side-specific
hypotheses. No nilpotent lifting is invoked: that alternative would require
Tor-vanishing for the target convolution kernel and comparison of its
base-change maps. The quotient A/(d_j) still has even polynomial parameters
and is not a field.

For distinct colours the applicable source is KKO I Theorem 9.1, proved
from Proposition 5.1 and the ideal equality (9.3): its extra double-crossing
term has equal endpoint colours and vanishes in a mixed corner. This is a
crossing-map statement after quotient, subject to the same tensor-mate
comparison, not an additional same-colour polynomial division problem.
