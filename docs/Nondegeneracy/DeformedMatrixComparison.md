# Tensor-adjunction comparison of the same-colour matrix

**Status: proposed written tensor calculation, not a Lean theorem or a full
action.** It identifies the specified maps, rather than a freely chosen
splitting. Invertibility additionally depends on the norm/division argument
in `DeformedBoundaryDivision.md`, which remains under review. The first-order
boundary argument is a separate input; its acceptance does not settle division.

Sources: KKO I, arXiv:1206.5933v2, Proposition 9.3, (9.9)–(9.12), and
**Theorem** 9.6; KKO II, arXiv:1303.1916v2, §8.3 and Theorem 8.13.
The latter states the shifted isomorphisms, not the full-ELV extension.
The explicit EX rows below use the recurrence and kernel-window argument
of `DeformedRouquierMatrix.md`, rather than attributing a displayed matrix
with those rows to the statement of Theorem 8.13.

## 1. Fixed kernels and conventions

Let A be the full ELV coefficient superalgebra of
`DeformedSquareResolution.md`, over a purely even ground ring with 2
invertible. Retain the compatible symmetrizable datum, homogeneous parameters
and their leading units, and every odd coefficient relation. Set

    B=R_A^Λ(β), D=R_A^Λ(β−α_i), C=R_A^Λ(β+α_i), p=p(i),
    M=B e(β−α_i,i) ⊗_D e(β−α_i,i) B,
    N=e(β,i) C e(β,i), a=⟨h_i,Λ−β⟩, h=−a.

Zero corners are allowed. Write φ(z)=(-1)^|z|z on homogeneous elements,
including coefficients. All tensor factors below are homogeneous when a
sign is written; extend by addition. Products include the corner embeddings.
Our E is induction and F restriction, opposite to KKO's letters. With
left-to-right functor composition, M is F₁ ≫ E₁ and N is E₂ ≫ F₂.

Use the signed-left, ordinary-right superbimodule convention of the existing
`CyclotomicAction/SuperDot.lean` and `SuperCrossing.lean`. On an induction
corner the dot is D_x(z)=(-1)^(p|z|)zx; the equal-colour crossing is
T(z)=-(-1)^(p|z|)zτ. The extra minus is the prescribed
`globalActionSignedCross` in `GlobalRouquierData.lean`, not a gauge choice.
`GlobalHeightAdjunction.lean` defines the even tensor unit by insertion of
the corner identity and the even counit by multiplication. These are the
maps used here, with the ordinary balanced-tensor associators.

This is an algebraic calculation for those actual kernels and maps. It
assumes neither presentation relations for a completed action nor a matrix
comparison. The currently implemented `globalRouquierData` has coefficients
`a : I → Polynomial k` with `CyclotomicPolynomialParity`; it is not the
full-ELV super-coefficient tower. The calculation does not identify these two
coefficient categories.

## 2. Evaluate the prescribed three entries

Put d_k=(-1)^(p k(k−1)/2). Iterating the signed right multiplier, in the
vertical order of `rouquierPower`, gives

    D_x^k(z)=d_k (-1)^(kp|z|) z x^k.                 (1)

Indeed the next application adds p(|z|+kp) to the exponent. In particular
a pair of odd dots contributes a minus: D_x²(z)=-zx² when p=1.
This is the super-opposite composition sign, not an optional normalization.

Let s be `rouquierMate` of these unit, counit and T, and let u_k,c_k
be the dotted unit and counit in `SuperRouquierLoc`. Their kernel formulas are

    s(a₀⊗b₀)=-(-1)^(p|a₀|) a₀ τ b₀,
    u_k(b₀)=d_k x_(n+1)^k b₀,
    c_k(a₀⊗b₀)=d_k (-1)^(kp|a₀|) a₀ x_n^k b₀.     (2)

For the mate, insertion first produces the outer induction identity; the
two induction factors multiply to a₀. T contributes exactly the first sign
in (2). The counit then multiplies b₀ on the right. Neither even structural
map contributes another sign. For the cup, evaluate the dot power on the
inserted identity and then multiply the coefficient on the right. For the
cap, evaluate the dot on the outer induction factor a₀, then multiply b₀.
No permutation of a₀ and b₀ occurs. Applying these calculations with a final
module tensor factor gives the same transformations on every module; the
only additional whiskering signs are the standard tensor signs. In
particular the coefficient b₀ is not moved through an odd dot for free.

## 3. The canonical shifted coordinate, and the cap correction

KKO's crossing source is

    M♯=B e ⊗_D Π^p(e B), with the additional q_i^(−2) shift.

The left D-action on π^p b is π^p φ^p(c)b; its right B-action is unchanged.
The canonical shift-through-tensor map, on underlying vectors, is

    J(a₀⊗b₀)=(-1)^(p|a₀|) a₀⊗π^p b₀.             (3)

It has parity p and is right B-linear and signed left B-linear. Balance
is explicit: replacing a₀ by a₀c contributes (-1)^(p|c|), while moving
c across π^p contributes the same sign; they cancel. Its inverse has the
same sign. This is the canonical parity transport, not a basis isomorphism.

Use the source formulas, with φ on all coefficients,

    F̄(a₀⊗π^p b₀)=a₀τb₀,
    E(a₀⊗π^p b₀)=a₀φ^p(b₀),
    X(a₀⊗π^p b₀)=(-1)^p a₀x_n⊗π^p φ^p(b₀),
    j_k(b₀)=x_(n+1)^k b₀.

They immediately give the first two comparisons

    s=−F̄ J,                  u_k=d_k j_k.          (4)

For the rows, set e_k=(-1)^(p k(k+1)/2). The exact comparison is

    c_k=e_k φ_B^(p(k+1)) E X^k J.                   (5)

Here φ_B is the parity involution of the output B, not multiplication by
a scalar and not an ordinary B-bimodule endomorphism. It is the canonical
identification with the parity-twisted output actions. Omitting it is wrong
already at k=0: E J(a₀⊗b₀)=(-1)^(p(|a₀|+|b₀|))a₀b₀, whereas c₀ is
ordinary multiplication.

For verification, before applying φ_B the right side without e_k is

    E X^k J(a₀⊗b₀)
      =(-1)^(p|a₀|+pk) a₀ x_n^k φ^(p(k+1))(b₀).

Applying φ_B^(p(k+1)) cancels the b₀ sign and leaves
(-1)^(kp|a₀|+pk) a₀x_n^k b₀. Multiplication by e_k gives (2), since
k(k+1)/2+k and k(k−1)/2 differ by 2k. These equalities also prove descent:
E and X are well defined after cyclotomic quotient (multiplication and the
homogeneous dot preserve its two-sided ideal); alternatively (5), with
invertible J and φ_B, identifies each EX^k with the already descended cap.
No trace, reverse adjunction or left-adjoint triangle is used.

The right semilinearity of EX^k is φ^(p(k+1)); φ_B in (5) cancels precisely
that semilinearity. Thus one must transport the actions along with the
parity coordinates. Tensoring the naked map φ_B with an arbitrary module
as though it were B-linear is invalid. After (5), the result is the actual
signed-left, ordinary-right cap kernel, which can be tensored normally.

## 4. Matrices, shifts and the remaining assertion

Write K_−=[F̄,j_0,…,j_(a−1)] for a≥0 and
K_+=[F̄;E;EX;…;EX^(−a−1)] for a<0. In the underlying canonical
coordinates the prescribed matrices are exactly

    h≤0: R_−=K_− diag(−J,d_0,…,d_(−h−1)),
    h>0: R_+=diag(−1,(e_k φ_B^(p(k+1)))_(k<h)) K_+ J.  (6)

Every coordinate change is specified and invertible. No triangular
change of dotted generators or correction X−2d_i is needed here: X in
(5) is the source contraction operator, not the moving boundary operator ρ.
The deformed coefficient correction belongs to the boundary lifts, not to
this fixed induction dot.

Keep the source's integer and parity shifts:

    a≥0: Π^p q_i^(−2) M ⊕ ⨁_(k<a) Π^(kp) q_i^(2k) B → N,
    a<0: Π^p q_i^(−2) M → N ⊕ ⨁_(k<−a) Π^((k+1)p) q_i^(−2k−2) B.

In the second line removing the common source shift gives the profile
M → Π^p q_i^2 N ⊕ ⨁ Π^(kp) q_i^(−2k) B. Thus both matrices have
crossing parity p and identity-entry parity kp, exactly the profiles of
`SuperSumInvFrom` and `SuperSumInvTo`. The displayed q-shifts are retained
here; `SuperRouquierLoc` itself forgets the integer grading, not Π. The
parity involutions in (6) implement the action twists in these shifts;
they are not additional unrecorded parity summands.

Consequently a verified bijectivity proof for these K matrices gives
bijectivity of the prescribed R matrices, and their even shifted
superbimodule inverses give natural inverses after tensoring. For full ELV
coefficients this remains conditional on the specified exact boundary and
norm/division calculation, particularly its kernel window and EX pivot
calculation. Right projectivity is a written input, not a Lean theorem;
this note proves no opposite-side projectivity or reverse adjunction.

The next formalization target is the descended source map
B e ⊗_D Π^p(e B) → e C e, a₀⊗π^p b₀ ↦ a₀τb₀,
together with J and (4)–(5), on the full-ELV graded balanced kernels.
Construct the coefficient-superalgebra module category and its induction,
restriction, dot, crossing, unit and counit there before claiming that
`globalRouquierData` realizes this extension. Even-polynomial Lean data,
this written comparison, pending division, and a full action are distinct
assertions; none supplies the remaining braid, nilpotence or fusion work.
