# Finite-quotient same-colour augmented inversion

**Status: proposed written assembly, conditional on the finite inverse
formulas of `ProbeWindowInverse.md`; not a Lean theorem.** The conclusion
is a two-sided inverse of the specified same-colour augmented mixed map
on the parity-completed, content-shifted Hom construction, at every pair
of heights, over each finite homogeneous reservoir coefficient quotient.
It is not a construction of a fused action. The leading inverse calculation
in `ProbeWindowInverse.md` is a separate proposed input, not an accepted
conclusion of this note.

## 1. Precise inputs and scope

Fix a colour i, reservoir content beta and its height k, probe height h,
and total height H=h-k. Work in the additive parity envelope; products
are functional order (rightmost map first). All matrices below are even
maps between the specified shifted sums. The symbol 1 denotes the identity
of the indicated object, not a scalar identification of different objects.

Use the following factor data.

1. The graded full-ELV reservoir action and normalized left adjunction of
   `DeformedGradedAction.md`, `SignedFTriangle.md` and
   `HomSectorTransport.md`, over the exact coefficient algebra of
   `DeformedReservoirBound.md`. In particular the purely even base field
   has 2 invertible, the Cartan symmetrizers are positive integers, the
   prescribed Q parameters and leading units are retained, and the
   weight realization and all cutoffs are specified. The even-cutoff
   relations between odd and top even coefficients are not discarded.
   Choose a homogeneous quotient by powers of the finitely many
   positive-degree even coefficient generators; keep the independent
   exterior generators and their relations. The resulting reservoir
   algebra at beta has upper integer-degree support M_beta. Reservoir
   dots on the finitely many adjacent edges used below are nilpotent.
2. A specified probe factor action, with its even right adjunction,
   literal same-colour mate, dotted windows and **whole** local inverse
   at every required content. Its relevant dots are invertible. For an
   odd dot, invertibility of its square suffices: x(x^2)^-1 is a two-sided
   inverse of x. The probe mate satisfies the literal slide
   `y s-q s x=u v`, q=(-1)^p, p=p(i). The action, adjunction and local
   inverse must exist on the chosen localized categories, not merely on
   an abstract algebra before localization. These are factor-action
   hypotheses, not consequences of the present matrix calculation.
3. The prescribed pre/postcomposition, z/xi comparisons, inherited dots,
   reversed reservoir crossing and probe crossing transport of
   `HomPrincipalMate.md` and `HomProbeMatrix.md`. Use the corrected cross
   diagonals of `CrossingNormalization.md`, with the swapping entries
   unchanged. The support and swapping inverse calculation is exactly
   `HomSwappingMates.md`. The finite residual coordinates and coefficient
   comparison are those of `HomResidualWindows.md`.
4. The finite algorithm of `ProbeWindowInverse.md`, including its shifted
   window formulas, six height subcases, extraction maps and old-index
   restoration, gives two-sided inverses of its explicit H_+,H_- tables.
   **This is the only additional proposed inverse calculation used here.**
   Its use is isolated in the definition of V below. We do not assume an
   inverse to a residual S or to a bare sector crossing.

For localization in item 2, a sufficient input is a system of probe
categories and edge functors on which the designated dots are units,
with the specified cup, cap, crossing and inverse-window maps descended
and all their identities preserved. Alternatively one may supply these
data directly on the localized categories. An arbitrary localization of
algebras does not by itself prove that restriction/induction, adjunctions
or their local inverses descend. No denominators in reservoir coefficients
are inverted. Same-colour cross denominators are obtained by finite
geometric sums from reservoir nilpotence and probe units; they require
no extra inversion of Q_ij. Distinct-colour inversion and braid comparisons
are outside this result. In particular this does not certify every
polynomial probe proposed in `NondegeneracyProof.md` at all contents.

## 2. The coefficient matrix ideal is jointly nilpotent

Use exactly the coefficient image algebra R of
`HomResidualWindows.md`: reservoir supercentral identity maps at beta,
and the closed probe words occurring in the residuals. Enlarge the probe
word set to include the finite compositions in the proposed table inverse,
its inverse dots and the coordinate changes used below. This enlargement
does not add open reservoir functors. All these probe words supercommute
with reservoir supercentral coefficients by enriched naturality and
horizontal interchange. Inverse dots have the same parity as dots; their
supercommutation follows by multiplying the dot commutation by its inverse.

Let Z_+ be the strictly positive integer-degree part of the reservoir
supercentre and J=R Z_+ R. Choose a positive integer n>M_beta. Any ordered
product of n homogeneous elements of Z_+ has degree at least n and is zero
in the reservoir algebra. In a product of n generators of J, move those
n positive factors together, retaining all Koszul signs. The remaining
reservoir supercentral and probe factors can be moved aside. Every term
vanishes. Thus J^n=0. This bound concerns **all** positive-degree
coefficients; the sharper bound 2dn>M_beta for the specific feedback
closures alone must not be substituted without a degree-divisibility
argument for all of J. If the reservoir algebra is zero, all maps on its
component are zero and the conclusions hold there as well.

More precisely use the finite collection of parity shifts of identity
appearing in a residual's source and target, with their specified z lifts.
For shifted sums U,V let J(U,V) be the matrices whose homogeneous
coefficients lie in J. Composition is matrix multiplication with the
actual shift transports. A product of n such matrices is a finite sum
over paths through summand labels. Adjacent shift comparisons cancel;
its coefficient is a sign times a product of n elements of J. Hence

    J(U_(n-1),U_n) ... J(U_0,U_1) = 0.

The collection J(-,-) is an ideal in this finite coefficient category,
and its endomorphism ideals have nilpotence exponent n, independent of
matrix size. No ordinary commutativity of R and no entrywise-nilpotence
shortcut is used. Parity completion here means adjoining shifts and
finite sums, not a topology or an infinite matrix completion. All these
identity windows return to the **same beta**; paths through window
labels do not change reservoir content. An open functor that changes
content cannot be inserted in this ideal argument.

This proves zero as a reservoir algebra element before it acts on any
Hom object. Arbitrary Hom spaces, probe modules and probe algebras need
not be finite-dimensional or integer-graded. No common exponent on an
infinite weight fiber is asserted.

## 3. A finite, ordered lift of the residual inverse

Keep the symbols of `HomResidualWindows.md` for each sign. Write
S:U->W for its exact residual, Htab for its explicit leading table, and
L,Q for its invertible finite window changes. They satisfy

    S = L Htab Q modulo J(U,W).

Htab and its inverse algorithm are finite probe words, not just
unlifted classes in a quotient. Define the following maps over the
original finite coefficient quotient, before reducing by J:

    V0 = Q^-1 Htab^-1 L^-1 : W -> U,
    eU = 1_U-V0 S,                 eV = 1_W-S V0,
    PU = sum_(a<n) eU^a,           PV = sum_(a<n) eV^a,
    V = PU V0 = V0 PV : W -> U.                              (1)

Here V denotes the inverse map.
The proposed table algorithm is used **only** to supply Htab^-1 and its
two products in the definition of V0. L and Q are the existing ordered
triangular changes; their inverses are already finite factor expressions.
Consequently eU and eV lie in the respective matrix ideals and their
nth powers are zero by section 2. The identity eU V0=V0 eV proves equality
of the two ordered formulas. Telescoping gives

    V S=PU(1-eU)=1_U,        S V=(1-eV)PV=1_W.              (2)

This supplies a typed two-sided inverse, including rectangular matrices
between differently labelled sums. It uses neither dimension cancellation
nor lifting of arbitrary quotient morphisms. Increasing n changes nothing
once both error powers vanish. Every product is ordered; odd coefficients
are not commuted to obtain (1).

## 4. Invert the exact central augmented map

To avoid the ambiguity in the letter V from now on denote the inverse (1)
by S_+^-1 or S_-^-1. Let X0,Y0,P0,N0, sigma0,u,v,I,a0,b0 be the specified
whole sector data:

    Phi=[sigma0,u; v,0]:X0+N0 -> Y0+P0,
    Phi^-1=[I,a0; b0,0].

In particular I:Y0->X0, a0:P0->X0 and b0:Y0->N0. These are not inverses
to bare crossings. Retain literally

    c(k)=(-1)^(p(k+1)) e(k), e(k)=1 (k<0), e(k)=q (k>=0),
    gamma(k)=q^k (k!=0), gamma(0)=q,
    I=diag(gamma f,j), K=Knew=-q [0,C;D,0].

All alpha/beta window scalars, reciprocal inverse scalars, and z/xi lifts
remain those in `HomResidualWindows.md`. In particular no gamma is erased
from an exact formula just because it disappears modulo J. Let

    A=1_Y0+K I, A^-1=[1+l E m,-l E; -E m,E],
    l=Cnew j, m=Dnew I_A, E=sum_(a<N) (m l)^a,
    B=1_X0+I K, B^-1=1-I A^-1 K.                         (3)

The closure bound of `HomCentralFeedback.md` supplies (m l)^N=0 at
this fixed content, for example with 2dN>M_beta. This is distinct from
the exponent n for the residual coefficient ideal. Both products for
A^-1 and B^-1 follow by ordered multiplication.

### H>=0

The central map is F_+=[sigma0+K;w]:X0->Y0+F, F=Fin(H), with the
**specified** fused cap row w, not an arbitrarily chosen window. Put

    D_+=[w I;b0]:Y0 -> F+N0, C_+=K a0:P0 -> Y0.

Then S_+=[w a0;0]-D_+ A^-1 C_+. For input (y,f) to F_+^-1 compute

    t=S_+^-1( (f,0_N0)-D_+ A^-1 y ),
    eta=A^-1(y-C_+ t),
    F_+^-1(y,f)=I eta+a0 t.                              (4)

Every occurrence of S_+^-1 means the finite algorithm (1), not a new
isomorphism hypothesis. Here is a two-sided check keeping the stabilization.
Start with F_+ directsum 1_N0 on X0+N0. On its output shear
(y,f,n0) to (y+u n0,f,n0), then precompose with Phi^-1. The matrix becomes

    [A,C_+; D_+,[w a0;0]]:Y0+P0 -> Y0+(F+N0).

Left multiply by [1,0;-D_+ A^-1,1], and right multiply by
[1,-A^-1 C_+;0,1]. The result is diag(A,S_+). The two shears have
inverses obtained by negating their off-diagonal entries. Thus the
stabilized map has an explicit two-sided inverse. Applying it to (y,f,0)
gives (4) and an auxiliary N0-coordinate zero, since its forward map has
last coordinate that same auxiliary input. Applying it after the forward
map on (x,0) returns (x,0). These two identities prove both products for
(4), without cancellation of an isomorphic summand.

### H<=0

Let G=Fin(-H) and use the specified cup column z:G->Y0. The central
map is F_-=[sigma0+K,z]:X0+G->Y0. Put

    C_-=[I z,a0]:G+P0 -> X0, D_-=b0 K:X0 -> N0,
    S_-=[b0 z,0]-D_- B^-1 C_-.

For input y to F_-^-1 compute

    (g,t)=S_-^-1( b0 y-D_- B^-1 I y ),
    x=B^-1( I y-C_-(g,t) ),
    F_-^-1(y)=(x,g).                                     (5)

Indeed stabilize F_- by 1_P0. Shear its input via
(x,g,t) -> (x,g,t+v x), then postcompose its output with Phi^-1.
The matrix is [B,C_-;D_-,[b0 z,0]]. The same two ordered elimination
shears, with B replacing A, give diag(B,S_-). Its inverse is two-sided.
For stabilized output (y,0), solving gives the x,g,t in (5). Undoing the
input shear gives auxiliary coordinate t+v x, which must be zero because
the original stabilized output has P0-coordinate zero. Thus (5) is a
right inverse; applying the stabilized inverse to the forward image of
(x,g,0) proves the left inverse as well.

At H=0 both formulas apply, with empty F,G, and give the same inverse
of sigma0+K by uniqueness of two-sided inverses. The residual P0->N0
is generally **not** empty: k=h>0 retains P_B->N_A, and k=h<0 retains
P_A->N_B. Only k=h=0 has both empty. The formulas also include k=0 or
h=0 separately. No equality of window cardinalities cancels a window.

## 5. Restore the swapping blocks and all coordinates

Let W_A,W_B be the two swapping mates, not the central sector maps.
The projection calculation in `HomSwappingMates.md` gives an exact block
decomposition of the full same-colour augmented map. After the canonical
even permutations of sum labels it is

    diag(F_sign,W_A,W_B).

Dotted cups/caps occur only in F_sign. There are no off-support entries
and hence no extra Schur correction from the swapping summands. Use the
unchanged inverses of that note. In its execution-order notation these are

    W_A^-1=alpha A_t;h_A^-1;A_s^-1,
    W_B^-1=-beta B_t;g_B^-1;h_B^-1;B_s^-1,

where its alpha,beta are the swapping scalars (not window indices), and
its g_B^-1 is the displayed finite inverse using the transposed probe dot.
Compose these with (4) or (5) and undo the same sum permutations and the
specified homogeneous sector/window comparisons. More explicitly, if
Dsrc,Dtar are those identifications and
Dtar Ffull Dsrc^-1=diag(F_sign,W_A,W_B), then

    Ffull^-1=Dsrc^-1 diag(F_sign^-1,W_A^-1,W_B^-1) Dtar.   (6)

Both products cancel adjacent comparisons and the three inverse pairs.
Thus (6) is an algorithm for the full **same-colour augmented map**,
not merely its leading residual or principal feedback.

## 6. Finite-quotient compatibility and the exact remaining gap

Take two homogeneous reservoir coefficient truncations with a quotient
map from the larger quotient to the smaller one. Fix the same content,
heights, factor prescriptions, probe localization, and parity comparisons.
Require their realized functors and all displayed kernel maps to commute
with this base change, including the adjunction and specified local
inverse. At the algebra/corner/balanced-kernel level these are the quotient
identifications of `DeformedReservoirBound.md`; tensoring the two inverse
identities preserves them without flatness. For a Hom realization one
must additionally have its specified base-change comparison intertwining
these maps. No assertion that scalar extension commutes with arbitrary
Hom spaces is used or deduced here.

Under these hypotheses the forward maps and all finite expressions
specialize. One may use the larger quotient's nilpotence bounds in the
smaller quotient, since the corresponding zero powers remain zero. If
the smaller quotient uses different adequate bounds, (2), (4)--(6) still
give the same map: two two-sided inverses of the same forward map agree.
This proves compatibility **between the given finite quotients**. It
neither constructs an inverse on an inverse-limit category nor proves
that the quotients jointly detect coefficients, PBW words or bubbles.
No inverse limit, completeness, flatness or faithful specialization is
silently inserted. Contentwise assembly, when the ambient product
category and maps are defined, uses componentwise natural inverses, not
one globally terminating series on an infinite weight fiber.

The exact discharged assertion, subject to section 1, is a two-sided
inverse of the same-colour augmented mixed map sought as
A2-b2 in `NondegeneracyProof.md` §5.4, on the parity-completed Hom
construction over each specified finite quotient, including its residual
identity windows. Its earlier bare 2-by-2 reduction
is not resurrected. The transport condition (TC) in
`FusedFeedbackComparison.md` §1 asks for more specific tensor coordinates:
its raw right-adjunction supported expressions and swapping comparisons,
and integer shifts if retaining a homogeneous precursor. The Hom notes
supply the needed parity-level component formulas and intrinsic **left**
closure support for this inverse; this assembly does not identify those
closures with the unmodified right-factor tensor closures of that TC.
It therefore does not announce literal full TC as proved.

Outstanding are a factor construction satisfying the localized hypotheses
where not already provided; validation of the proposed leading inverse;
the literal right-factor TC identification if that formulation is used;
coherent integer word shifts for graded fusion; all required mixed-colour
and three-strand crossing relations; distinct-colour action comparisons;
and truncation-compatible joint coefficient/PBW and bubble detection.
Even simultaneous resolution of this same-colour inversion and its
parity-level mate transport does not prove full fusion or nondegeneracy.
