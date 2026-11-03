# Swapped Hom vacuum and bounded signed-corner recovery

**Status: proposed written construction, not a Lean theorem.** The local
coordinate construction below uses the existing left-module reservoir
realization, not a replacement factor action. It is conditional on assembling
the specified swapped Hom action with its unchanged all-reservoir upward
blocks. In particular it does not prove the swapped augmented inversion,
normalized bubbles, or nondegeneracy. The affine presentation and ideal
calculations below are written arguments; their Lean implementation remains
open.

The useful target is `ReservoirVacuumEvaluation.affine_coordinates`, not a
global isomorphism with the first-boundary quotient and not necessarily
`RegularVacuumIdentification`. Bounded extraction permits precisely the
opposite/word-reversed coordinates produced by the actual signed multipliers.
No coefficient involution is needed for this route.

## 1. Literal external weight and support

Fix the original weight μ. Apply `exists_extended_weights D (-μ) m`, in
`ReservoirWeights`, and call its dominant weights ΛP and ΛR. In the actual
pairing extension X × (I → ℤ), not merely on coroot coordinates, they satisfy

    ΛR - ΛP = (-μ,0),       ΛP - ΛR = (μ,0).

Use the same normalized Hom construction with T the invertible-dot probe
and W the nilpotent reservoir. Their lowest-weight towers have labels

    T(-ΛP + βP),      W(-ΛR + βR).

The content-zero Hom sector has `(muP,muM)=(ΛP,-ΛR)`, since
`homWeightSector T W muP muM = Hom(T(-muP),W(muM))`. Its total weight is
exactly `(μ,0)`. The schedule is

    h(i) = -D.h i μ,
    P_i = probeLevel h m i,       N_i = reservoirLevel h m i.

The probe levels are even; the reservoir parity is unchanged by negating h;
both schedules are cofinal. No Chevalley involution or E/F exchange is
required for this weight choice. `FusedRegularVacuumFamily (μ) (h)` accepts
arbitrary h: its definition does not require h(i)=D.h i μ. The weight-sign
objection to this swap in `ELVVacuumTransport.md` §4 therefore does not apply
with this choice of dominant weights.

Retain formal contents independently of their root images. Let A be the
reservoir coefficient algebra, including the exact ELV coefficient relations,
and let its height-zero regular left module be A. The probe height-zero
algebra is k. On the content-indexed product categories define a k-linear
superfunctor V by

    V(M)_0 = A ⊗_k M_0,       V(M)_β = 0 for β ≠ 0.

On a homogeneous input map u of parity r, V(u)(a⊗v)=(-1)^(r|a|)a⊗u(v).
This is the ordinary super extension-of-scalars functor on the zero component,
followed by extension by zero. Projection is onto formal content zero, not
onto a numerical weight space. It is defined even when positive contents
have root image zero. With a common coefficient base, replace the displayed
k-tensor by extension over that base; do not duplicate A.

For every nonnegative probe content β and colour i,

    e_0 B_i^probe e_β = 0,

because induction has output content β+α_i in the free content monoid.
Thus pre(E_T)(V)=0. More generally every expanded upward word containing
a probe/precomposition letter is zero: reservoir postcomposition does not
change input support and the sum of the probe contents remains positive.
The parity shifts do not change zero objects. On the sole surviving term
βP=0, so `homContentShift i βP=0`; the postcomposition shifts are trivial.
The surviving word is reservoir induction on A. This statement uses only
upward blocks. It supplies no inverse matrix for the swapped full action.

## 2. Actual word values, including the reversal

Put S=`parameterTwist D Sc`. The reservoir algebra before its cyclotomic
quotient is the coefficient-extended affine matrix algebra for S. Matrix
multiplication is right-factor-first composition (`Hn.single_mul_single`).
Write B_β for its quotient by the first-position factor polynomial and the
coefficient relations. Optional finite coefficient truncations are treated
in §6. Work with locally unital algebras; all elements have finite support.

For the literal source word t=[i₁,…,iₙ], define ν(t)=reverse(t). Source
E_i E_j means E_i applied after E_j, hence the appended algebra tuple is
[j,i], not [i,j]. Iterated multiplication of the existing induction kernels
has the explicit form

    B_γ e(β,i) ⊗_(B_β) B_β e_ν  → B_γ e_(ν,i),
    b ⊗ c ↦ b append_i(c),
    z ↦ z ⊗ e_ν.

The inverse is balanced: `(b append_i(c))⊗e_ν=b⊗c`; multiplication back
uses the right corner identity. These maps are even. No crossing, coefficient,
or module factor is interchanged. This is the calculation of
`InductionComposition.compositionCornerLinear` and its insertion inverse;
the same formulas descend for the full-ELV quotients since append carries
old first-boundary relations to the new ideal. It does not require flatness.

Consequently the actual surviving word functor is

    V_t(M) = (B_(content(t)) e_ν(t)) ⊗_k M_0.

The contraction sends the original dot to signed right multiplication
R_x(z)=(-1)^(|x||z|)zx, and a crossing to ε_ij R_τ, where ε_ii=-1 and
ε_ij=1 for i≠j. This follows on each pure induction tensor from the
super tensor formula: moving the local multiplier past the inner factors
contributes its parity times their total parity, giving the displayed sign
on the contracted product. For successive homogeneous multipliers b₁,…,b_l,

    R_(b_l)…R_(b₁)(z)
      = (-1)^((Σ|b_j|)|z| + Σ_(j<k)|b_j||b_k|) z b₁…b_l.       (1)

This is the existing factor convention, including the equal-colour minus.
At βP=0, the all-reservoir Hom dot and crossing have these same components;
this last identification is conditional on the assembled swapped action
retaining the specified same-sector blocks, not on faithfulness of that action.

## 3. Signed left-module Hom coordinates, not assumed regularity

For each t let P_t=B e_ν(t). For homogeneous φ:P_s→P_t of parity r,
signed left-linearity gives

    b=φ(e_ν(s)) ∈ e_ν(s) B e_ν(t),
    φ(z)=(-1)^(r|z|) z b.                                     (2)

Conversely the second formula defines a signed left-module map from every
homogeneous b in that corner. Evaluation and this formula are inverse:
use e_ν(s)z=z for the corner value and z e_ν(s)=z for the input left ideal.
Thus these are actual Hom coordinates, including nonzero/zero corners;
no action-faithfulness assertion has been used. If φ_b has parity r and
φ_c has parity q, evaluation of chronological composition is

    ev(φ_b ; φ_c)=(-1)^(rq) b c.                              (3)

Evaluation at the probe zero-content regular object k similarly identifies
supernatural transformations V_s→V_t with these module maps. To see the
inverse rather than invoking an abstract representability slogan, extend a
map φ to φ⊗id on P_s⊗M_0. Naturality against the homogeneous maps
k→M_0 determined by individual homogeneous vectors forces this extension;
the tensor sign and supernatural sign cancel. Other input components are
zero. Hence evaluation is injective and surjective on these transformations.

Use the genuine word-Hom module

    W.V(t) = ⊕_(s with the same target weight as t) Hom(V_s,V_t).

These are finite-support sums of actual Hom spaces. The s-component can
vanish when the formal contents differ even if their weights agree. The
cyclic vector is the identity of V_t in the component s=t. An actual upward
morphism f:t→t' acts by chronological postcomposition with its evaluated
transformation. Associativity proves `act_comp`; no choice of regular
coordinates defines the action. Arbitrary upward presentation morphisms,
not only affine diagrams, act here once the full action has been assembled.
The source s in a recovery map remains s; it is never renamed ν(s).

Define the reservoir coefficient action by postcomposition with left
multiplication L_a on P_t. Since coefficients are supercentral,
L_a(z)=(-1)^(|a||z|)za=R_a(z), so it is a signed left-module map.
Moreover L_a L_b=L_(ab), which gives exactly an algebra map
SYM→End_k(W.V(t)). This coefficient action is constructed, not inferred
from `W.bubbles`; eventual bubble normalization must compare to it (or to
an explicitly specified pullback of it).

## 4. All-colour affine presentation map

Let C_Sc(s,t) be the unquotiented coefficient-extended affine Hom. Define U
on generators, with target corner e_ν(s) R_A(S) e_ν(t):

| Source generator | U-value |
|---|---|
| identity of t | e_ν(t) |
| dot at position r, colour i | x_(n+1-r) e_ν(t) |
| crossing t→s_r t | ε_(t_r,t_(r+1)) times the algebra crossing ν(s_r t)→ν(t), at n-r |
| a ⊗ identity | a e_ν(t) |

Extend by the signed chronological product U(f;g)=(-1)^(|f||g|)U(f)U(g)
on homogeneous morphisms. This is the corner form of a super-opposite map,
not an ordinary algebra anti-map. Coefficient tensors use the literal law

    (a⊗f);(b⊗g)=(-1)^(|a||g|)ba⊗(f;g).

For a pure coefficient tensor, U(a⊗f)=a U(1⊗f); this follows by placing a
after f and using supercentrality, with the two coefficient/diagram signs
cancelling. In particular there is no extra coefficient sign in this formula.

Here are the relation checks needed for the map and its inverse. They are
affine checks, before any cyclotomic quotient.

* Idempotent corners and endpoints follow from ν(s_r t)=s_(n-r)ν(t).
  Distant interchange follows from the super-opposite product and the
  usual disjoint-position supercommutation; no weight labels occur.
* Both equal-colour slides have constant +1. For s=(-1)^p, the algebra
  relations are τx₁-sx₂τ=1 and x₁τ-sτx₂=1. Reversal and τ↦-τ send the
  first relation to -s(x₂τ-sτx₁)=1, and the second similarly to the other
  slide. Equal-colour square-zero is unchanged. Distinct-colour slides
  exchange positions, with their same Koszul sign and zero constant.
* For a monomial u^r v^s of Q_ij, put p=p(i), q=p(j). Allowed support has
  pr=qs=0 modulo two. The two crossing multipliers contribute (-1)^(pq);
  the dotted monomial contributes (-1)^(p floor(r/2)+q floor(s/2)). Thus
  the required algebra coefficient is

      (-1)^(pq+p floor(r/2)+q floor(s/2)) Q^Sc_ij[u^r v^s],

  exactly `parameterTwist`. Reversing colours also reverses exponents.
  The disconnected constant occurs once and acquires (-1)^(pq).
* For an uncorrected braid both sides have the same crossing-parity pairs
  and equal-colour minus signs. For the corrected i,j,i braid, use the
  ordered terms of `Presentation.relation`, not commuting dots. If
  a=r-1-l, the target order is x₁^l x₂^s x₃^a. The reversal of the two
  braid words and the unique equal-colour crossing each contribute minus.
  The remaining parity identity is

      pq+pl+H = pa+T (mod 2),
      H=p binom(r-1,2)+q binom(s,2),
      T=pq+p floor(r/2)+q floor(s/2).

  Its difference is p[(r-1)+floor((r-1)/2)-floor(r/2)], zero when p=0
  and even when p=1 and r is even. For r=0 the correction sum is empty.
  This is the calculation in `DeformedMixedBraid.md` §§2–3, including
  its reverse corner table. It covers leading and interior coefficients.
* Coefficient supercommutation, exterior squares, and independent
  exterior products are preserved: coefficients are fixed, and two
  reversals contribute the defining supercommutativity sign twice.

These checks apply inside arbitrary left and right strand contexts. In
such a context r is replaced by n+1-r, the crossing by n-r, and disjoint
interchanges retain exactly their Koszul signs. They therefore descend
through the contextual presentation ideal, not just its isolated relations.

The inverse uses the identical generator table with Sc and S interchanged.
The parameter involution is proved by `parameterTwist_involutive`. Reversal
squares to identity, each ε occurs twice, the signed reversed-product signs
occur twice, and coefficients are fixed. Both composites fix every generator.
This proves the proposed affine presentation equivalence U. It does not
assume an action is faithful. This full argument still needs formalization;
`parameterTwist_involutive` alone is not that equivalence.

## 5. Exact transformed ideal; no identical-boundary requirement

Take the raw factor coefficients, without theta. Let I_N be the actual
first-boundary ideal in R_A(S), including the exact coefficient ideal J_N.
The inverse image K_N under U is the two-sided ideal generated by:

1. the unchanged coefficient ideal J_N in every word corner;
2. the following LAST-position polynomials in words v++[i].

If f_i(x)=Σ_(j=0)^N c_(i,j) x^j is the literal factor polynomial with
coefficients on the left, its inverse image is

    g_i(y)=Σ_(j=0)^N (-1)^(p(i) binom(j,2)) c_(i,j) ⊗ y_last^j.    (4)

For an odd colour c_(i,j)=(-1)^(N(j+1)) c_(N-j), where c_(2r)=χ_r and
c_(2r+1)=δ_iχ_r. For an even colour these are the ordinary alternating
elementary coefficients. Formula (4) follows from (1) on one dot, and
U(a⊗y^j)=(-1)^(p binom(j,2))a x^j. Its leading coefficient is a unit sign.
At N=0 it is 1. No odd coefficient or even-cutoff δ_iχ_(i,N/2) relation
has been removed.

The whole ideal equality U(K_N)=I_N follows in both directions: map every
homogeneous sandwich of a listed generator using the signed product law;
it is a unit sign times a sandwich of the corresponding factor generator.
Conversely every factor generator has the displayed preimage, and U is
surjective on its two outside factors. Decompose inhomogeneous factors
into homogeneous summands. This proves the kernel, not just annihilation
of a cyclic vector. The corner calculation (2) then identifies the actual
word-Hom corner with C_Sc(s,t)/K_N(s,t).

K_N is generally not the standard first-boundary ELV ideal. Nor need (4)
be the standard last-boundary polynomial with the same coefficients. At
odd cutoff two and δ=0 it is χ-y², whereas the standard relation is χ+y².
This agrees with the raw obstruction D²(1)=χ versus post_x²(1)=-χ.
It rules out the stronger coefficient-preserving global intertwiner, not
bounded recovery. The proposed theta from `ELVVacuumTransport.md` can be
studied separately; neither its validity nor any global quotient isomorphism
to the standard first-boundary quotient is required below.

## 6. Transfer of detection by the actual ideal bound

Suppose N₀≤N_i for all i. Every term of (4) has coefficient weight at least
N_i-j and j dots, at a valid last position with no crossing. It therefore
belongs to `ExtendedScore N_i`, hence `ExtendedScore N₀`. This is literally
the proof of `deformedCyclotomic_mem_score` with dot position length(v)
instead of zero: `highCoefficient_word_mem_score` and
`positionedScore_dots` permit every valid position.

Every element of J_N has coefficient weight at least N₀+1, by
`elvCoefficientIdeal_le_weight`. In particular the even-cutoff relation
δ_iχ_(i,m) has weight 1+2m=N_i+1, including δ_i at N_i=0.
Signs and the opposite product do not alter this estimate. Therefore

    K_N(s,t) ⊆ WeightedRelationSpan Sc s t N₀
             ⊆ ExtendedAtLeast Sc s t (N₀ - 2 choose(length(s),2)).   (5)

The second inclusion is the existing
`weightedRelationSpan_le_extendedAtLeast`, which already allows arbitrary
multicolour outside factors. Consequently the actual quotient map q_K is
injective on F_d=`ExtendedAtMost Sc s t d` whenever

    d + 2 choose(length(s),2) < N₀.                              (6)

No assertion that U preserves the chosen PBW normal forms or their upper
filtration is needed: the proof bounds the inverse images of the ideal
GENERATORS and uses the already checked two-sided weighted theorem.
This avoids hidden braid-straightening losses in a reversed PBW basis.

For the nilpotent reservoir of `DeformedReservoirBound.md`, include its
coefficient-power ideal T=(c_a^(L_a)). Choose each exponent so that
L_a coefficientWeight(c_a)≥N₀. Then U fixes these generators and they also
lie in `ExtendedScore N₀`. Equations (5)–(6) hold for K_(N,T) unchanged.
Thus finite coefficient quotients need not destroy the requested bounded
window. This is a bound on their actual kernels, not an invocation of
flatness. The nilpotence/action result for such quotients is separate.
The finite-support hypotheses of that result must still be respected;
this calculation does not by itself assemble an infinite-colour action.

## 7. Concrete bounded recovery with the original source indices

Work over the field used by the detection consumer. Let σ be the diagonal
source-order involution `reservoirSourceOrder`; on homogeneous a and f,

    σ(a⊗f)=(-1)^(|a||f|)a⊗f.

It preserves F_d and squares to identity. Project W.V(t) to its actual
s-component, evaluate its natural transformation at k, then at e_ν(s),
and apply the descended inverse of U. Denote this explicitly defined map

    coordK(s,t): W.V(t) → C_Sc(s,t)/K_(N,T).

Equations (1)–(3) give the requested concrete generator square BEFORE
extracting a standard quotient:

    ev_s(act(g)(φ_b))=(-1)^(|g||b|) b U(g),
    coordK(s,t')(act(alpha(f))(reservoir(a)(vacuum(s))))
       = q_K(σ(a⊗f)),               f:s→t'.                    (7)

The first equation applies to every positioned dot and every equal or
unequal-colour crossing. The second follows by chronological composition,
not by redefining the top action. Also coordK(t,t)(vacuum(t))=q_K(1_t).
In (7) the starting cyclic word is s, the target is t', and the physical
corner is e_ν(s) B e_ν(t'); these indices must not be interchanged.

Let i_d:F_d→C_Sc(s,t)/K_(N,T) be restriction of q_K. By (5)–(6) it is
injective. Choose its k-linear left inverse L_d on the whole quotient by
extending a basis of its image (the same linear-algebra construction as
`reservoirWindowCoordinates`). Its values on the image are canonical.
With q_first the standard, untruncated `ELVRelationSpan Sc N` quotient map,
define

    recover_(s,t,d) = q_first ∘ σ ∘ inclusion(F_d) ∘ L_d ∘ coordK(s,t).  (8)

Then for a⊗f∈F_d, equation (7), L_d i_d=id, and σ²=id give

    recover_(s,t,d)(act(alpha(f))(reservoir(a)(vacuum(s))))
        = q_first(a⊗f).                                      (9)

This is exactly the bounded `affine_coordinates` law with the original
source words and external weight μ. It holds for arbitrary ordered
multicolour exterior products, by linearity and the coefficient parity law.
It transfers detection from the actual last-boundary signed coordinates
to the desired first-boundary quotient, without identifying their ideals.
No global dot-intertwining law for (8) outside the window is claimed.

For every fixed s,t,d choose m with h=-D.h μ and
N_i=reservoirLevel h m i satisfying d+2 choose(length(s),2)<2m, and take
sufficiently high coefficient truncation powers. This constructs every
requested admissible bounded observation. It does not yet package a single
everywhere-defined `ReservoirVacuumEvaluation`: its `window` field is total
in all word lengths at a fixed cutoff. At the remaining long words its
zero window still contains identities and crossing-only diagrams, so setting
recover=0 is not justified. A zero-window extension requires a separate
kernel-compatibility proof and has NOT been established here.
`regularVacuumWindow_covers` supplies cofinal admissible m for every fixed
s,t,d. A consumer formulated for admissible observations would avoid this
extension; no interface change or small-cutoff theorem is asserted in Lean.

## 8. Exact remaining boundary

The proposed affine generator equivalence and whole-ideal transport above
provide an explicit kernel and recovery, rather than an assumed regular
identification. They do not supply a new factor action or a new hypothesis
for a nondegeneracy theorem. Remaining obligations are:

* formalize the affine presentation comparison, signed Hom-corner evaluation,
  and bounded inverse-ideal argument;
* assemble the swapped normalized Hom action, including its full augmented
  inversion and all presentation relations, and verify that its surviving
  reservoir blocks are precisely those used in (1) and (7);
* package admissible bounded observations in the detection interface, or
  prove the needed small-cutoff/zero-window extension rather than assuming it;
* identify the actual source-placed bubbles with the constructed reservoir
  coefficient action, including any required normalization;
* retain the scope of the supplied factor actions when passing beyond their
  finite compatible support. Weight arithmetic itself works for arbitrary I.

The local obstruction from keeping raw coefficient coordinates is therefore
not a no-go theorem for detection. The correct next comparison is (7) for
the assembled swapped action and then the bubble action, not equality of
first- and last-boundary indexed ideals.

## Source definitions used

* `OddMath/SKM/RouquierHom.lean`: `homPre`, `homPost`, `homPostTransform`.
* `OddMath/SKM/RouquierHomContent.lean`: `homWeightSector`, `homContentPostE`,
  `homContentPreE`, `homContentShift`.
* `OddMath/QuiverHecke/Algebra.lean`: `Hn.single_mul_single`, word idempotents.
* `OddMath/QuiverHecke/CyclotomicAction/InductionComposition.lean`:
  `compositionCornerLinear`, `compositionCornerInverseLinear`,
  `inductionCompositionIso` (ordinary-polynomial implementation).
* `OddMath/QuiverHecke/CyclotomicAction/ParameterTransport.lean`:
  `parameterSignExponent`, `parameterTwist_involutive`.
* `OddMath/QuiverHecke/Presentation.lean`: `relation`, especially both slides
  and the ordered `braidEq` correction.
* `OddMath/SKM/BubbleELVSpecialization.lean`: `ELVCoefficientRelation`,
  `elvCoefficientIdeal_le_weight`.
* `OddMath/QuiverHecke/WeightedCoefficientSeparation.lean`:
  `highCoefficient_word_mem_score`, `weightedRelationSpan_le_extendedAtLeast`,
  `weighted_quotient_injective_on_extendedAtMost`.
* `OddMath/QuiverHecke/ELVCyclotomicSeparation.lean`: `ELVGenerator`,
  `ELVRelationSpan`, `elv_quotient_injective_on_extendedAtMost`.
* `OddMath/QuiverHecke/ReservoirCoordinates.lean`: `reservoirWindowCoordinates`,
  `exists_bounded_reservoir_extraction`.
* `OddMath/QuiverHecke/ReservoirSourceCoordinates.lean`:
  `reservoirSourceOrder_source`, `_involutive`, `_mem`.
* `OddMath/QuiverHecke/ReservoirFusedVacuum.lean`: the k-linear `coord` and
  constructed `reservoir` fields of `RegularVacuumIdentification`, and the
  independent h parameter of `FusedRegularVacuumFamily`.
* `OddMath/QuiverHecke/ReservoirVacuumDetection.lean`:
  `ReservoirVacuumEvaluation`, `NormalizedBubbleFormula`.
* Written factor comparisons: `DeformedActionAssembly.md` §§1,5–6,
  `DeformedMixedBraid.md` §§2–4, `DeformedReservoirBound.md` §§1–3.
