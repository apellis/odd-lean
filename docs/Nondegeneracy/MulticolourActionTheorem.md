# Even-cutoff multicolour action: consolidated paper-level argument

Research manuscript, 2026-10-25. This is a proposed theorem supported by
the source adaptations below. It is not a theorem already formalized in
Lean. The individual quotient maps and the assembled super-2-functor
still require independent review and native implementation.

## Statement and scope

Fix finite symmetrizable Cartan superdatum and homogeneous quiver Hecke
superalgebra parameters in the scope of KKO, with invertible prescribed
leading coefficients and `2` invertible. Use the polynomial parameters
matching the native SKM upward presentation. This statement does not
cover arbitrary nonsymmetrizable BE2 data or arbitrary nonhomogeneous
`Scalars` merely because the native presentation permits them.

Choose a dominant weight `Λ` whose odd-colour coordinates `N_i` are
positive even integers, say `N_i=2m_i`. Over an even commutative graded
coefficient ring, adjoin independent odd parameters `d_i` and even
parameters `χ_(i,r)` with the corresponding homogeneous degrees. Impose
supercommutativity, `d_i²=0`, and `d_i χ_(i,m_i)=0`. Additional
parity-preserving base specializations are allowed provided the stated
parameter units survive; the graded action additionally requires
grading-preserving specialization.
Define

`C_i(z)=z^m_i+χ_(i,1)z^(m_i-1)+...+χ_(i,m_i)`,

`q_i(z)=(C_i(z)-χ_(i,m_i))/z`,

`f_i(x)=C_i(x²)-x d_i q_i(x²)`.

At even colours use the usual homogeneous monic cyclotomic polynomial
with even coefficients. Let `R_f(β)` be the cyclotomic quotient by the
first-strand polynomials `f_i`.

**Proposed theorem.** Induction and restriction between the projective
supermodule categories of `R_f(β)` have their standard induction/
restriction adjunction, the standard affine dot and crossing maps, and
invertible native SKM same- and different-colour inversion matrices.
With native `E=induction`, `F=restriction`, and weight `-Λ+β`, these data
define an action of the native SKM presentation, in the additive and
parity-completed target. In particular the same-colour inverse entries
exist with the original adjunction, rather than with newly chosen cups
and caps.

This theorem asserts existence of this family of actions. It does **not**
assert faithfulness, full coefficient separation, or fixed-weight SKM
independence. Dominant weights are not generally cofinal in a prescribed
root-lattice coset. All odd native coroot heights in the stated family
are even; odd-height components require a separate extension.

## Proof dependencies and argument

The baseline sources are
[KKO, arXiv:1206.5933v2](https://arxiv.org/abs/1206.5933), Sections 7--9,
[Kang--Kashiwara, arXiv:1102.4677v4](https://arxiv.org/abs/1102.4677),
Lemmas 4.18--4.19 and Section 5.2, and
[ELV, arXiv:2203.14153v2](https://arxiv.org/abs/2203.14153), Theorem 4.5.
The last source establishes the odd-coefficient rank-one case; its
universal-category equivalence is not used as an independence input.

1. **Affine algebra and normality.** Start with the standard PBW
   descriptions over the even coefficient ring and extend coefficients
   superlinearly. Each `f_i` has even total parity. It commutes with
   distant crossings and dots, and obeys the ELV first-dot normality
   `x f_i=f_i(x-2d_i)`. The top-coefficient relation is used here.
   Independent parameters of other colours introduce no extra sign:
   in `x d_i` the two odd commutation signs cancel.

2. **The exact `P` sequence.** Use KKO's modules `K₀,K₁` and map
   `P(b⊗y)=b f_i(x₁)τ₁...τ_n⊗y`, with the specified parity shift.
   Normality plus PBW gives the cyclotomic ideal decomposition of
   Lemma 8.2. The old-dot and old-crossing balancing errors shorten
   the crossing prefix and belong to the old cyclotomic ideal. Thus
   `P` descends and its image is the kernel of `K₀→R_f(β+α_i)e(β,i)`.
   Its extra-variable law is `P(zt)=P(z)(t-2d_i)`, not ordinary
   `t`-linearity. Details are in the
   [balanced-map audit](MulticolourCyclotomicAction.md).

3. **`Q` and injectivity.** Use the original affine intertwiners for
   `Q`. Their transport of an odd coefficient has the sign already
   encoded by the parity shift. In the repeated-colour step of the
   (8.14) induction both the dot and its odd coefficient change sign,
   so their even product transports unchanged. This gives
   `QP=f_i(t)G_i(t²)` for odd `i`, with the original norm product `G_i`.
   The leading coefficient is a unit. PBW polynomial coordinates give
   injectivity, even over a base with exterior zero divisors. See the
   [norm audit](OddUnfurling.md).

4. **Projectivity without a circular use of `PQ`.** Put `s=t²`.
   The conjugate identity
   `(C_i(x²)+x d_i q_i(x²)) f_i(x)=C_i(x²)²`
   supplies a monic first-dot square annihilator independently of `PQ`.
   KKO Lemma 7.3 propagates it to every dot square. The `P` translation
   fixes `s`, so its exact sequence is `B[s]`-linear, with
   `B=R_f(β)`. The PBW projectives remain projective over `B[s]`, since
   the split skew polynomial algebra is free of rank two over `B[s]`.
   Kang--Kashiwara Lemma 4.18 now gives projectivity of the cyclotomic
   induction bimodule over `B`. No fibrewise-flatness inference is used.
   For the left-projectivity assertion needed by restriction, apply
   the same argument to the opposite presentation: ordinary diagram
   reversal is the affine map of KKO (6.3), which fixes dots and
   crossings under the stated parameter hypotheses. The opposite polynomial has
   exterior parameter `-d_i^op`. It is the same allowed family over
   the opposite coefficient superalgebra. On the universal exterior
   base this can equivalently be expressed by the anti-involution
   fixing the even parameters and sending `d_i` to `-d_i`.
   Merely fixing `d_i` under ordinary reversal would be incorrect.

5. **Companion norm.** Translation fixes `t²`, `td_i`, and therefore
   the norm `f_i(t)G_i(t²)`. Hence the commuting square of norm maps
   and `P` holds.
   The difference `PQ-A₀` factors through the cyclotomic cokernel.
   This cokernel has a monic `s`-annihilator, whereas multiplication
   by that polynomial is injective on `K₀`. Consequently the
   difference vanishes, as in Kang--Kashiwara Lemma 4.19.

6. **Actual inversion, not only dimension counting.** Form the exact
   Mackey diagram (9.5), using the preceding projectivity result.
   The filtered coefficient argument gives `γφ_k` monic of degree
   `a+k`, for KKO height `a` and a unit `γ`. The extra-variable defect
   is the ELV twisted one; its even norm factor is fixed by translation.
   This calculation is detailed in the balanced-map audit.
   At `a≥0`, the cokernel basis lifts by actual dotted units.
   At `a<0`, the deformed recurrence first gives an invertible
   antitriangular cap matrix using `X-2R_(d_i)`. Its powers differ
   from actual dot powers by a unitriangular change of rows, so the
   actual dotted-cap matrix is invertible as well. At `a=0` the mate
   alone is invertible. Distinct-colour inversion follows from the
   same ideal decomposition and the affine Mackey map. The map and
   orientation checks are in
   [CoupledBubbleEvaluation.md](CoupledBubbleEvaluation.md).

7. **Presentation and coherence.** Induction/restriction unit and
   multiplication counit satisfy the adjunction triangles on tensors.
   Their mate of the upward crossing is the map `a⊗π_i b↦aτ_n⊗b`
   in (9.5). Under the negative weight convention above, KKO's
   positive-height unit matrix is the native negative-height matrix;
   its negative-height cap matrix is the native positive-height one.
   The native inverse generators are assigned the corresponding
   inverse matrix entries, with the signs prescribed by the native
   presentation (in particular `lcross=-σ⁻¹` at height zero).
   These are the presentation relations; no independent arbitrary
   choices of left cups or caps are introduced.

## Verification status

`CyclotomicNorm.lean` checks square-zero norm factors, conjugate products,
matching-sign transport, and translation invariance. Its concrete
consumer passes with only `propext` in the printed axiom lists.
`DotTranslation.lean` additionally checks preservation of the paired
odd braid correction. The all-content bimodule maps, exact sequences,
filtered monicity, and the assembled action above are written
mathematical arguments, not native Lean declarations.

The finite connected and rank-one matrix experiments elsewhere in the
repository test particular instances with nonzero exterior coefficients.
They support sign checks but are not substituted for the all-content
proof. Before promoting this manuscript to a completed theorem in the
research board, independently review the balanced-map and norm audits,
including the parity conventions in the negative-height cap conversion.
