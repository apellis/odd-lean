# Odd cutoffs and exterior translation

Status: **proposed**. This proves a reduction of the odd-cutoff extension to
the unshifted odd-cutoff action. It does not fill the presentation-comparison
gap recorded in ActionReview.md, nor claim a new Lean action theorem.

## The parameter and its parity

For odd colour i let `N_i=2m+1`. Take

`A_i=k[χ₁,…,χ_m]⊗Λ(d_i)`,
`C_i(z)=z^m+χ₁z^(m−1)+…+χ_m`,
`f_i(x)=(x−d_i)C_i(x²)`.

There is **no** relation `d_iχ_m=0`. In ELV,
arXiv:2203.14153v2, (3.24)–(3.27), this is `−a_(2m+1)(x)`;
the harmless minus sign makes it monic. Its parity is odd. At m=0 the
relation is x−d_i, not x and not x²−xd_i. The independent parameters of
distinct colours are super tensor factors; in particular `d_i d_j=−d_j d_i`.
ELV's remark that its coefficient algebra is also ordinarily commutative
uses a single exterior generator and cannot be extended to this multicolour
base.

This is required by the target's weight lattice, not an optional variant:
for odd i the compatible Cartan matrix has even i-th row, so
`⟨h_i,λ+Σ_j n_jα_j⟩≡⟨h_i,λ⟩ (mod 2)`.
Even cutoffs alone cannot change an odd value in this coset.

## Normality: a warning against copying the even-cutoff twist

For homogeneous a in the coefficient algebra,

`xf_i=f_i(x−2d_i)`, `a f_i=(−1)^|a| f_i a`.

The normalizing automorphism on the first-dot coefficient extension is

`ν(x)=x−2d_i`, `ν(a)=(−1)^|a|a`.

It fixes x² and f_i and satisfies ν²=id. Its inverse therefore also sends
x to x−2d_i. This contrasts with even cutoff, where ν fixes a and ν inverse
sends x to x+2d_i. Ignoring this coefficient involution gives a wrong
right-module twist. The source formula `f_i x=(x−2d_i)f_i` is exactly the
odd-n version of ELV (3.27).

An even central monic annihilator is available without a conjugate choice:
`f_i²=x² C_i(x²)²`. Thus an odd polynomial creates no obstruction to the
square-variable projectivity mechanism. Its odd parity must nevertheless
remain in KKO's `Π_i^(N_i+p(β))` and `T_i^N_i` twists. KKO I,
arXiv:1206.5933v2, §7.1 and (8.2)–(8.5), permits odd N_i and explicitly
retains those twists. Replacing them by their even-N specializations is not
an extension to odd cutoff.

## Exterior translation of the affine algebra

Let S be any set of odd colours, and choose independent exterior coefficients
d_i for i in S. On each word idempotent set

`θ(x_r e(ν))=(x_r−d_(ν_r))e(ν)` if ν_r is in S,

and fix all other dots, all crossings, all idempotents, and all coefficients.
Then θ is a graded affine algebra automorphism, with inverse translating by
+d_i. Give d_i the same degree as an i-dot.

Here is the relation check, including the repeated-colour braid correction.

1. Translated odd dots anticommute with each other and with odd coefficients,
   since the coefficients are exterior and supercommute with affine
   generators. Their squares equal the original dot squares.
2. A crossing at colours i,j has parity p(i)p(j), including when the
   colours differ. If the transported dot has odd colour, its coefficient
   supercommutes with the crossing with exactly the sign in the dot-slide.
   Thus the new coefficient terms cancel in both different-colour slides.
   At equal odd colour the crossing anticommutes with d_i, so the two new
   terms in `τ(x−d)+(y−d)τ=1` cancel. The other slide is identical.
   Distant dot/crossing relations have the same sign check.
3. The mixed quadratic polynomial depends only on squares of any odd
   variables, by the KKO parameter restrictions. It is unchanged. Crossing
   nilpotence and distant crossing supercommutation are unchanged as well.
4. For a repeated odd outer colour, the alternating divided difference can
   be paired into terms `x^(2r)(x a−a z)z^(2s)`. The middle coefficient a
   is even and commutes with d_i. Both the square powers and `x a−a z`
   are unchanged by simultaneous translation. This checks the entire braid
   correction, not only its highest term. For an even outer colour the
   translated middle odd variables enter only through squares; for three
   equal colours the correction is zero.

Existing local identities are
`OddMath.OddNilHecke.DotTranslation.square`, `slide`, and
`braidPolynomial_translate`. They are supporting identities, not an existing
multicolour algebra equivalence.

## Quotients and the relative action theorem

At every colour in S replace the polynomial by the unshifted
`g_i(x)=x C_i(x²)`, retaining independent d_i in the coefficient algebra.
At other colours retain the prescribed polynomials, including the even-cutoff
ELV polynomials where applicable. Translation affects none of those other
colours. Then `θ(g_i)=f_i` and θ carries the entire cyclotomic ideal to the
new ideal. It induces compatible algebra equivalences at every β, respecting
strand-adding idempotents and the embeddings for induction and restriction.

**Relative theorem.** Suppose the unshifted family has the specified SKM
action, with its original adjunction and invertible inversion matrices.
Then the translated odd-cutoff family has such an action with its prescribed
dots and the same crossings and adjunction maps.

To see the last clause, transport the unshifted action along θ. Its dots
are x−d. Restore the prescribed dots x by exterior translation. The affine
relation check above applies. The crossing mate is unchanged. In the
same-colour inversion matrix, each even dot power is unchanged and each
odd dot power differs by d times the preceding even power. After including
the parity shifts, this is a triangular row or column automorphism with
diagonal one. It is invertible by negating the translation. Hence both
signs of the coroot height and height zero retain inversion. The unit and
counit have not been chosen anew. The quotient equivalences also preserve
projectivity; no argument from fibres or dimensions is needed.

For cutoffs that are odd at every odd colour, the unshifted family is exactly
KKO's allowed coefficient family, super-extended by independent exterior
parameters. For mixed cutoff parities it is the proposed even-ELV argument
with KKO's full N_i-dependent twists at the remaining odd cutoffs. At the
latter colours the polynomial is xC(x²), so there is no new deformed
normality calculation: the original KKO signed formulas apply. The proof
must keep those twists in the same multicolour diagram; one cannot combine
independent rank-one actions and declare their mixed relations checked.

Thus there is no algebraic odd-cutoff obstruction and no reason to discard
the ELV parameter at odd height. The outstanding obstruction to promoting
this to an unconditional SKM action theorem is precise: the complete
multicolour source-to-presentation comparison from ActionReview, followed by
the balanced diagram with arbitrary N_i parity. These are not supplied by
ELV's rank-one theorem. The relative result isolates them from the
odd-parameter extension itself.

Finally, an algebra equivalence after shifting dots does **not** say that
the exterior coefficient is invisible to the action. Its specified dot and
therefore its normalized bubbles change under that equivalence. Coefficient
detection must use those specified dots, not just the isomorphism class of
the underlying algebras.
