# Separated monomials under rectangular bending

Brundan–Ellis Lemma 3.3 supplies the mixed-braid correction used in the
canonical cap-pitchfork tests of Lemma 7.1. The ordered correction monomial
has an endomorphism on each of three consecutive strands. Bending its
outer strands with the prescribed even right adjunctions separates it
into the dotted cap, the middle endomorphism and the dotted cup.

For `E : a → b`, `G : b → c`, `H : c → d`, with right adjoints `F`, `K`,
`rectangularMate_associator` first computes the rectangular mate of the
associator as the cap followed by the cup, retaining all associators and
unitors. The proof transposes the capped input and applies naturality of
the postcomposition adjunction; no cyclicity or left adjunction is used.

`rectangularMate_separated` permits arbitrary endomorphisms `x`, `y`, `z`
of `E`, `G`, `H`. Its ordered input is

    ((x ▷ G) ▷ H) ; associator(E,G,H) ; (E ◁ ((y ▷ H) ; (G ◁ z))).

After bending and the two outer associators, its output is

    ((F ◁ x) ; counit) ▷ G ; leftUnitor ; y ; rightUnitor⁻¹
      ; G ◁ (unit ; (z ▷ K)).

Input and output naturality of the rectangular mate remove the two outer
endomorphisms. Naturality of the even postcomposition unit moves the
middle endomorphism to its indicated position. The order is retained and
there is no extra parity coefficient. Substituting the prescribed dot
powers gives the dotted correction terms; the conversion to the actual
multicolour diamond and the cap-boundary vanishings are separate steps.

The producer and paired consumer pass strict checks, including the
standard-axiom audit of all three owned declarations. The consumer applies
both formulas to a constructed rational unit-supercategory adjunction
and nonzero scalar endomorphisms with nonzero composite, and audits every
owned declaration. This calculation alone does not establish the canonical
left-mate inverse or the nondegeneracy theorem.
