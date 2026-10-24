# Elementary odd sorting and coefficient placement

This calculation supports the Brundan–Ellis §8 Nondegeneracy Conjecture. It gives
identities of SKM morphisms. [ElementaryClosure](ElementaryClosure.md) uses them
to prove independence of the fixed family below **conditional on upward SKM
independence with full SYM coefficients**, not the general conjecture.
Throughout, composition `f ; g` means `f ≫ g`. The base and scalar data are those
of the existing SKM presentation.

Fix an odd colour `i` and `h_i(μ)=1`. Put `A=E_i F_i 1_μ`, `B=F_i E_i 1_μ`,
`O=1_μ`. Use the following morphisms from
[`LeftDot.lean`](../../OddMath/SKM/LeftDot.lean):

- `u=uLM`, `d=dRM` in `End(A)`; `x=uRM`, `v=dLM` in `End(B)`;
- `S=sgM : A→B`, `L=lcM : B→A`;
- `e_n=eLM n : A→O`, `H_n=hLM n : O→B`;
- `D=dcM 0 : O→A`, `c=cs.c μ i`, `J=etaP=c D`;
- `q_n=D;e_n`, with `q_0=1`.

The equality for `J` is its defining positive-weight normalization. Powers here
mean repeated vertical composition. Fix the dot serializer

\[
 T_{ab}=u^a;d^b,\qquad K_{ab}=e_a;J;u^b.
\]

These are the through and cap-cup matching types, with the cap and cup dots on
their upward legs. For `p ∈ SYM`, the prescribed source coefficient means
prefixing by `P_A(p)=bubAt μ A (betaSYM μ p)`. No commutation of `p` is implicit.

## Both sorting components

The component map is `f ↦ (f;S, f;e_0)`, with reconstruction

\[
 f=-(f;S);L+(f;e_0);D.
\]

Indeed, the inversion relations give `S;L=e_0;D-1`, `L;S=-1`, `L;e_0=0`,
`D;S=0` and `D;e_0=1`. The minus sign in reconstruction is necessary.

Let `χ(b)=b(b−1)/2`. The dot slides give

\[
 T_{ab};e_0=(-1)^{\chi(b)}e_{a+b},
\]

\[
\begin{aligned}
 T_{ab};S={}&(-1)^{a+b}S;x^a;v^b\\
 &+\sum_{s<a}(-1)^{a+b+1+s}e_s;H_{a-1-s};v^b\\
 &-\sum_{r<b}(-1)^{r+\chi(b-1-r)}e_{a+b-1-r};H_0;v^r.
\end{aligned}
\]

For the cap-cup matching,

\[
 K_{ab};e_0=c\,e_a;q_b,\qquad
 K_{ab};S=c\sum_{r<b}(-1)^{b+1+r}e_a;q_r;H_{b-1-r}.
\]

These follow by induction from the odd specializations of `sg_uR`, `sg_dL`,
`uL_eL` and `dR_eL`. In particular,

\[
 S;x^b-(-1)^b u^b;S
   =\sum_{r<b}(-1)^r e_r;H_{b-1-r};
\]

prefixing by `D`, using `D;S=0` and `D;e_r=q_r`, proves the second cap-cup
formula. The terms remain in the indicated order and region. For arbitrary
source coefficients, prefix **every** term by `P_A(p)`.

The first cases are

\[
\begin{aligned}
 K_{a0}&\longmapsto(0,c e_a),\\
 K_{a1}&\longmapsto(c e_a;H_0,c e_a;q_1),\\
 K_{a2}&\longmapsto(c[-e_a;H_1+e_a;q_1;H_0],c e_a;q_2).
\end{aligned}
\]

The zero in the first component does not permit discarding these labels. These
identities do not classify the kernel of that component or assert that the
remaining expressions are nonzero without a separate independence argument.

## Bending and the changed-weight coefficient

Applying `SpanBend.bendF` with source word `[up i,dn i]` gives target words
`EFFE` and `EF`, not all-upward words. Its return sign is `+1` in this weight
case, but that does not turn it into a coefficient comparison with an upward
basis. The right-adjunction closures to `EE` and `E` instead use rightmost weight
`λ=μ−α_i`. Their dot, crossing and coefficient images are computed with the
literal cup/cap placements in [ElementaryClosure](ElementaryClosure.md).

Already the first odd elementary coefficient has a correction. Write

\[
 Q_2(\nu)=c_{\nu;i}^{-1}\operatorname{bubLs}(i,\nu,2)
         =\beta_\nu(e_{i,1}).
\]

The source generator `e_{i,1}` is `SYM.e i 0` in Lean. At **every** weight `λ`,
not only the elementary sorting weight, the same-colour slide specializes to

\[
 \operatorname{lbub}_i(\lambda,Q_2(\lambda+\alpha_i))
 =\operatorname{rbub}_i(\lambda,Q_2(\lambda))+3x_i^2.
\]

[`BubbleCoefficientTransport.lean`](../../scripts/NonVacuity/BubbleCoefficientTransport.lean)
checks this on the actual `betaSYM` generator, with a concrete two-odd-colour
scalar datum over `ℚ`. Its hypotheses and normalization are discharged; its
axioms are `propext`, `Classical.choice` and `Quot.sound`.
This is an identity, not a claim that `3x_i²` is nonzero in every allowed base.
Odd dot squares are not exterior squares, so deleting the term uniformly is
unjustified. In contrast, the actual odd bubbles slide by
`OddBubbleCentrality.oddBubble_slide_up`.

The full coefficient and middle-bubble transport in
[ElementaryClosure](ElementaryClosure.md) now supplies the conditional
division-with-remainder argument for this family. The transported source
coefficient has constant dot coefficient `p`, and middle-bubble transport
introduces no left-strand dot in the chosen two-strand closure. These are the
additional facts that make the `r=0` term leading. Morphism reconstruction
alone does not give formal matching independence, and the upward independence
input and global arbitrary-matching comparison remain unproved.

## Checks and their scope

Run `python3 scripts/Nondegeneracy/elementary_sorting.py`. It checks the four
component formulas by typed, ordered word reduction from the displayed local
relations, including an untouched source coefficient prefix. It retains the
middle bubble symbols rather than commuting or erasing them. These are exact
finite word-identity checks, not a representation of SKM, a simulation of the
right-adjunction closures, or a proof of matching independence.
