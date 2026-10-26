# Signed reflection and the canonical F triangle

**Status: written mathematical proof, not yet checked in Lean.** This is a
proof for the inverse-defined generators in `RouquierLeftCupCap`, not an
additional interface assuming a triangle. The input is two adjacent
`SuperRouquierLoc`s, their even right adjunctions, both crossing squares, and
the upward braid. The local E triangle is already proved in
`RouquierPitchfork.leftAdj_triangle_E_of_neg/of_nonneg`.

The source step is Brundan, *On the definition of Kac–Moody 2-category*,
arXiv:1501.00350v1, Theorem 4.3: obtain the other triangle by reflection.
Its even local implementation is `Categorification/TwoRep/RouqAdjunction.lean`,
`RouqLoc.mirror` and `leftZigzag_left`. Brundan–Ellis,
*Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §6, Proposition 6.2,
(6.6), also proves the second triangle from an opposite symmetry. Their
left cups/caps have an additional normalization (see their introductory
“Second adjunction” paragraph); they are not silently identified with this
repository's unnormalized inverse components. Neither that proposition nor
any subsequent cyclicity/pitchfork relation is an input here.

## 1. Conventions and statement

Write composition in execution order, `u;v`. Write a string of 1-morphisms
in the repository's order: `E₁E₂ : a → c` if `E₁ : a → b` and `E₂ : b → c`.
Associators and unitors are suppressed in calculations below, but always
insert the unique canonical even coherence maps. This notation does not
assume strictification or an unsigned interchange law.

Let `A_j : E_j ⊣ F_j` have even unit `η_j : 1 → E_jF_j` and even counit
`ε_j : F_jE_j → 1`. Let `L` be centred at `b` at height `h`, and `U` be
centred at `c` at height `h+2`. Their dots and crossings have parity `p`.
Set

```
s = (-1)^(p p),       q(n) = s^(n(n-1)/2)  (n ≥ 0),
σ = p(h+1) in Z/2,   e(h) = 1 if h<0, and s if h≥0.
```

The required statement, with no renormalization of either generator, is

```
Z_F := λ_F₂⁻¹ ; (U.cupL ▷ F₂) ; α_F₂,E₂,F₂ ;
                       (F₂ ◁ L.capL) ; ρ_F₂
     = (-1)^(σσ) e(h) id_F₂.                         (1)
```

It is even: both `U.cupL` and `L.capL` have degree `σ`. Explicitly its
coefficient is `s^(h+1)` for `h<0`, and `s^h` for `h≥0`; integral powers
of the unit `s` make sense also for negative exponents. In particular the
coefficient at `h=-1` and at `h=0` is one.

## 2. Right transposition from even right adjunctions

For parallel right-adjointable 1-morphisms `V,W : a → b`, and homogeneous
`f : V → W`, define

```
M(f) : W* → V*
     = (W* ◁ η_V) ; (W* ◁ f ▷ V*) ; (ε_W ▷ V*).
```

Thus `|M(f)|=|f|`. No left adjunction is used. The two bending equations are

```
(M(f) ▷ V) ; ε_V = (W* ◁ f) ; ε_W : W*V → 1_b,    (2)
η_V ; (f ▷ V*) = η_W ; (W ◁ M(f)) : 1_a → WV*.     (3)
```

To prove (2), substitute the definition, move its even unit past the
adjacent whiskered map, and contract the `V` right-adjunction snake.
Equation (3) is obtained by substituting the same definition and contracting
the `W` snake. Every exchanged pair has an even member, so the sign is one.
These also prove uniqueness: if `β : W*V → 1_b`, the inverse of bending
a map `ψ : W* → V*` down to `(ψ ▷ V);ε_V` is

```
β ↦ (W* ◁ η_V);(β ▷ V*).
```

The inverse of bending `f : V → W` to `(W* ◁ f);ε_W` is
`β ↦ (η_W ▷ V);(W ◁ β)`. The inverse checks are precisely the two right
snakes, with even cups/caps. Consequently `M` is a parity-preserving linear
bijection on each homogeneous Hom space, including degree zero; in
particular it is injective and `M(id)=id`, `M(0)=0`.

For `f : V → W` of degree `r` and `g : W → T` of degree `t`, equation (2)
gives a useful explicit sign calculation:

```
((M(g);M(f)) ▷ V);ε_V
 = (M(g) ▷ V);(W* ◁ f);ε_W
 = (-1)^(rt) (T* ◁ f);(M(g) ▷ W);ε_W
 = (-1)^(rt) (T* ◁ (f;g));ε_T.
```

The middle equality is the single super interchange of `M(g)` and `f`.
Uniqueness therefore proves

```
M(f;g) = (-1)^(rt) (M(g);M(f)).                    (4)
```

This sign must not be dropped. Induction in (4) yields

```
M(x^n) = q(n) M(x)^n                              (5)
```

for a degree-`p` endomorphism `x`; at the induction step the new factor is
`s^n`, and `n(n-1)/2+n=(n+1)n/2`.

For composable `V,W`, use the composite right adjunction with

```
η_VW = η_V ; (V ◁ η_W ▷ V*),
ε_VW = (W* ◁ ε_V ▷ W) ; ε_W.
```

Substitution in (2), with these displayed counits, gives

```
M(V ◁ g) = M(g) ▷ V*,
M(f ▷ W) = W* ◁ M(f).                             (6)
```

Indeed, in the first case move `g` past the even `ε_V`, then apply (2)
for `g`; in the second apply (2) for `f` inside `W*[-]W`, then move the
result past the even `ε_W`. These verify the bending characterizations
for the composite adjunction, so uniqueness proves (6). There is no sign
in either whiskering identity. If horizontal composition is defined by
`f ⊗ g = (V ◁ g);(f ▷ W')`, equations (4) and (6) give the fully signed law

```
M(f ⊗ g) = (-1)^(|f||g|) (M(g) ⊗ M(f)).          (7)
```

The source and target on the right are `W'*V'* → W*V*`. Coherence maps
are even; their mates reverse the order of adjoints and reassociate the
reversed string. For example `M(α⁻¹_V,W,T)=α⁻¹_T*,W*,V*` with the
corresponding two bracketings. This follows by the same characterization
(2): expanding the two composite counits only rebrackets the same string
of even counits. No crossing relation enters any of (2)–(7).

## 3. The horizontal opposite and the partial-mate comparison

Use `HOpS(B)` with the same objects, reversed 1-morphisms and unchanged
Hom supercategories and vertical composition. Set

```
f ∘' g = gf,       f ◁' u = u ▷ f,       u ▷' f = f ◁ u,
α'_(f,g,h) = α_(h,g,f)⁻¹,  λ'_f = ρ_f,  ρ'_f = λ_f.
```

All coherence is even. The opposite interchange equation is the original
interchange equation solved in the reverse direction; its coefficient is
unchanged because `(-1)^(rt)` is its own inverse. The pentagon and triangle
are the reversed original coherence equations. Thus this is a
2-supercategory over the same ring, not an ordinary bicategory replacing it.
Each original `E_j ⊣ F_j` gives `F_j ⊣' E_j` with the *same* `η_j,ε_j`:
the two reflected right snakes are the original right snakes exchanged.

Here is the comparison that prevents the reflection from assuming the
answer. All displayed maps are in the original category. Define

```
P : End(E₁E₂) → Hom(F₁E₁,E₂F₂),
P(t) = (F₁E₁ ◁ η₂);(F₁ ◁ t ▷ F₂);(ε₁ ▷ E₂F₂),

Q : Hom(F₁E₁,E₂F₂) → End(F₂F₁),
Q(u) = (F₂F₁ ◁ η₁);(F₂ ◁ u ▷ F₁);(ε₂ ▷ F₂F₁),

R : End(F₂F₁) → Hom(F₁E₁,E₂F₂),
R(v) = (η₂ ▷ F₁E₁);(E₂ ◁ v ▷ E₁);(E₂F₂ ◁ ε₁).
```

`P(t)` is precisely `rouquierMate A₁ A₂ t`; `R(v)` is precisely the
reflected `rouquierMate` of `v`. These maps preserve the degree of their
argument. Expanding gives

```
Q(P(t)) = M_E₁E₂(t),       R(Q(u)) = u,       Q(R(v)) = v.  (8)
```

For the first equality the unit inserted by `Q` is `η₁` and the next
inserted unit is `η₂` nested inside it. Together they are `η_E₁E₂` above;
the two caps occur as `F₂ ε₁ E₂` followed by `ε₂`, hence are
`ε_E₁E₂`. For `RQ`, expansion leaves one `u`, the `E₂` unit/counit
snake and the `E₁` unit/counit snake; contract those two snakes.
For `QR` it leaves one `v`, the `F₂` snake and the `F₁` snake.
The contractions move only even units/counits past the lone argument.
Thus none of these three identities has a sign, even when the argument
is odd. In particular

```
R(M(t)) = P(t).                                    (9)
```

This is a comparison of the prescribed cup–crossing–cap composites, not
an appeal to cyclicity and not a new assumption about `F`.

## 4. Every field of the reflected local data

For a local datum of height `z`, put

```
E'_j=F_j, F'_j=E_j in HOpS(B),
x'_j=M(x_j),     t'=s M(t),     z'=z, p'=p.
```

The height is unchanged: this is a local construction on the same
indexed objects, not a weight-negating family. In particular the two
heights are still `h,h+2`. The parities are `p`, and the reflected right
adjunctions were constructed above.

Write `A=E₁ ◁ x₂` and `B=x₁ ▷ E₂`. Applying `M` to the original right
slide `t;A-s B;t=id` and using (4),(6) gives

```
s M(A);M(t) - M(t);M(B) = id.
```

This is exactly the reflected left slide
`(E'₁ ◁' x'₂);t' - s t';(x'₁ ▷' E'₂)=id`.
Applying `M` to the original left slide `A;t-s t;B=id` gives
`s M(t);M(A)-M(B);M(t)=id`, exactly the reflected right slide.
The scalar `s` in `t'` is therefore necessary, not optional.

For the square, `0=M(t;t)=s M(t);M(t)`, so `t';t'=0`.
On three strands write the two rebracketed crossings as `T₁,T₂`.
By (6) and the even associator calculation, their mates are exactly the
corresponding reflected whiskered crossings before the scalar `s`.
Applying (4) twice gives

```
M(T₂;T₁;T₂)=s³ M(T₂);M(T₁);M(T₂),
M(T₁;T₂;T₁)=s³ M(T₁);M(T₂);M(T₁).
```

Both sides of the reflected braid acquire the same further factor `s³`
from the three definitions of `t'`. Hence the braid holds, without
commuting two odd crossings. This verifies all square and braid inputs
of the local E theorem.

Put `f=P(t)`, and write `g_n` for the positive dotted cap or the negative
dotted cup, as appropriate. Equations (5), (2), (3), and (9) give

```
f_new = s f,
capD_new(n) = q(n) capD(n),
cupD_new(n) = q(n) cupD(n).                        (10)
```

For example the reflected cap is `M(x₁)^n ▷ E₁;ε₁`;
replace the power by `q(n)M(x₁^n)` and use (2). The reflected cup is
`η₂;E₂ ◁ M(x₂)^n`, and (3) gives the other formula. These are ordered
powers; no commuting of dots on distinct strands is used.

If `(f_inv,g_inv(n))` are the supplied inverse components, define

```
f_inv_new = s f_inv,      g_inv_new(n) = q(n) g_inv(n).  (11)
```

This verifies *both* inversion structures, at height zero as well:
`f_new;f_inv_new` and its reverse have coefficient `s²=1`;
`g_new(n);g_inv_new(n)` and its reverse have coefficient `q(n)²=1`.
Every off-diagonal component is its old zero multiplied by `s q(n)`
or `q(m)q(n)`. For a diagonal identity component `m=n`, its factor is
`q(n)²=1`. Therefore `total`, `ff`, `fg`, `gf`, and `gg` hold in both
the row and column orientations. The component parity is unchanged
(`p` for the crossing, `np` for the identity summand), since all scalars
are even. Components outside the finite window are scaled by the same
formula; no extra inverse identity outside the window is needed.
This constructs every field of the mirrored `SuperRouquierLoc`.

## 5. Identification of canonical cups and caps

Since vertical composition is unchanged in `HOpS`, equations (10)–(11)
and the actual piecewise definitions in `RouquierLeftCupCap` give

```
sigL_new = s sigL,
cupN_new(n) = q(n) cupN(n),   capN_new(n) = q(n) capN(n),

cupL_new(z) = a(z) cupL(z),
 a(z) = q(z-1)       if z>0,
        s q(-z)      if z≤0,

capL_new(z) = b(z) capL(z),
 b(z) = q(-z-1)      if z<0,
        s q(z)       if z≥0.                       (12)
```

In the zero branches the unused `cupN`/`capN` are zero on both sides.
For `z≤0` the cup is `cupD(-z);sigL`, yielding the extra `s`; for `z≥0`
the cap is `-(sigL;capD(z))`, yielding the same extra `s` without
changing its leading minus. This derives the normalization rather than
selecting it to fit the triangle.

The product relevant to the edge `E₂` is

```
a(h+2)b(h) = s^(h+1) = (-1)^(σσ).                 (13)
```

Here is the all-height exponent calculation. If `h≥0`, its exponent is
`choose(h+1,2)+1+choose(h,2)=h²+1`, whose difference from `h+1` is
`h(h-1)`, an even integer. If `h≤-2`, the exponent is
`1+choose(-h-2,2)+choose(-h-1,2)=1+(h+2)²`;
subtracting `h+1` gives `h(h+3)+4`, again even. If `h=-1`, both
factors are `q(0)=1`. Finally `σ²=σ=p(h+1)` in `Z/2`, so the last
equality in (13) holds. This is a symbolic parity argument for every
height, not finite-height evidence.

## 6. Apply the E theorem and read back the F composite

All hypotheses of the existing *local* E theorem have now been verified
for `L_new,U_new`, with the original value of `h`. It gives

```
ρ'⁻¹_F₂ ; (F₂ ◁' U_new.cupL) ; α'⁻¹_F₂,E₂,F₂ ;
                    (L_new.capL ▷' F₂) ; λ'_F₂
   = e(h) id_F₂.
```

Substitute the explicitly defined opposite unitors, associator and
whiskers from §3. This is

```
λ⁻¹_F₂ ; (U_new.cupL ▷ F₂) ; α_F₂,E₂,F₂ ;
                    (F₂ ◁ L_new.capL) ; ρ_F₂
   = e(h) id_F₂.
```

By (12) its left side is `a(h+2)b(h) Z_F`; extracting these even scalar
factors introduces no super interchange. By (13) that coefficient is
`(-1)^(σσ)`, an involutive unit. Multiplying by it proves (1).
This identifies the canonical F map, unlike transferring only an equality
between scalar identities through a right adjunction.

Consequently the existing `LeftZigzags` obligation is mathematically
satisfied with the explicit unit

```
c(h) = (-1)^(σσ) e(h),       c(h)⁻¹=c(h).
```

The existing E result is `Z_E=e(h)id_E=(-1)^(σσ)c(h)id_E`.
Normalizing the cap by `c(h)⁻¹` produces the shifted left adjunction in
the existing API. This last normalization is a consequence, not a change
to any generator used to prove (1).

## Formalization boundary

No Lean declaration is added by this document. The missing implementation
is the generic even-right-adjunction transposition calculus (2)–(9),
the super horizontal opposite, and the explicit mirrored local structure
(10)–(12). The mathematical argument above supplies those identities and
all scalar coefficients; they must still be checked in the kernel before
claiming `leftZigF` or `LeftZigzags` as a proved Lean theorem. It does not
construct a nonzero odd inversion model, a multicolour action, or a
nondegeneracy proof.