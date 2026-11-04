# Distinct left rotation from the cup identity

Brundan–Ellis, Lemma 7.1, (7.2), gives the cup identity used in the
positive-height range; Proposition 6.2, (6.6), prescribes the corresponding
left crossing. This note records the generic contraction needed to pass
from the former identity to invertibility of the prescribed left mate.
The canonical factor action must still establish the cup identity.

Use the notation of `SKM.leftCrossMate`: shifted left adjunctions
`A_d : F_d ⊣ E_d` and `A_a : F_a ⊣ E_a` have unit and counit degrees
`σd` and `σa`, and `T : E_d E_c → E_b E_a`. For a homogeneous
`l : E_c F_a → F_d E_b` of degree `p`, suppose that

```
λ(E_c)⁻¹ ; (unit_d ▷ E_c) ; α(F_d,E_d,E_c) ; (F_d ◁ T) ; α(F_d,E_b,E_a)⁻¹
  = q · (ρ(E_c)⁻¹ ; (E_c ◁ unit_a) ; α(E_c,F_a,E_a)⁻¹ ; (l ▷ E_a)).
```

Whisker this identity on the right by `F_a`, then compose with
`α(F_d E_b,E_a,F_a)`, `(F_d E_b) ◁ counit_a`, and `ρ(F_d E_b)`.
The left side is the literal unit–crossing–counit word defining the left
mate. On the right, the super interchange of `l` with `counit_a` gives
`(-1)^(σa p)`. The remaining cup and cap contract by the triangle on
`F_a`, which is the identity in `ShiftedSuperAdjunction`. Thus

```
leftCrossMate A_d A_a T = q · (-1)^(σa p) · l.
```

No factor `(-1)^σa` is contributed by this contraction: that factor
belongs to the other, `E_a` triangle. If `q` is a unit and `s` is an
inverse of `l`, the inverse of the left mate is
`q⁻¹ · (-1)^(σa p) · s`. These statements are the declarations
`SKM.leftCrossMate_eq_of_cup_pitchfork`,
`SKM.leftCrossMate_inv_products_of_cup_pitchfork`, and
`SKM.leftCrossMate_isIso_of_cup_pitchfork` in
`OddMath/SKM/RouquierDistinctLeftCupRotation.lean`.

The paired consumer uses the identity superfunctor of the nonzero
one-object rational supercategory, even identity adjunctions,
`T = 2 id`, and `l = id`. Its cup identity and inverse hypotheses are
proved, and the resulting left mate has nonzero scalar component two.
Additional API examples specialize `σa = p = 1`, retaining the
coefficient `-2` and reciprocal coefficient `-1/2`.
