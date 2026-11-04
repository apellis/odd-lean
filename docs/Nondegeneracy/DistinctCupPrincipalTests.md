# Principal tests for the distinct cup pitchfork

Brundan–Ellis, Lemma 7.1, the strict branch `pcu_a_gt` of (7.2), tests
the two cup words through the distinct right crossing and the positive
augmented inverse. `SKM/RouquierDistinctCupTests.lean` carries out these
principal tests in a Rouquier multicolour family.

Write `a+i=b`, `a+j=c`, and `b+j=c+i=d`. The lower local object is
centered at `b`, with edges `hi : a+i=b` and `hupper : b+i=e`; the upper
one is centered at `d`, with edges `hji : c+i=d` and `hnext : d+i=f`.
The raw left cup word is

```
λ(Ej)⁻¹ ; (cupL_b ▷ Ej) ; α(Fi,Ei,Ej) ;
  (Fi ◁ crossing(j,i)) ; α(Fi,Ej,Ei)⁻¹.
```

The raw right cup word is `ρ(Ej)⁻¹ ; (Ej ◁ cupL_d)` followed by the
inverse of `distinctCupTarget`. These are `distinctCupLeft` and
`distinctCupRight`. Their source is `Ej : b→d`, and their common target
is `(Fi : b→a ; Ej : a→c) ; Ei : c→d`.

At positive shifted height the right principal test is zero by
`cupL_sig`. For the left test, `distinctCupLeft_principal_eq` identifies
the literal composite with the second mixed braid word preceded by the
lower cup. The first mixed braid word vanishes by the lower
`cupL_sig`. If `d_ij < h_i(b)`, every leading-dot exponent `s` in the
mixed-braid correction satisfies `s < d_ij < h_i(b)` and misses the
Kronecker boundary `h_i(b)-1`. Thus `cupL_capD` kills every correction
monomial, proving `distinctCupLeft_principal_of_gt` without assuming a
cup pitchfork relation.

The paired consumer uses the canonical cyclotomic factor family for
the connected, both-odd asymmetric Boolean datum. It constructs both
edge orientations and strict heights explicitly, applies both principal
tests, and retains nonzero vacuum append vectors in both colours. An
owner-module audit checks every declaration against the standard axiom
allowlist. The finite cap rows are separate inputs to positive cup
detection; these principal tests alone do not assert the cup identity.
