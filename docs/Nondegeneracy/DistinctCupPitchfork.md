# The strict distinct cup identity

Brundan–Ellis Lemma 7.1, (7.2), has a positive cup proof by the principal
test `pcu_a_gt`, the finite tests `pcu_b`, and the positive augmented
inverse `ext_EEF`. `SKM/RouquierDistinctCupPitchfork.lean` assembles these
tests for the raw cup words defined in `RouquierDistinctCupTests`.

For `a+i=b`, `a+j=c`, and `b+j=c+i=d`, assume
`d_ij < h_i(b)`. Then `h_i(d)=h_i(b)-d_ij>0`. The two words are
`distinctCupLeft`, obtained from the lower cup and the upward crossing,
and `distinctCupRight`, obtained from the upper cup and the inverse of
the specified distinct right mate. The principal test of each word is
zero. After closing the finite cap row numbered `n` by the right
unitor, their values are respectively

```
t_ij · δ[n = h_i(d)-1] · id(Ej),
       δ[n = h_i(d)-1] · id(Ej).
```

The left row uses the dotted-cap mate identity and the original upward
quadratic relation. The two dot-slide signs cancel before the quadratic
row is evaluated. Consequently the coefficient is `t_ij`. Cancelling
the right unitor and applying `distinctCup_hom_ext_of_nonneg` gives
`distinctCupLeft_eq_of_gt`:

```
distinctCupLeft = t_ij · distinctCupRight.
```

The lower local inverse is centered at `b`, and the upper local inverse
at `d`. The strict range suffices for the remaining left-mate
invertibility range: the complement of
`h_i(a) ≤ max(d_ij-1,0)` has `h_i(a) ≥ d_ij` and `h_i(a)>0`, while
`h_i(b)=h_i(a)+2>d_ij`. Thus the shifted-zero boundary branch of the cup
identity is not an additional input to this application.

The paired consumer applies the identity to the canonical cyclotomic
factor family of the connected both-odd Boolean datum, with all edge,
parameter and strict height hypotheses constructed. It also retains
nonzero vacuum append vectors in both colours and audits all owned
declarations against the standard axiom allowlist.
