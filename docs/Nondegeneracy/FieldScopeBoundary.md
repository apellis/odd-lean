# Field input and the scope of BE2 §8

The source target is Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, §8, the conjecture following Theorem 8.1 (PDF p.33).
The symmetrizability and scalar homogeneity assumptions introduced on
pp.8–9 apply to the remainder of the introduction. Section 9 introduces
these assumptions again with “Henceforth”; they are extra hypotheses
relative to the §8 conjecture.

`Datum` in `SKM/Basic.lean` requires a generalized Cartan matrix and the
odd-row evenness condition. It does not supply a `Symmetrizer`.
`Scalars.Homogeneous` in `SKM/Grading.lean` constrains the supported
nonzero interior coefficients; in particular it holds when all such
coefficients vanish. It does not imply existence of a positive symmetrizer.

For example, the all-odd Cartan pattern

```
  2  -2  -4
 -4   2  -2
 -2  -4   2
```

has even rows and the required generalized Cartan signs. Its symmetrizer
equations imply d₁=2d₂, d₂=2d₃ and d₃=2d₁, contradicting positivity.
This elementary calculation illustrates why a symmetrizer cannot be
silently inferred from the current datum and homogeneous-parameter APIs.
No additional Lean counterexample construction is claimed here.

The current swapped construction explicitly uses a positive symmetrizer,
including the coefficient-power induction-dot nilpotence input. Its intended
field endpoint must therefore retain that hypothesis: for fixed `D` and
`sy : Symmetrizer D`, prove `CharZeroFieldNondegeneracy D`.
This predicate already quantifies over every characteristic-zero field,
homogeneous `Sc` and supplied `CScalars Sc` for that same datum.

`nondegeneracyConjecture_of_charZeroField` is already proved and then gives
the ordinary commutative-ring conclusion with 2 invertible. It does not
change the datum or remove assumptions used to establish its field input.
There is no additional ground-ring descent obligation.

The remaining source-fidelity question is: what source-backed input removes
symmetrizability and the homogeneous-parameter restriction for the rest of
BE2 §8? Until such an input is supplied, retain the explicit hypotheses on
the field construction and track their removal separately. No replacement
proof route or exclusion of the broader target is chosen here.
