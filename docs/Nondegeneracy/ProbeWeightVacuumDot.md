# The raw whole-weight vacuum dot in the cap source chart

This is the dot-coordinate step needed by SwappedActionAssembly F2 and
SwappedVacuumNonpositiveBubbles §1 (2).

`ELVProbeWeightVacuumDot.vacuumLoopDot` is the empty-content component
of the chosen whole-weight induction dot, right-whiskered by the chosen
restriction, at the original regular probe. It is the raw dot used in
the pre-Hom construction.

`vacuumLoopDot_source` states

```
vacuumLoopDot ≫ vacuumCapSourceIso.hom
  = vacuumCapSourceIso.hom ≫ ProbeVacuumCap.moduleDot.
```

The four factors are exactly those of the cap source comparison. Their
commuting squares use, in order, the whole-weight successor dot formula,
the inverse of the even append upper-loop comparison, empty-content
forgetting, and the regular-input identification. The composition is
proved as four typed commuting squares. There is no dot compatibility
or moment premise.

The helpers `upperLoop_dot` and `forgetEmpty_upper_dot` retain their
full module-map equalities before selecting the regular probe. The
paired consumer applies the full source square to both odd colours of
the asymmetric fixture, checks the given module dot polynomial, and
retains the nonzero vacuum vector.

The raw pre-Hom source shift must also be retained when using this
square inside the padded Dx series. In particular the raw dot differs
from the unsigned transported module dot by its source-shift Koszul
factor, as recorded in `shiftedPreDot_coordinates`.
