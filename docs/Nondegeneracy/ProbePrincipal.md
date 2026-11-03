# Probe principal entry

Brundan–Ellis, *Super Kac–Moody 2-categories*, Definition 1.5,
(1.13)–(1.14), requires comparison of the pure probe principal entry with
the prescribed local inverse data of the probe factor.

`ProbeReservoir.sigmaEntry_probe_mate` identifies the literal `(P,P)` to
`(P,P)` entry of the constructed sideways crossing with the cup–crossing–cap
mate of `homContentSuperAdjunction` and `homContentCrossing`. The source and
target charts are `probeCapFactorIso` and `probeCupFactorIso`. The adjunction
is the canonical inverse-defined left adjunction of the given factor. The
crossing retains its horizontal-reversal coefficient `-koszulSign p p`.
The result holds for every mixed coefficient datum `c`; it requires no
central inverse or comparison equation.

`ProbeReservoir.sigmaEntry_probe_coordinates` then composes these path
charts with the source and target shift-removal charts of
`homContentPreInverseSource` and `homContentPreInverseTarget`. In those
coordinates the entry is

```text
homPreGamma p H • ((-sigL) ▷ Z),
p = D.parity i,   H = D.h i (-P.muP t).
```

Here `sigL` is the leftward crossing of the specified factor local record.
The coefficient is `(-1)^p` at height zero and
`koszulSign p (p * (H mod 2))` otherwise. The exceptional height-zero sign
and the negative leftward crossing are not cancelled or replaced.

The consumer constructs both factors from the positive-level ELV family
with connected asymmetric two-odd parameters. It tests both comparisons
at each colour on a mixed sector and retains an explicitly nonzero
two-odd PBW coordinate in the input of the full identity Hom object. It
also tests both odd colours on concrete mixed zero-height sectors and
checks the exceptional coefficient is `-1`. Every owned declaration is
included in the allowlist axiom audit.

The principal comparison supplies the specified central matrix entry.
Construction of the augmented central inverse also needs the diagonal
rows and the two mixed bends; that inverse is a separate obligation.
