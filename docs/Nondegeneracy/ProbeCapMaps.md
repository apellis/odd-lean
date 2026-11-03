# Inverse-defined caps on the regular vacuum probe

`ProbeVacuumCap.cap` specializes the native content coefficient cap to the
original regular height-zero probe T₀. Its source is the native FE(T₀)
module, and its target is T₀ itself. The selected FE chart, prescribed last
inverse row, and inverse fully faithful inclusion unit are all retained.
No arbitrary coefficient extractor or replacement probe module is supplied.

At positive probe cutoff P, `cap_mem` proves degree `(P-1)p`.
`cap_total_surjective` gives component surjectivity, and `cap_ne_zero`
proves the module morphism nonzero over any nontrivial ground ring. The
proof detects the original nonzero empty probe vector.

`groundRow` decodes the canonical empty component with the existing
`probeVacuumScalarEquiv`. Its scalar coordinate is surjective
(`groundRow_surjective`) and has the same degree (`groundRow_mem`), since
the original empty regular probe is entirely even.

The paired asymmetric rational two-odd-colour consumer uses levels one
and two. The actual native module cap is nonzero and odd, and its ground
row extracts one from a nonzero odd vector of its actual native FE source.

The exact total linear-map formula for the generic cap is the selected
operator chain used by the scalar inverse-row comparison. Binding that
formula to the ordinary probe's prescribed inverse row and to a separate
action's normalized left counit is not asserted here. Native dotted-unit
window recovery and the final mixed slide remain separate statements.
