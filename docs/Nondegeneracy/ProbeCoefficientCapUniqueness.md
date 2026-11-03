# Coefficient cap uniqueness beyond the ground module

The transpose in `SwappedActionAssembly.md` (A14), evaluated on E(T₀),
uses the cap at F(E(T₀)). A comparison only at T₀ does not identify that
component, nor is T₀ faithful on all full old coefficients.

`probeContentCoefficientCap_eq_of_window` proves the same uniqueness
criterion on any scalar-evaluating module at an output with absent moving
colour, and for every prescribed coefficient row. The actual missing-unit
matrix inverse and selected scalar charts supply spanning. The window is
an intermediate premise, to be supplied by the local inverse equations;
there is no cap-compatibility assumption or extra inverse assumption.

The consumer uses the actual F(E(T₀)) at odd cutoffs 2 and 4. Its coefficient
condition is proved by the existing induction and restriction closure
lemmas. The given coefficient-cap window supplies every column premise.
It proves that F(E(T₀)) has nonzero identity from the original nonzero
cap, then proves every second-level coefficient cap nonzero using its
componentwise surjectivity. The module therefore remains occupied.

This does not yet instantiate local Rouquier records or the transpose.
It prevents replacing a required higher-input cap by an unjustified
conclusion from equality only on the original ground probe.
