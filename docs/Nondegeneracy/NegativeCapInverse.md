# Identifying the prescribed negative-height cap

SwappedVacuumNonpositiveBubbles §3 identifies the extreme inverse cap
using its forward tests, rather than choosing a cap to force its moments.
`SwappedVacuum/NegativeCapInverse` makes this step explicit.

For the given cup-window inverse `[j; B]` of `[s,u_0,...,u_(h-1)]`, its
identity `j;s + sum B_n;u_n = 1` implies that the columns detect every
outgoing morphism. Thus a map annihilated by s and with the Kronecker
window of slot n equals the specified row B_n.

`negative_inverse_cap_eq_polynomial` applies this to the existing signed
mate-slide and coefficient-extraction calculations. If the monic probe
polynomial g has degree P<N and annihilates the probe dot, the last row
of the given augmented inverse is exactly `g(y);ell`. The extraction
window and the polynomial's parity support are explicit inputs, to be
supplied by the chosen factor construction. No bubble-value premise or
alternative inverse is introduced.

The producer and concrete consumer pass strict scoped checking, including
all six owned standard-axiom audits. The consumer tests
N=2, P=1 over rational modules, with a nonzero nilpotent reservoir dot,
a nontrivial invertible augmented matrix, and a proved nonzero inverse
row. Full integration remains a separate gate.
