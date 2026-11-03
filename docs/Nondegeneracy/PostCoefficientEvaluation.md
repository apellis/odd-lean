# Coefficient evaluation at an ELV output block

For the finite bend expansion in `SwappedHomInversion` §3 (3) and §4,
`elvPostEndEvaluation` evaluates a whole natural endomorphism on the
actual postinduced module and then projects to its chosen output block.
`elvPostEndEvaluation_of_mem` retains its prescribed homogeneous component.
`elvPostEndEvaluation_dot_isNilpotent` supplies the constructed reservoir
dot bound for every output block, in either parity. The bound may depend
on that block; no uniform nilpotence on the full weight product is assumed.

`elvPostCoefficient_even_expansion` combines this bound with the finite
geometric expansion after the evaluation homomorphism. It retains an
invertible supplied operator, its commutation with the chosen postdot,
and the coefficient equation as intermediate hypotheses. The evaluated
odd expansion is already available from `mixedCoefficient_odd_map_expansion`
using the same constructed bound. Identifying the supplied operator and
coefficient with the intended mixed crossing remains an attachment step;
this note does not claim that identification or the residual ideal closure.

The producer and concrete consumer pass strict scoped checks. The consumer
uses the actual empty-word representable array and its occupied successor
block, checks the constructed bound for both even and odd data, and applies
the even expansion with the identity operator and the constructed inverse
of the actual dot-minus-identity denominator. It audits all ten owned
declarations against the standard axiom allowlist.
