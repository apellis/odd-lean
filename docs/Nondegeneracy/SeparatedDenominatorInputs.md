# Separated denominator inputs on content products

Status: full build with warnings as errors, axiom audit and concrete consumers passed before research integration in #767.

The coefficient and braid algebra require units of y−x (even colour) and
x²−y² (odd colour). The older CrossCoeffInputs supplies these from an
invertible probe dot and a nilpotent reservoir dot as whole endomorphisms.
Fixed-content reservoir bounds do not supply a single exponent on an infinite
weight fibre, and formal sector labels do not restrict the internal content
blocks of the full Hom category.

CrossDenominatorUnits records the actual unit properties. The generic
coefficient, slide, braid and supernaturality chain uses those weaker inputs.
The old CrossCoeffInputs, its of_factor criterion and coefficient/braid
producers remain as corollaries through the explicit toDenominatorUnits map.

ProductDenominatorUnits assembles actual product endomorphism units from
component units, deriving the even difference and odd square difference/sum
from componentwise nilpotence. Its infinite-product module consumer tests
these identities. superfunctorEnd_isUnit and superfunctorProductEnd_isUnit
lift objectwise units to actual even natural inverses, preserving the existing
functor and target product. No uniform exponent is introduced. These constructions are full-CI verified in #794; their actual normalized
full-ELV postdot specialization and commutation follow in #801. The Sigma/SwappingReservoir mate invertibility
producer still has its original strong hypotheses; its positive/square-norm
and cap comparisons require a separate componentwise refactor.

This refactor does not construct the full factor or swapped action and does
not establish nondegeneracy.
