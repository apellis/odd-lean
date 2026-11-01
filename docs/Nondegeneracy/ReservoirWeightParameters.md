# Parameters and restriction on the pairing extension

ReservoirWeights already constructs the datum Xhat = X × (I → ℤ), with root (α_i,0), coroot h_i(x)+z_i, and cofinal balanced highest-weight pairings. ReservoirWeightRestriction already restricts a RouquierFamily along x ↦ (x,0), inheriting its exact E/F/dot/crossing/adjunction/local-inverse fields.

ReservoirWeightParameters supplies the remaining parameter and coherence transport. Its scalar extension uses the identical t and s values; its supplied c-unit extension is c_hat((x,z),i)=c(x,i). In particular it retains original weights in the common coroot kernel. The symmetrizer and homogeneous parameter support are preserved. ParameterTwist commutes with extension, so the algebra/action parameter distinction is retained rather than collapsed.

The multicolour restriction theorem reuses the existing restricted factor family and transports all seven RouquierMulticolour fields, including the corrected braid and distinct-colour mate inverse. Original heights, dot parities, ipar and supplied units are preserved along (x,0).

The consumer uses an odd one-colour datum on ℤ×ℤ whose coroot ignores the second original coordinate, with supplied units that differ on two original weights with the same coroot. It also checks parameterTwist identification and the multicolour restriction interface, and audits every owned declaration.

This transports already-constructed factor data; it does not construct the remaining full-ELV inverse/coherence fields or assert a completed concrete factor family. No faithful inclusion theorem for the presented categories is assumed.
