# Detecting the distinct cup pitchfork

`RouquierDistinctCupDetection` ports the nonnegative-height detection in
Brundan–Ellis Lemma 7.1 (7.2), using `Lemma71Cup.ext_EEF` through the factor
Rouquier API. `RouquierFamily.distinctCupTarget` is the prescribed distinct
right mate followed by the target associator; its invertibility follows
from `RouquierMulticolour.invNe`. The theorem
`distinctCup_hom_ext_of_nonneg` detects equality from the principal test
and every finite cap-row test of the positive augmented inverse.

The producer and paired consumer pass strict checks, with the three owned
declarations audited against the standard axiom allowlist. The consumer
uses the constructed two-odd probe family at positive and zero shifted
heights, proves all principal and row hypotheses, and retains nonzero
vacuum append vectors.

This is a detection theorem. Evaluation of its tests, and the resulting
canonical left-mate identity, remain open. No left-mate invertibility or
pitchfork equality is assumed by the detection theorem.
