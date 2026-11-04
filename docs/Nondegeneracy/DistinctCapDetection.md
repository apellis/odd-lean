# Detecting the distinct cap pitchfork

The nonpositive-height part of Brundan–Ellis Lemma 7.1 tests a cap
pitchfork against the principal column and every finite cup column of
an augmented inverse. `RouquierDistinctCapDetection` ports this detection
step from `Lemma71.ext_FEE` to the factor Rouquier API.

`RouquierFamily.distinctCapSource` is the prescribed right mate between
the two bracketed sources, including both associators. Its invertibility
uses only `RouquierMulticolour.invNe`. The theorem
`distinctCap_hom_ext_of_nonpos` then composes the existing negative
augmented-inverse detection with this invertible transport. It retains
every finite column and makes no assumption about a left mate or cap
pitchfork equality.

This detection step does not prove the two required families of tests.
Their evaluation still needs the rectangular mixed-braid correction and
its dotted boundary consequences in the factor API. In particular it
does not establish `LeftMateInvertible` or finish the pure-probe sideways
crossing. The producer and paired consumer pass strict checks; all three
owned declarations pass the standard axiom audit. The consumer uses the
constructed two-odd probe Rouquier family, proves every principal/finite
column test, and retains the proved nonzero vacuum append vectors.
