# Even negative-height input inverse

DeformedRouquierMatrix, section 4, uses the prescribed balanced crossing
together with its input contraction rows. For an even moving colour i and
arbitrary old words v,t, ELVEvenInputMatrix defines these maps directly:

- evenInputCapVector is (E, E X, ..., E X^(m-1)), with the descended
  evenInputContraction and evenCrossingInputDot.
- evenBoundaryKernelVectorEquiv and evenCrossingKernelVectorEquiv identify
  finite ordinary low coefficients with the actual boundary/crossing kernels.
- evenCapOnKernelVector_single identifies the restriction to each kernel
  basis column with the original long-lift cap recurrence.
- evenCapOnKernelVector_bijective uses the proved even below/pivot formulas
  and the shared finite triangular theorem after coordinate reversal. The
  diagonal is exactly evenOffDiagonalBoundaryLeadingEquiv.
- evenInputMatrix and evenInputMatrixEquiv are the crossing together with
  these cap rows, with a two-sided inverse.

The degree condition is outputSDegree=endpointQPDegree+m. The result includes
m=0. Coefficients retain the complete arbitrary Old(v,t) module over the
supplied commutative ring, with no field, dimension, flatness, faithful
action, source-basis assumption or presumed cap/crossing inverse.

The producer and paired concrete consumer pass scoped builds with warnings
as errors. The consumer uses mixed-parity asymmetric Cartan data, distinct
endpoint orders, positive cutoffs, three cap rows, actual zero and unit
pivots, and both inverse identities. The zero-cap edge is also instantiated.
It audits all thirty-four matrix declarations, seventeen shared coordinate
declarations and nine finite triangular declarations. The underlying raw
operator and pivot producers and their consumers also pass scoped checks.
Full CI and the global audit remain integration gates.

The categorical source for an even moving colour uses coefficient(0), not
the odd coefficient(1) source comparison. The raw contraction has the
negative of the ordinary counit on representatives, while its input dot
has the ordinary even dot action. Identifying that categorical map and the
ordered-mate first row remains a separate comparison; none is assumed by
this raw inverse.
