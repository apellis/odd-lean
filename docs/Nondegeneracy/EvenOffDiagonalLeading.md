# Even boundary leading maps on arbitrary old Homs

This is the parity-zero arbitrary-Hom transport in
[DeformedBoundaryDivision](DeformedBoundaryDivision.md), section 5.

The generic zero-section output-old transport is iterated through the
literal even moving dot. Precomposition by this source operator commutes
with arbitrary output arrows by associativity. The checked even extraction
recurrence carries the initial chronological-short error through every
iterate. Actual C0P factorization and generic C0 output covariance therefore
identify every row with the independently computed diagonal row:

    A_vt(single(d,b))(n) = Phi_v(d)(n) composed with oldTwist(p)(b).

Both old endpoints are arbitrary, including empty old Homs. No old basis
index, field, flatness or diagonal-corner sufficiency premise is supplied.

The diagonal bound and scalar-unit top then extend to every old coefficient.
The leading operator on Old(v,t) is

    appendQPProductUnit · oldTwist(p).

It is a linear equivalence because the scalar is a unit and total parity
twist is involutive. The balance twist p remains even though the moving
colour has parity zero. Negative height gives the entire zero row.

The proposed implementation is `ELVEvenOffDiagonalLeading`, with connected
mixed-data reversed-word/coefficient consumers and an empty-Hom equivalence
consumer. Source and consumers await checking. This supplies the actual
arbitrary-Hom leading input to module triangular division; it does not
assert an even categorical inverse or action.
