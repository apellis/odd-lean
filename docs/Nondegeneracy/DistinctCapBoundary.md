# The zero-height principal cap test

The zero-height branch of Brundan–Ellis Lemma 7.1 (`pf_a`) differs from
strictly negative height: a boundary contraction survives. Its coefficient
must be retained before normalizing the canonical left adjunction.

The local identity `sig_capL_of_zero` specializes the checked dotted
cap relation at exponent zero. The prescribed equal-colour right mate
followed by the raw inverse-defined left cap is exactly the right counit.

For disconnected distinct colours, the mixed-braid correction sums are
empty. `distinctMixedBraidRight_cap_of_zero_disconnected` substitutes the
local boundary counit, applies the rectangular cap pitchfork, and then
uses the actual disconnected quadratic relation. The surviving scalar
is `t_ji = t_ij`. `distinctMixedBraidLeft_cap_of_zero_disconnected` uses
the mixed-braid equality to obtain the same first-word value. These are
raw cap values; no extra cap compatibility premise is introduced.

For connected colours at height zero before the `j`-step, the subsequent
height is `-d_ij`. The second mixed word vanishes. The monomial cap
calculation kills all interior correction terms. In the leading sum,
only zero source-dot exponent survives, with final exponent `d_ij - 1`;
its coefficient is exactly `t_ij`. The proposed connected attachment is
in `RouquierDistinctConnectedCapBoundary`, separately from the
disconnected calculation.

The disconnected boundary producer and its constructed two-odd consumer
pass strict checks and the standard-axiom audit of all seven owned
declarations. The connected boundary and its consumer are being checked.
The disconnected consumer retains a nontrivial leading parameter equal
to 2, proves both height conditions, and retains nonzero probe append
vectors. The connected consumer uses asymmetric off-diagonal entries.
Neither calculation alone supplies every finite-column test, the
positive-height argument, or canonical left-mate invertibility.
