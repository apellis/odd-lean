# First odd polynomial-cap closure at nonpositive height

This extends the zero-height calculation in `CoefficientPowerPolynomialCap.md` to the first normalized candidate moment of `SwappedVacuumNonpositiveBubbles.md`, §§3–4. The maps remain the original signed dot, ordinary unit and prescribed inverse extraction row on literal A/T. Identification with the chosen mixed inverse cap is still separate.

Let P=2M≤N, with N>0 the reservoir cutoff, and d=N−P. The actual polynomial functional is λg(D), where g(T)=(T²+1)^M. Its first normalized closure is

    λ ∘ (D²+1)^M ∘ D^d ∘ u.

At negative height this is the candidate cap followed by d dots; at zero height d=0, giving the principal-inverse candidate closure. All underlying powers are nonnegative.

`polynomialCapMoment_nonpositive_first` expands the same finite binomial sum on every coefficient vector. Its top term is momentMap_N. Every lower term has exponent at most N−2 and is killed by the actual low inverse-row window. Consequently

    λ ∘ (D²+1)^M ∘ D^(N−2M) ∘ u = momentMap_N.

`polynomialCapMoment_nonpositive_first_odd` therefore gives the exact original left coefficient operator

    L_((-1)^(N+1) δ).

This retains the plus sign at odd reservoir cutoff and the minus sign at even reservoir cutoff. It does not infer the negative case by exchanging adjunctions, or supply an inverse cap or a bubble value as a hypothesis.

The consumer takes probe degree four and reservoir cutoffs four and five, testing zero and negative height in the same connected all-odd datum. Two independent exterior coefficients have a nonzero product in the actual quotient. The odd-cutoff negative-height closure acts by L_δ, with its nonzero value on the other odd direction fixing the original multiplication order. An inhomogeneous vector is checked as well. Every owned producer declaration is audited.

To identify these maps with the source-placed odd bubbles, the prescribed mixed maps, their slide and their inverse-cap normalization must still be attached. The existing principal and negative-cap recovery theorems explain the intended next identification; this computation assumes none of that mixed datum.
