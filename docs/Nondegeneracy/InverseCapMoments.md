# Coefficient extraction after the height-zero principal inverse

This is the polynomial step of the proposed nonpositive-height bubble
calculation, [SwappedVacuumNonpositiveBubbles, §§2–4](SwappedVacuumNonpositiveBubbles.md).
It supports research issue #345 and the bounded recovery construction in
[SwappedNondegeneracy, §4](SwappedNondegeneracy.md).

Work in a k-linear category. In functional order let x and y be the probe
and reservoir dots, s:X→Y the literal mate, u:V→Y and v:X→V its unit and
cap, and ell:Y→V normalized coefficient extraction. Assume N>0 and

    y s-q s x=u v,
    ell y^a u=0 (a<N-1),   ell y^(N-1)u=1.

For 0≤n≤N, induction on the slide gives

    ell y^n s=q^n ell s x^n + [n=N]v.

The proof preserves composition order. It does not move a coefficient or
parity comparison through a dot. Consequently it applies to q=1 and q=-1
in their independently prescribed homogeneous coordinates.

Let g(T)=sum_(n=0)^N c_n T^n be monic, with c_n q^n=c_n and g(x)=0.
Summing the displayed identity yields

    ell g(y)s=v.

If j=s^-1 is the prescribed principal inverse, its cap therefore satisfies

    v j=ell g(y),
    v j y^r u=sum_(n=0)^N c_n ell y^(n+r)u,  r≥0.

This proves the coefficient-extraction identification of the inverse cap;
the inverse cap is not chosen to have these moments. At even height zero
g(T)=(T-1)^N. At odd height zero g(T)=(T²+1)^(N/2) and q=-1, so the
support condition holds. The fake zeroth moment is separately 1: it is
not the r=-1 instance of the final formula. No overall minus sign should
be applied to the right-moment generating series.

The declarations in
`OddMath/QuiverHecke/SwappedVacuum/InverseCapMoments.lean` are
`slide_coefficient_window`, `principal_cap_polynomial`,
`principal_inverse_cap` and `principal_inverse_right_moment`.
The paired consumer `scripts/NonVacuity/SwappedInverseCapMoments.lean`
checks occupied rational module examples at N=P=1 and N=P=2. The degree-two
example uses a nonzero nilpotent reservoir dot, a companion probe dot for
(T-1)², and the literal coefficient-extraction window; every hypothesis is
proved. The consumer also audits all owned declarations against the
standard axiom allowlist.

This is an intermediate algebraic identification. It does not construct
the actual swapped vacuum, its coefficient-extraction functional or its
normalized adjunction, and it does not establish the complete generating
series. The next attachment must identify the actual homogeneous maps
with these endpoints and use the full monic-remainder moments of the
one-strand reservoir. The positive and negative height windows remain
separate from this principal-inverse case. Full CI remains the integration
gate; scoped checks do not establish the entire action or nondegeneracy.
