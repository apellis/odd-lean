#!/usr/bin/env python3
"""Exact polynomial checks for connected ELV coefficient transfer.

Commuting symbols x,d below encode the fixed normal order x^l*c_(n-l);
we never commute d past x. z is even. Separate parity checks account for
moving the whole polynomial past a distant odd crossing.
"""
import sympy as s


def run():
    x,z,d=s.symbols("x z d")
    for n in range(1,11):
        m=n//2
        chi=(s.Integer(1),)+s.symbols(f"c1:{m+1}")
        new=(s.Integer(1),)+tuple((chi[r] if r<=m else 0)+z*chi[r-1]
                                 for r in range(1,m+2))
        def f(degree,cs):
            return s.expand(sum((-1)**ell*x**ell*
                                (d if (degree-ell)%2 else 1)*cs[(degree-ell)//2]
                                for ell in range(degree+1)))
        residual=s.expand(f(n+2,new)-(x*x+z)*f(n,chi))
        expected=-x*d*chi[m] if n%2==0 else 0
        assert s.expand(residual-expected)==0
        # In even degree the new defining relation is z times the old one.
        if n%2==0:
            assert s.expand(d*new[-1]-z*d*chi[m])==0
            assert residual!=0  # dropping the old ELV relation is detected
        # Every summand has total parity n, so a distant odd crossing
        # moves across with ONE sign, including its coefficient sign.
        assert all((-1)**(ell+(n-ell)%2)==(-1)**n for ell in range(n+1))
        # Treating odd coefficients as even incorrectly changes that sign.
        assert any((-1)**ell!=(-1)**n for ell in range(n+1))
    print("PASS degrees 1..10: ELV degree+2 transfer and distant-crossing parity")
    print("PASS even-cutoff constraint maps to z times old constraint")
    print("PASS omitted-constraint and coefficient-sign negative controls")
    print("SCOPE: coefficient compatibility, not an SKM action or trace")


if __name__ == "__main__":
    run()
