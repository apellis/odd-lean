"""Exact diagnostics for graded odd spectral blocks, not an SKM action.

Run: python3 scripts/Nondegeneracy/odd_spectral_blocks.py
Requires SymPy. All computations are over Q. The two exterior parameters are
independent; the odd Clifford dot is invertible. Negative controls reject
ordinary scalar shifting, graded scalar eigenblocks and collapsed parameters.
"""
import sympy as S


def exterior_left(n, j):
    """Left exterior multiplication, basis indexed by subsets in bit order."""
    m = S.zeros(2**n)
    for mask in range(2**n):
        if not (mask >> j) & 1:
            swaps = (mask & ((1 << j) - 1)).bit_count()
            m[mask | (1 << j), mask] = (-1)**swaps
    return m


def require_failure(predicate, name):
    assert not predicate, "negative control unexpectedly passed: " + name
    print("negative control PASS:", name)


def main():
    c = S.Matrix([[0, 1], [1, 0]])
    pc = S.diag(1, -1)
    pe = S.diag(1, -1, -1, 1)
    ident = S.eye(8)
    parity = S.kronecker_product(pc, pe)
    x = S.kronecker_product(c, S.eye(4))
    d = [S.kronecker_product(pc, exterior_left(2, j)) for j in range(2)]
    assert x*x == ident
    assert parity*x == -x*parity
    for z in d:
        assert z*z == S.zeros(8)
        assert parity*z == -z*parity
        assert x*z == -z*x
    assert d[0]*d[1] == -d[1]*d[0]
    assert d[0]*d[1] != S.zeros(8)
    assert x*d[0]*d[1] == d[0]*d[1]*x
    require_failure(x*d[0]*d[1] == -d[0]*d[1]*x,
                    "one sign for moving past two independent odd coefficients")
    require_failure(d[0]*d[1] == d[0]*d[0], "collapse independent exterior parameters")

    ep, em = (ident+x)/2, (ident-x)/2
    assert ep*ep == ep and em*em == em
    assert ep*em == S.zeros(8) and ep+em == ident
    assert parity*ep*parity == em
    require_failure(parity*ep == ep*parity, "scalar spectral projector is even")
    assert ep*d[0] == d[0]*em
    assert ep*d[0]*ep == S.zeros(8)
    assert ep*d[0]*d[1]*ep != S.zeros(8)
    require_failure(ep*d[0]*d[1]*ep == (ep*d[0]*ep)*(ep*d[1]*ep),
                    "compression to one scalar eigenblock preserves products")

    # Two independent odd dots with commuting squares, not commuting dots.
    a = S.kronecker_product(c, S.eye(2))
    b = S.kronecker_product(pc, c)
    i4 = S.eye(4)
    assert a*b == -b*a and a*a == i4 and b*b == i4
    shifted = (a-i4)*(b-i4)+(b-i4)*(a-i4)
    assert shifted == 2*i4-2*a-2*b
    require_failure(shifted == S.zeros(4), "ordinary scalar shifts retain odd skew relation")
    ea, eb = (i4+a)/2, (i4+b)/2
    require_failure(ea*eb == eb*ea, "joint ordinary odd-dot spectral projectors commute")
    print("PASS: exact Clifford/exterior model, squared-dot grading, and six controls")


if __name__ == "__main__":
    main()
