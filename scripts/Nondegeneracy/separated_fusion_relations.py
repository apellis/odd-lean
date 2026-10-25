# /// script
# requires-python = ">=3.10"
# dependencies = ["sympy==1.14.0"]
# ///
"""Exact separated-spectrum affine checks, not a categorical action.

The adjacent odd example is the symmetric Cartan matrix [[2,-2],[-2,2]]
with Q_ij(u,v)=u^2+v^2. Both exterior generators belong to the reservoir.
The probe has odd dot y with y^2=1 and no exterior coefficient.
Run with uv run --no-project --script and this file's path.
"""
from itertools import permutations
import sympy as s


def tensor(*args):
    return s.kronecker_product(*args)


def reservoir():
    d = s.Matrix([[0, 0], [1, 0]])
    p = s.diag(1, -1)
    z = s.zeros(2)
    x = s.BlockMatrix([[z, z], [s.eye(2), -d]]).as_explicit()
    delta = tensor(p, d)
    parity = tensor(p, p)
    assert x**2 + x*delta == s.zeros(4)
    assert x**3 == s.zeros(4) and delta**2 == s.zeros(4)
    return x, delta, parity


def cross_polynomials():
    """Extremal-term tests, with a nonsemisimple invertible probe."""
    # Q[z,w]/(z^3,(w-2)^2) tensor Lambda(di,dj).
    z = s.zeros(3)
    z[1, 0] = z[2, 1] = 1
    w = s.Matrix([[2, 0], [1, 2]])
    d = s.Matrix([[0, 0], [1, 0]])
    p = s.diag(1, -1)
    Z = tensor(z, s.eye(2), s.eye(4))
    W = tensor(s.eye(3), w, s.eye(4))
    D = tensor(s.eye(6), d, s.eye(2))
    E = tensor(s.eye(6), p, d)
    one = s.eye(Z.rows)
    zero = s.zeros(Z.rows)
    assert D*E != zero and D*E + E*D == zero
    # Ordinary dots at even colours; squared dots at odd colours.
    cases = {
        'even-even A2, Q=u+v': Z+W,
        'even-odd B2, Q=u+v^2': Z+W,
        'odd-even B2, Q=u^2+v': Z+W,
        'odd-odd affine A1, Q=u^2+v^2': Z+W,
        'even-even affine A1, Q=3u^2+5uv+7v^2': 3*Z**2+5*Z*W+7*W**2,
    }
    for name, Q in cases.items():
        inv = Q.inv()
        assert Q*inv == inv*Q == one
        assert (Q*D*E).rank() == (D*E).rank()
        print(name, 'dimension', Q.rows, 'det', Q.det(),
              'exterior-product rank', (D*E).rank(), flush=True)


def adjacent_odd_shuffle():
    """One reservoir i, one probe i, one reservoir j; all six shuffles.

    This is a representation of the indicated three-strand affine corner.
    It does not supply cyclotomic induction or categorical mates.
    """
    x, d, p = reservoir()
    y = s.Matrix([[0, 1], [1, 0]])
    py = s.diag(1, -1)
    X = {'a': tensor(x, s.eye(2), s.eye(4)),
         'b': tensor(p, y, s.eye(4)),
         'c': tensor(p, py, x)}
    D = tensor(d, s.eye(2), s.eye(4))
    E = tensor(p, py, d)
    P = tensor(p, py, p)
    n = P.rows
    one, zero = s.eye(n), s.zeros(n)
    colour = {'a': 'i', 'b': 'i', 'c': 'j'}
    words = tuple(permutations('abc'))
    grading = {w: (-1)**sum(w[i] > w[j] for i in range(3)
                            for j in range(i+1, 3))*P for w in words}
    assert D*E != zero and D*E+E*D == zero
    assert X['a']**3 == X['c']**3 == zero and X['b']**2 == one
    for a in X:
        assert X[a]*D+D*X[a] == X[a]*E+E*X[a] == zero
        for b in X:
            if a != b:
                assert X[a]*X[b]+X[b]*X[a] == zero

    def crossing(w, r):
        a, b = w[r:r+2]
        target = list(w)
        target[r], target[r+1] = b, a
        target = tuple(target)
        if colour[a] != colour[b]:
            Q = X[a]**2+X[b]**2
            return {target: P if colour[a] < colour[b] else Q*P}
        diff = X[a]**2-X[b]**2
        diag = (X[a]-X[b])*diff.inv()
        norm = (X[a]**2+X[b]**2)*diff.inv()**2
        return {w: diag, target: P if a < b else -norm*P}

    def path(w, rs):
        out = {w: one}
        for r in rs:
            nxt = {}
            for u, mat in out.items():
                for v, cross in crossing(u, r).items():
                    nxt[v] = nxt.get(v, zero)+cross*mat
            out = nxt
        return out

    nonzero_braids = 0
    for w in words:
        for r in (0, 1):
            same = colour[w[r]] == colour[w[r+1]]
            for v, T in crossing(w, r).items():
                rhs = one if same and v == w else zero
                assert T*X[w[r]]+X[v[r+1]]*T == rhs
                assert X[v[r]]*T+T*X[w[r+1]] == rhs
                far = 2 if r == 0 else 0
                assert T*X[w[far]]+X[v[far]]*T == zero
                assert grading[v]*T+T*grading[w] == zero
                assert T*D+D*T == T*E+E*T == zero
            square = path(w, (r, r))
            for v in words:
                rhs = X[w[r]]**2+X[w[r+1]]**2 if v == w and not same else zero
                assert square.get(v, zero) == rhs
        left, right = path(w, (0, 1, 0)), path(w, (1, 0, 1))
        for v in words:
            correction = (X[w[2]]-X[w[0]]) if v == w and colour[w[0]] == colour[w[2]] else zero
            assert left.get(v, zero)-right.get(v, zero) == correction, (w, v)
            nonzero_braids += int(correction != zero)
    print('adjacent odd affine A1: six labelled shuffles, block dimension', n,
          'nonzero braid corrections', nonzero_braids,
          'exterior-product rank', (D*E).rank(), flush=True)


if __name__ == '__main__':
    cross_polynomials()
    adjacent_odd_shuffle()
    print('PASS exact affine tests; categorical mixed inversion is not inferred')
