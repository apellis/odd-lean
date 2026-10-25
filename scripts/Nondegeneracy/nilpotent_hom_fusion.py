#!/usr/bin/env python3
"""Exact obstruction to blockwise zero/zero Hom fusion.

This tests necessary upward relations, not a full categorical action.
See docs/Nondegeneracy/GeneralRoute.md. Only the Python standard library is used.
"""
from fractions import Fraction
from itertools import product


def zero(n, m=None):
    return [[0] * (n if m is None else m) for _ in range(n)]


def identity(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def add(a, b, sign=1):
    return [[x + sign * y for x, y in zip(r, s)] for r, s in zip(a, b)]


def multiply(a, b):
    return [[sum(x * y for x, y in zip(row, col)) for col in zip(*b)] for row in a]


def rank(a):
    a = [[Fraction(x) for x in row] for row in a]
    pivot = 0
    for j in range(len(a[0])):
        k = next((k for k in range(pivot, len(a)) if a[k][j]), None)
        if k is None:
            continue
        a[pivot], a[k] = a[k], a[pivot]
        c = a[pivot][j]
        a[pivot] = [x / c for x in a[pivot]]
        for k in range(pivot + 1, len(a)):
            c = a[k][j]
            if c:
                a[k] = [x - c * y for x, y in zip(a[k], a[pivot])]
        pivot += 1
        if pivot == len(a):
            break
    return pivot


def direct_sum(a, b):
    n, m = len(a), len(b)
    return [r + [0] * m for r in a] + [[0] * n + r for r in b]


def exterior_left(bit):
    """Left multiplication on the ordered basis 1,x,y,xy."""
    a = zero(4)
    for mask in range(4):
        if not mask & (1 << bit):
            sign = (-1) ** ((mask & ((1 << bit) - 1)).bit_count())
            a[mask | (1 << bit)][mask] = sign
    return a


def fusion_test():
    x, y = exterior_left(0), exterior_left(1)
    # Both ordered shuffle blocks; no restriction on the candidate crossing.
    X, Y = direct_sum(x, y), direct_sum(y, x)
    n = len(X)
    assert multiply(X, X) == multiply(Y, Y) == zero(n)
    assert add(multiply(X, Y), multiply(Y, X)) == zero(n)
    assert X != Y
    # Vectorize T -> T X + Y T. Unknowns are all n*n matrix entries.
    columns = []
    for i, j in product(range(n), repeat=2):
        t = zero(n)
        t[i][j] = 1
        columns.append(sum(add(multiply(t, X), multiply(Y, t)), []))
    equations = list(map(list, zip(*columns)))
    target = sum(identity(n), [])
    augmented = [r + [v] for r, v in zip(equations, target)]
    a, b = rank(equations), rank(augmented)
    assert b > a
    # The derived obstruction holds identically for every matrix unit T:
    # (TX+YT)X - Y(TX+YT) = TX^2 - Y^2T = 0,
    # while the right side for TX+YT=I would be X-Y != 0.
    assert add(X, Y, -1) != zero(n)
    print(f'shuffle dimension={n}; rank(T -> TX+YT)={a}; augmented rank={b}')
    print('NO crossing T satisfies TX+YT=I, even without parity restrictions')


def denominator_test():
    # Q[z,w]/(z^2,w^2) tensor Lambda(di,dj); basis z^a w^b delta_mask.
    basis = list(product(range(2), range(2), range(4)))
    index = {v: i for i, v in enumerate(basis)}
    n = len(basis)
    Z, W, D = zero(n), zero(n), zero(n)
    for col, (a, b, mask) in enumerate(basis):
        if a == 0:
            Z[index[(1, b, mask)]][col] = 1
        if b == 0:
            W[index[(a, 1, mask)]][col] = 1
        if mask == 0:
            D[index[(a, b, 3)]][col] = 1
    Q = add(Z, W)
    Q2, Q3 = multiply(Q, Q), multiply(multiply(Q, Q), Q)
    assert Q3 == zero(n)
    assert Q2 != zero(n)
    assert D[index[(0, 0, 3)]][index[(0, 0, 0)]] == 1
    assert rank(D) == 4
    print(f'adjacent-odd coefficient algebra dimension={n}; '
          f'ranks(Q,Q^2,Q^3)={rank(Q)},{rank(Q2)},{rank(Q3)}; '
          f'rank(delta_i delta_j)={rank(D)}')
    print('Q^3=0: making Q invertible makes 1=0; the exterior product is lost')
    # Separated control: replace the second squared coordinate by 1.
    # Keep both exterior variables in the reservoir base, not in a probe ELV factor.
    separated = add(identity(n), Z)
    inverse = add(identity(n), Z, -1)
    assert multiply(separated, inverse) == multiply(inverse, separated) == identity(n)
    assert multiply(D, separated) != zero(n)
    print(f'separated control Q=1+z has rank={rank(separated)} and inverse 1-z; '
          'the exterior product survives')


if __name__ == '__main__':
    fusion_test()
    denominator_test()
