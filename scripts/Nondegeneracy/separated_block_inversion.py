"""Exact tests of the conditional separated-factor matrices.

Tests the ordered block equations, not superfunctor coherence or a BE2 action.
The first factor is a pure nilpotent cup/cap block. The second is an arbitrary
background companion satisfying the stated factor inversion and dot slide.
"""
from fractions import Fraction as F
import json


def eye(n): return [[F(i == j) for j in range(n)] for i in range(n)]
def zeros(m, n): return [[F(0) for _ in range(n)] for _ in range(m)]
def mul(a, b):
    return [[sum((a[i][k] * b[k][j] for k in range(len(b))), F(0))
             for j in range(len(b[0]))] for i in range(len(a))]
def add(a, b): return [[x + y for x, y in zip(r, s)] for r, s in zip(a, b)]
def scale(a, c): return [[c * x for x in r] for r in a]


def inv(a):
    n = len(a)
    z = [[F(v) for v in row] + eye(n)[i] for i, row in enumerate(a)]
    for j in range(n):
        pivot = next((i for i in range(j, n) if z[i][j]), None)
        if pivot is None: raise ValueError('singular matrix')
        z[j], z[pivot] = z[pivot], z[j]
        c = z[j][j]; z[j] = [v / c for v in z[j]]
        for i in range(n):
            if i != j:
                c = z[i][j]; z[i] = [v - c * w for v, w in zip(z[i], z[j])]
    result = [row[n:] for row in z]
    assert mul(a, result) == eye(n) == mul(result, a)
    return result


def power(a, s):
    if s < 0: return power(inv(a), -s)
    r = eye(len(a))
    for _ in range(s): r = mul(r, a)
    return r


def factor(h, q):
    """Return x,y,sigma,u,v satisfying sigma*x=u*v+q*y*sigma."""
    A = [[F(2), F(1)], [F(1), F(1)]]
    w, c = [[F(1)], [F(2)]], [[F(2), F(-1)]]
    n, b = 2, abs(h)
    if h == 0:
        y, u, v = A, w, c
        x = add(scale(y, q), mul(u, v))
        sigma = eye(n)
    else:
        T = zeros(n + b, n + b)
        for i in range(n):
            for j in range(n): T[i][j] = A[i][j]
        if h > 0:
            for i in range(n): T[i][n] = w[i][0]; T[-1][i] = c[0][i]
            for j in range(b - 1): T[n + j][n + j + 1] = F(1)
            for j in range(b): T[-1][n + j] = F(j + 1)
            x, y, u = T, scale(A, q), w
            sigma = [eye(n)[i] + [F(0)] * b for i in range(n)]
            v = [[F(0)] * n + [F(1)] + [F(0)] * (b - 1)]
        else:
            for i in range(n): T[i][-1] = w[i][0]; T[n][i] = c[0][i]
            for j in range(b - 1): T[n + j + 1][n + j] = F(1)
            for j in range(b): T[n + j][-1] += F(j + 1)
            x, y, v = scale(A, q), T, scale(c, -q)
            sigma = eye(n) + zeros(b, n)
            u = [[F(0)] for _ in range(n)] + [[F(1)]] + [[F(0)] for _ in range(b - 1)]
    assert mul(sigma, x) == add(mul(u, v), scale(mul(y, sigma), q))
    inv(x); inv(y)
    if h >= 0:
        Q = sigma + [mul(v, power(x, j))[0] for j in range(h)]
        inv(Q)
    else:
        cups = [mul(power(y, j), u) for j in range(-h)]
        P = [row + [col[i][0] for col in cups] for i, row in enumerate(sigma)]
        inv(P)
    return x, y, sigma, u, v


def total_matrix(hA, hB, q):
    x, y, sigma, u, v = factor(hB, q)
    aX, aY = max(hA, 0), max(-hA, 0)
    bX, bY = len(x), len(y)
    h = hA + hB
    rows, cols = aY + bY + max(h, 0), aX + bX + max(-h, 0)
    assert rows == cols
    M = zeros(rows, cols)
    for i in range(bY):
        for j in range(bX): M[aY + i][aX + j] = sigma[i][j]
    # C=sum q^r u_A,r v_B,-r-1; D=-sum q^(r+1) u_B,-r-1 v_A,r.
    for r in range(aY):
        row = mul(v, power(x, -r - 1))[0]
        for j in range(bX): M[r][aX + j] = q**r * row[j]
    for r in range(aX):
        column = mul(power(y, -r - 1), u)
        for i in range(bY): M[aY + i][r] = -q**(r + 1) * column[i][0]
    if h >= 0:
        for s in range(h):
            row = aY + bY + s
            if s < aX: M[row][s] = F(1)
            cap = mul(v, power(x, s))[0]
            for j in range(bX): M[row][aX + j] = cap[j]
    else:
        for s in range(-h):
            column = aX + bX + s
            if s < aY: M[s][column] = F(1)
            cup = mul(power(y, s), u)
            for i in range(bY): M[aY + i][column] = cup[i][0]
    return M


# Known-bad raw-window shortcut: W_2 is zero, although the dot is invertible.
T = [[F(1), F(1)], [F(-1), F(0)]]
raw_window = power(T, -2)[1][1]
assert raw_window == 0
# The full a=2,b=1 matrix retains the additional cup column.
corrected = [[F(1), F(1), F(1)], [F(-1), F(0), F(0)], [F(1), F(0), F(1)]]
inv(corrected)
# Deleting its second-factor cup entry reproduces the singular shortcut.
mutant = [row[:] for row in corrected]
mutant[2][2] = F(0)
try:
    inv(mutant)
except ValueError:
    pass
else:
    raise AssertionError('deleted cup term was not detected')

cases = []
for q in (-1, 1):
    for hA in range(-4, 5):
        for hB in range(-4, 5):
            M = total_matrix(hA, hB, q)
            inv(M)
            cases.append((q, hA, hB))
print(json.dumps({'weight_sign_cases': len(cases), 'all_invertible': True,
                  'raw_beyond_window': int(raw_window), 'corrected_example_invertible': True,
                  'missing_cup_mutation_detected': True}))
