"""Finite formal coefficient checks; not an SKM representation or Lean proof."""
from collections import defaultdict
from itertools import product

checks = 0
for eps in (0, 1):
    t = (-1) ** eps
    for h in range(-9, 10):
        # Strip the common unit c^-1. Keys encode e_m ; barq_n.
        # Initialize directly from -t^h (S;L);e_h and fake bubbles.
        F = defaultdict(int)
        if h >= 0:
            F[h, 0] += t ** h
            for j in range(h):
                F[j, h-j] += (-t ** h) * (-t ** (h-j))
        for b in range(15):
            expected = {(b+h-n, n): t ** (b+h-n) for n in range(max(0, b+h+1))}
            assert dict(F) == expected, (eps, h, b, F, expected)
            checks += 1
            G = defaultdict(int)
            for (m, n), v in F.items():
                G[m+1, n] += t*v
            if b+h+1 >= 0:
                G[0, b+h+1] += 1
            F = G
print(f'Principal recurrence: {checks} cases passed')
parity_checks = 0
for eps in (0, 1):
    for p in (0, 1):
        for h in range(-9, 10):
            for b in range(15):
                for n in range(max(0, b+h+1)):
                    m = b+h-n
                    # Move source coefficient across S and e_m, then across q_n.
                    assert (eps*p*(1+m+n)-eps*p*(b+h+1)) % 2 == 0
                    parity_checks += 1
                for s in range(max(0, -h)):
                    n = s+b+h+1
                    assert (eps*p*(s+n)-eps*p*(b+h+1)) % 2 == 0
                    parity_checks += 1
print(f'Chronological coefficient signs: {parity_checks} cases passed')
remainder_checks = 0
for h in range(-15, 0):
    for B in range(-h):
        s = -h-1-B
        assert 0 <= s < -h
        for b in range(B+1):
            assert b+s+h+1 == b-B
            assert (b+s+h+1 == 0) == (b == B)
            remainder_checks += 1
print(f'Finite remainder anti-triangularity: {remainder_checks} entries passed')


def exterior_product(a, b):
    """Signed monomial product in two independent exterior generators."""
    if a & b:
        return (0, 0)
    inversions = sum(1 for i in range(2) for j in range(2)
                     if i > j and a & (1 << i) and b & (1 << j))
    return ((-1) ** inversions, a | b)


# Coefficient order is observable even though all entries supercommute.
p, d = 1, 2
assert exterior_product(d, p) == (-1, 3)  # target residual column: d*p
assert exterior_product(p, d) == (1, 3)   # source bubble suffix: p*barQ
assert exterior_product(d, p) != exterior_product(p, d)
assert exterior_product(d, p)[0] != 0
assert exterior_product(p, p) == (0, 0)
assert (-1) ** (p | d).bit_count() == 1  # parity fixes the mixed product
print('PASS: ordered mixed exterior coefficients retained; opposite orders distinguished.')


def mul(a, b):
    sign, mask = exterior_product(a[1], b[1])
    return (a[0] * b[0] * sign, mask)


def theta(a, power):
    return (a[0] * (-1) ** (power * a[1].bit_count()), a[1])


# Two ways to move the source coefficient and a chosen suffix coefficient
# across e_m.  This tests coefficient order as well as both involutions.
context_checks = 0
for eps in (0, 1):
    for m in range(16):
        for dmask in range(4):
            for pmask in range(4):
                d, p = (1, dmask), (1, pmask)
                direct = mul(theta(d, eps*m), theta(p, eps))
                suffix = theta(mul(d, theta(p, eps*(m+1))), eps*m)
                assert direct == suffix
                context_checks += 1
assert mul(theta((1, 1), 1), (1, 0)) != mul((1, 1), (1, 0))
assert mul((1, 0), theta((1, 1), 1)) != mul((1, 0), (1, 1))
assert mul((1, 1), (1, 2)) != mul((1, 2), (1, 1))
assert mul((1, 1), theta((1, 0), 1)) != theta(mul((1, 1), (1, 0)), 1)
print(f'Contextual ordered coefficient paths: {context_checks} cases passed; '
      'missing-twist, reversed-product and extra remainder-twist mutations rejected')


def inversions(word, first):
    return sum(x[0] == first and y[0] != first
               for i, x in enumerate(word) for y in word[i+1:])


def weight(word):
    return tuple(sum(orientation for orientation, colour in word if colour == i)
                 for i in range(2))


boundary_checks = 0
alphabet = tuple(product((-1, 1), range(2)))
for length in range(7):
    for word in product(alphabet, repeat=length):
        for j in range(length - 1):
            x, y = word[j:j+2]
            if x[0] == y[0]:
                continue
            swapped = word[:j] + (y, x) + word[j+2:]
            # Source sorts F E; target sorts E F.
            assert inversions(swapped, x[0]) + 1 == inversions(word, x[0])
            assert weight(swapped) == weight(word)
            boundary_checks += 1
            if x[1] == y[1]:
                deleted = word[:j] + word[j+2:]
                assert len(deleted) < len(word)
                assert weight(deleted) == weight(word)
                boundary_checks += 1
# Opposite orientation alone does NOT give weight zero at distinct colours.
assert weight(((1, 0), (-1, 1))) != (0, 0)
print(f'Boundary swap/deletion measure: {boundary_checks} coloured cases passed')
