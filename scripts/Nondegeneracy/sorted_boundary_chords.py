"""Finite combinatorial/sign checks, not an SKM action or sweep proof."""
from itertools import combinations, permutations


def interleave(a, b, c, d):
    a, b = sorted((a, b))
    c, d = sorted((c, d))
    return (a < c < b < d) or (c < a < d < b)


cases = pairs = 0
for n in range(7):
    for r in range(n + 1):  # number of D' endpoints
        for v in range(n + 1):  # number of U' endpoints
            circle = ([('s', i) for i in range(r, n)]
                      + [('t', j) for j in range(n - 1, v - 1, -1)]
                      + [('t', j) for j in range(v - 1, -1, -1)]
                      + [('s', i) for i in range(r)])
            loc = {a: k for k, a in enumerate(circle)}
            for w in permutations(range(n)):
                for i, j in combinations(range(n), 2):
                    cross = interleave(loc['s', i], loc['t', w[i]],
                                       loc['s', j], loc['t', w[j]])
                    assert cross == (w[i] > w[j])
                    pairs += 1
                counts = tuple(i ** 2 for i in range(n))
                out: list[int | None] = [None] * n
                for i, j in enumerate(w):
                    out[j] = counts[i]
                assert tuple(out[w[i]] for i in range(n)) == counts
                cases += 1
print(f'Chord/inversion and dot-count bijection: {cases} permutation/split cases; '
      f'{pairs} strand pairs passed')

mate_cases = 0
for parity in (0, 1):
    for m in range(40):
        recursive = sum(parity * k for k in range(m)) % 2
        assert recursive == (parity * (m * (m - 1) // 2)) % 2
        assert recursive == (parity * (m // 2)) % 2
        mate_cases += 1
print(f'Repeated right-dot mate signs: {mate_cases} cases passed; no dot-square quotient')
