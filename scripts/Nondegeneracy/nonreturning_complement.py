"""Finite Coxeter/top-symbol checks, not categorical independence tests."""

from collections import deque
from fractions import Fraction
from functools import lru_cache
from itertools import permutations, product


def length(p):
    return sum(p[i] > p[j] for i in range(len(p)) for j in range(i + 1, len(p)))


def compose(p, q):
    return tuple(p[q[i]] for i in range(len(p)))


def inverse(p):
    return tuple(p.index(i) for i in range(len(p)))


def transposition(n, i):
    p = list(range(n))
    p[i], p[i + 1] = p[i + 1], p[i]
    return tuple(p)


def word_value(n, word):
    p = tuple(range(n))
    for i in word:
        p = compose(transposition(n, i), p)
    return p


@lru_cache(None)
def reduced_words(p: tuple[int, ...]) -> tuple[tuple[int, ...], ...]:
    n = len(p)
    if length(p) == 0:
        return ((),)
    out: list[tuple[int, ...]] = []
    for i in range(n - 1):
        q = compose(transposition(n, i), p)
        if length(q) == length(p) - 1:
            out.extend(w + (i,) for w in reduced_words(q))
    return tuple(out)


def neighbors(word, parity):
    strand = list(parity)
    for j, a in enumerate(word):
        if j + 1 < len(word) and abs(a - word[j + 1]) > 1:
            b = word[j + 1]
            sign = (-1) ** (strand[a] * strand[a + 1] * strand[b] * strand[b + 1])
            yield word[:j] + (b, a) + word[j + 2:], sign
        if j + 2 < len(word) and word[j + 2] == a and abs(a - word[j + 1]) == 1:
            b = word[j + 1]
            yield word[:j] + (b, a, b) + word[j + 3:], 1
        strand[a], strand[a + 1] = strand[a + 1], strand[a]


def multiply_monomials(a, b):
    """Ordered odd x1,x2,delta_i,delta_j; only the deltas square to zero."""
    if any(a[i] + b[i] > 1 for i in (2, 3)):
        return Fraction(0), None
    sign = (-1) ** sum(a[i] * b[j] for i in range(4) for j in range(i))
    return Fraction(sign), tuple(x + y for x, y in zip(a, b))


def main():
    counts = {
        "complement_pairs": 0,
        "triangular_tests": 0,
        "signed_reduced_graphs": 0,
        "signed_edges": 0,
    }
    for n in range(5):
        ps = list(permutations(range(n)))
        w0 = tuple(reversed(range(n)))
        top_length = length(w0)
        for w in ps:
            c = compose(w0, inverse(w))
            assert compose(c, w) == w0
            assert length(c) + length(w) == top_length
            counts["complement_pairs"] += 1
            for v in ps:
                if length(v) <= length(w):
                    # A top symbol needs a reduced concatenation of length N.
                    top = (
                        length(c) + length(v) == top_length
                        and length(compose(c, v)) == top_length
                    )
                    assert top == (v == w)
                    counts["triangular_tests"] += 1
            words = set(reduced_words(w))
            assert all(word_value(n, a) == w and len(a) == length(w) for a in words)
            for parity in product((0, 1), repeat=n):
                first = min(words)
                signs = {first: 1}
                queue = deque([first])
                while queue:
                    a = queue.popleft()
                    for b, sign in neighbors(a, parity):
                        assert b in words
                        counts["signed_edges"] += 1
                        if b in signs:
                            assert signs[b] == signs[a] * sign
                        else:
                            signs[b] = signs[a] * sign
                            queue.append(b)
                assert set(signs) == words
                counts["signed_reduced_graphs"] += 1

    # A purely unsigned graph check would miss this local super sign.
    assert dict(neighbors((0, 2), (1, 1, 1, 1)))[(2, 0)] == -1

    x1, x2 = (1, 0, 0, 0), (0, 1, 0, 0)
    di, dj = (0, 0, 1, 0), (0, 0, 0, 1)
    assert multiply_monomials(x1, x2)[0] == 1
    assert multiply_monomials(x2, x1)[0] == -1
    assert multiply_monomials(x1, x1) == (Fraction(1), (2, 0, 0, 0))
    sign, exterior_product = multiply_monomials(di, dj)
    assert sign == 1 and exterior_product == (0, 0, 1, 1)
    assert multiply_monomials(dj, di)[0] == -1
    assert multiply_monomials(di, di)[0] == 0
    q_product = [
        multiply_monomials(z, exterior_product)
        for z in ((2, 0, 0, 0), (0, 2, 0, 0))
    ]
    assert q_product == [
        (Fraction(1), (2, 0, 1, 1)),
        (Fraction(1), (0, 2, 1, 1)),
    ]
    print(counts)
    print("Q coefficient arithmetic:", q_product)
    print("PASS: complements, triangular top symbols, signed reduced graphs through S4;")
    print("empty boundary, nonzero odd dot squares, and full mixed exterior monomial retained.")
    print("Not tested: categorical lower terms, upward independence, or oriented transport.")


if __name__ == "__main__":
    main()
