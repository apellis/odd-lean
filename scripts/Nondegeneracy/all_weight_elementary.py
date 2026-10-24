"""Exact all-weight target/cup recurrences and both-parity nilHecke signs.

The coefficients q_n are formal symbols, q_0=1 and q_n=0 for n<0.
The common scalar unit c is suppressed. These checks are not an SKM action,
not a proof of upward independence, and not a contextual matching comparison.
"""
from collections import defaultdict
from functools import lru_cache
import json


def sign(t, exponent):
    """Use parity so negative exponents never introduce floating point."""
    return t ** (exponent % 2)


def clean(terms):
    return {key: value for key, value in terms.items() if value}


def initial_from_fake_bubbles(t, h):
    """J;S from etaP, the inverse matrix and the negative bubL branch."""
    if h > 0:
        return {}
    n = -h
    out = {(0, n): -sign(t, h + 1)}
    for j in range(n):
        # t^(h+1) times H_n;C_j = -t^(h-j) q_(n-j).
        out[(n - j, j)] = -sign(t, h + 1 + h - j)
    return clean(out)


def closed_cup_formula(t, h, b):
    return {(n, b - h - n): -sign(t, b - h + 1 - n)
            for n in range(max(b - h + 1, 0))}


def cup_step(terms, t, h, b):
    """F_(b+1)=t F_b x - t q_(b-h+1) H_0."""
    out = defaultdict(int)
    for (n, m), coefficient in terms.items():
        out[(n, m + 1)] += t * coefficient
    if b - h + 1 >= 0:
        out[(b - h + 1, 0)] -= t
    return clean(out)


@lru_cache(None)
def normal(word, t):
    """Chronological normal form tau^e X^a Y^b, tau encoded by 'z'."""
    for j in range(len(word) - 1):
        pair = word[j:j + 2]
        if pair == 'YX':
            rules = [(t, 'XY')]
        elif pair == 'Xz':
            rules = [(1, ''), (t, 'zY')]
        elif pair == 'Yz':
            rules = [(-t, ''), (t, 'zX')]
        elif pair == 'zz':
            return {}
        else:
            continue
        out = defaultdict(int)
        for coefficient, replacement in rules:
            for term, value in normal(word[:j] + replacement + word[j + 2:], t).items():
                out[term] += coefficient * value
        return clean(out)
    return {word: 1}


def total(terms, t):
    out = defaultdict(int)
    for coefficient, word in terms:
        for term, value in normal(word, t).items():
            out[term] += coefficient * value
    return clean(out)


def check():
    counts = {'cup_recurrences': 0, 'through_PBW': 0, 'remainder_entries': 0,
              'mutation_rejections': 0}
    for t in (1, -1):
        for h in range(-7, 8):
            actual = initial_from_fake_bubbles(t, h)
            for b in range(12):
                expected = closed_cup_formula(t, h, b)
                assert actual == expected, (t, h, b, actual, expected)
                if b >= h:
                    assert actual[(0, b - h)] in (1, -1)
                    assert all(m < b - h for (n, m) in actual if n > 0)
                else:
                    assert not actual
                counts['cup_recurrences'] += 1
                actual = cup_step(actual, t, h, b)
        for a in range(10):
            for b in range(10):
                chi = b * (b - 1) // 2
                direct = total([(sign(t, b + chi), 'Y' * a + 'z' + 'Y' * b)], t)
                expanded = [(sign(t, a + b + chi), 'z' + 'X' * a + 'Y' * b)]
                expanded += [(-sign(t, b + chi + j + 1 + j * (a - 1 - j)),
                              'X' * j + 'Y' * (a + b - 1 - j)) for j in range(a)]
                assert direct == total(expanded, t), (t, a, b)
                counts['through_PBW'] += 1
        for h in range(1, 8):
            for largest_b in range(h):
                s = h - 1 - largest_b
                assert 0 <= s < h
                for b in range(largest_b + 1):
                    bubble_index = b + s - h + 1
                    assert (bubble_index == 0) if b == largest_b else (bubble_index < 0)
                    counts['remainder_entries'] += 1
    for t in (1, -1):
        # Removing the fake-bubble summand at h=-1 must be detected.
        assert {(0, 1): -1} != initial_from_fake_bubbles(t, -1)
        counts['mutation_rejections'] += 1
        # Reversing the inversion minus sign at h=0 must be detected.
        assert {(0, 0): t} != initial_from_fake_bubbles(t, 0)
        counts['mutation_rejections'] += 1
    print(json.dumps(counts, sort_keys=True))
    print('PASS: target-side cups at both parities and h=-7..7; finite remainder pivots.')
    print('Formal recurrences only: no global source-sorting or independence claim.')


if __name__ == '__main__':
    check()
