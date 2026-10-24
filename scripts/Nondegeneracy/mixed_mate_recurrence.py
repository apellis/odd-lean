"""Exact parity and ordered-word checks for separated mixed mates.

These test the stated coordinate calculation, not existence of a coherent
upward action. Raw source mates and normalized mates have different even signs.
"""
from collections import Counter
import itertools
import json

parity_cases = 0
for p, content, a, v, f in itertools.product(range(2), repeat=5):
    s = p * content
    b = (a + v + p + f) % 2
    # Input frame, the two crossing frames, and outer parity whiskering.
    assert (s * (v + f) + s * (a + b) + s * p) % 2 == 0
    parity_cases += 1

ordered_cases = 0
raw_even_mutations_rejected = 0
for q in (-1, 1):
    for n in range(1, 20):
        # A key (i,j) means y^i b x^j. Never commute b with either dot.
        c_slide = Counter()
        d_slide = Counter()
        for r in range(n):
            c_slide[r, -r] += q ** r
            c_slide[r + 1, -r - 1] -= q ** (r + 1)
            d_slide[-r - 1, r + 1] -= q ** (r + 1)
            d_slide[-r, r] += q ** (r + 2)
        c_slide = {k: v for k, v in c_slide.items() if v}
        d_slide = {k: v for k, v in d_slide.items() if v}
        assert c_slide == {(0, 0): 1, (n, -n): -q ** n}
        assert d_slide == {(0, 0): 1, (-n, n): -q ** n}
        # Nilpotence kills the respective n-th-power remainder.
        # The raw source equation instead has right-hand side -q b.
        for slide in (c_slide, d_slide):
            raw = {k: -q * v for k, v in slide.items()}
            assert raw[0, 0] == -q
            if q == 1:
                assert slide[0, 0] != raw[0, 0]
                raw_even_mutations_rejected += 1
        ordered_cases += 2

print(json.dumps({
    "parity_line_cases": parity_cases,
    "ordered_telescoping_cases": ordered_cases,
    "raw_even_mutations_rejected": raw_even_mutations_rejected,
    "all_passed": True,
}))
