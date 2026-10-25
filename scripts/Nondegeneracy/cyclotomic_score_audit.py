#!/usr/bin/env python3
"""Finite adversarial audit, not a proof or an SKM action.

Two-strand odd nilHecke and distinct-odd-colour Ore models, with two
independent exterior coefficients. All arithmetic is integral. The latter
model has an inhomogeneous invariant quadratic polynomial. We test actual
normal forms of two-sided cyclotomic multiples, not only numeric scores.
"""
from collections import defaultdict
from functools import lru_cache
from itertools import product


class Reducer:
    def __init__(self, mixed):
        self.mixed = mixed

    def rule(self, pair):
        a, b = pair
        if a == b and a in "de":
            return []
        if (a in "xyt" and b in "de") or (a == "e" and b == "d"):
            return [(-1, (b, a))]
        if pair == ("y", "x"):
            return [(-1, ("x", "y"))]
        if a == "t" and b in "xy":
            result = [(-1, ("y" if b == "x" else "x", "t"))]
            return result if self.mixed else [(1, ())] + result
        if pair == ("t", "t"):
            # Q=1+x²+y²+3x²y² is invariant under x↦−y,y↦−x.
            return [(1, ()), (1, ("x",)*2), (1, ("y",)*2),
                    (3, ("x",)*2+("y",)*2)] if self.mixed else []
        return None

    @lru_cache(maxsize=None)
    def normal(self, word):
        for i in range(len(word)-1):
            terms = self.rule(word[i:i+2])
            if terms is not None:
                answer = defaultdict(int)
                for c, middle in terms:
                    for target, value in self.normal(word[:i]+middle+word[i+2:]):
                        answer[target] += c*value
                return tuple(sorted((w, c) for w, c in answer.items() if c))
        return ((word, 1),)

    def polynomial(self, terms):
        answer = defaultdict(int)
        for c, w in terms:
            for v, a in self.normal(w):
                answer[v] += c*a
        return {w:c for w,c in answer.items() if c}


def dot_count(w):
    return w.count("x") + w.count("y")


def score(w):
    return len(w) - 2*w.count("t")


def run():
    count = 0
    for mixed in (False, True):
        r = Reducer(mixed)
        # Resolve every minimal length-three ambiguity independently at
        # either possible first reduction (includes exterior/crossing overlaps).
        overlaps = 0
        for w in product("dexyt", repeat=3):
            left, right = r.rule(w[:2]), r.rule(w[1:])
            if left is not None and right is not None:
                a = r.polynomial((c, u+w[2:]) for c,u in left)
                b = r.polynomial((c, w[:1]+u) for c,u in right)
                assert a == b, (mixed, w, a, b)
                overlaps += 1
        multipliers = [tuple(ext)+("x",)*a+("y",)*b+("t",)*t
                       for ext in ("", "d", "e", "de")
                       for a in range(3) for b in range(3-a) for t in (0,1)]
        for n in (3,5):
            for a,b in product(multipliers, repeat=2):
                pure = r.polynomial([(1, a+("x",)*n+b)])
                assert all(dot_count(w) >= n-2 for w in pure)
                # d has coefficient weight 1; x^n+d*x^(n-1) is
                # parity homogeneous and every term has total weight n.
                deformed = r.polynomial([(1, a+("x",)*n+b),
                                         (1, a+("d",)+("x",)*(n-1)+b)])
                assert all(score(w) >= n-2 for w in deformed)
                count += 2
        assert r.normal(tuple("de")) == ((tuple("de"),1),)
        assert r.normal(tuple("tde")) == ((tuple("det"),1),)
        assert r.normal(tuple("ted")) == ((tuple("det"),-1),)
        # A forbidden unweighted constant term is detected, not silently
        # interpreted as a homogeneous coefficient of weight n.
        bad = r.polynomial([(1,("x",)*5),(-1,())])
        assert any(score(w) < 3 for w in bad)
        print(f"PASS {'distinct-colour' if mixed else 'same-colour'}: "
              f"{overlaps} local ambiguities, pure/deformed ideal support, "
              "mixed exterior coefficients, unweighted-constant control")
    print(f"PASS {count} explicit two-sided ideal multiples; no full SKM claim")


if __name__ == "__main__":
    run()
