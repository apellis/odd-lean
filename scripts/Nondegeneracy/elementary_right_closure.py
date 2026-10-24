"""Exact sign/word check, NOT an SKM action over Z or a Lean proof.
Normal forms in the formal odd nilHecke presentation: t^e X^a Y^b.
"""
from functools import lru_cache
from collections import defaultdict

@lru_cache(None)
def nf(w):
    for j in range(len(w)-1):
        pair = w[j:j+2]
        if pair == 'YX': rules = [(-1, 'XY')]
        elif pair == 'Xt': rules = [(1, ''), (-1, 'tY')]
        elif pair == 'Yt': rules = [(1, ''), (-1, 'tX')]
        elif pair == 'tt': return {}
        else: continue
        out = defaultdict(int)
        for c, replacement in rules:
            for term, v in nf(w[:j]+replacement+w[j+2:]).items():
                out[term] += c*v
        return {k:v for k,v in out.items() if v}
    return {w:1}

def total(terms):
    out = defaultdict(int)
    for c,w in terms:
        for term,v in nf(w).items(): out[term] += c*v
    return {k:v for k,v in out.items() if v}

def s(n): return (-1)**n
def chi(n): return n*(n-1)//2

checks = 0
for a in range(10):
    for b in range(10):
        direct = total([(s(b+chi(b)), 'Y'*a+'t'+'Y'*b)])
        explicit = [(s(a+b+chi(b)), 't'+'X'*a+'Y'*b)]
        explicit += [(s(b+chi(b)+j+j*(a-1-j)), 'X'*j+'Y'*(a+b-1-j)) for j in range(a)]
        assert direct == total(explicit), (a,b,'PBW')
        # Close the independent sorting-component formula term by term.
        component = [(s(a+b+b*(1+a)+chi(b)), 'X'*b+'t'+'X'*a)]
        for j in range(a):
            m = a-1-j
            component.append((s(a+b+1+j+b*(j+m)+chi(b)), 'X'*b+'Y'*j+'X'*m))
        for r in range(b):
            n = a+b-1-r
            component.append((-s(r+chi(b-1-r)+r*n+chi(r)), 'X'*r+'Y'*n))
        assert direct == total(component), (a,b,'sorting')
        checks += 2
mutations = [
    ('missing crossing parity', total([(1, 'tY')]), total([(-1, 'tY')])),
    ('missing mate power parity', total([(1, 'tYY')]), total([(-1, 'tYY')])),
    ('odd dot square erased', {}, nf('YY')),
    ('unsigned distant dots', nf('XY'), nf('YX')),
]
for label, mutated, correct in mutations:
    assert mutated != correct, label
print(f'PASS: {checks} exact T closure/PBW comparisons (0 <= a,b < 10).')
print(f'PASS: {len(mutations)} sign/square mutations rejected.')
print('These are formal integer sign bookkeeping checks, not an odd categorical action over Z.')
