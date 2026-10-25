#!/usr/bin/env python3
"""First connected cyclotomic inversion corner, with two odd parameters.

N_i=N_j=2, top even coefficients zero, Q=t²+x². Corner B[t]/(f_i(t)Q)
has proposed basis d^a e^b x^c t^r, a,b,c<2, r<4 (dimension 32).
Checks all word-overlap ambiguities, regular algebra relations and the
unit/dot inversion basis. This is the i-absent weight beta=alpha_j only.
"""
from collections import defaultdict
from functools import lru_cache
from itertools import product
import sympy as s


def run():
    order={c:i for i,c in enumerate("dext")}
    rules={tuple("dd"):[],tuple("ee"):[],tuple("xx"):[(-1,tuple("ex"))],
           tuple("tttt"):[(-1,tuple("dttt")),(1,tuple("extt")),(1,tuple("dext"))]}
    for a,b in product(order,repeat=2):
        if order[a]>order[b]:rules[a,b]=[(-1,(b,a))]
    @lru_cache(None)
    def nf(w):
        for at in range(len(w)):
            for lhs,rhs in rules.items():
                if w[at:at+len(lhs)]==lhs:
                    out=defaultdict(int)
                    for c,v in rhs:
                        for u,k in nf(w[:at]+v+w[at+len(lhs):]):out[u]+=c*k
                    return tuple(sorted((u,c) for u,c in out.items() if c))
        return ((w,1),)
    def poly(terms):
        out=defaultdict(int)
        for c,w in terms:
            for u,k in nf(w):out[u]+=c*k
        return {u:c for u,c in out.items() if c}
    overlaps=0
    # Every intersecting pair of left-hand sides, including contained ones.
    for left,right in product(rules,repeat=2):
        for shift in range(len(left)):
            overlap=min(len(left)-shift,len(right))
            if left[shift:shift+overlap]!=right[:overlap]:continue
            word=left+right[len(left)-shift:] if len(right)>len(left)-shift else left
            first=poly((c,v+word[len(left):]) for c,v in rules[left])
            second=poly((c,word[:shift]+v+word[shift+len(right):]) for c,v in rules[right])
            assert first==second,(word,left,right)
            overlaps+=1
    basis=[tuple("d"*a+"e"*b+"x"*c+"t"*r)
           for a,b,c,r in product(range(2),range(2),range(2),range(4))]
    indexes={w:i for i,w in enumerate(basis)}
    def left(c):
        m=s.zeros(32)
        for col,w in enumerate(basis):
            for u,a in nf((c,)+w):m[indexes[u],col]=a
        return m
    D,E,X,T=map(left,"dext"); zero=s.zeros(32)
    assert X*X-X*E==zero
    F=T*T-T*D;Q=T*T+X*X
    assert F*Q==zero
    assert D*E!=zero and (D*E).rank()==8
    assert F!=zero # connected relation is f_i(t)*Q, NOT f_i(t)=0
    for a,b in product((D,E,X,T),repeat=2):
        if a!=b:assert a*b+b*a==zero
    # The canonical unit and its first four extra-dot powers give all
    # B coordinates; here B basis is d^a e^b x^c.
    unit=s.eye(32)[:,indexes[()]]
    columns=[]
    for a,b,c,r in product(range(2),range(2),range(2),range(4)):
        columns.append(D**a*E**b*X**c*T**r*unit)
    inversion=s.Matrix.hstack(*columns)
    assert inversion==s.eye(32)
    print(f"PASS {overlaps} rewrite overlaps; 32D connected cyclotomic corner")
    print("PASS canonical unit/dot rank-4 B-basis inversion; exterior product rank 8")
    print("PASS f_i(t) nonzero control; scope beta=alpha_j, i absent")


if __name__ == "__main__":
    run()
