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
    # Right-B coefficient of t^3 in t^4 is d_i. This is the degree-one
    # inverse-coordinate bubble formula of ELV Proposition 4.7, applied
    # to this connected corner's canonical unit/dot inverse.
    base=[w for w in basis if "t" not in w]
    unitmap=s.zeros(32,8); extract0=s.zeros(8,32); beta3=s.zeros(8,32)
    for k,w in enumerate(base):
        unitmap[indexes[w],k]=1
        extract0[k,indexes[w]]=1
        beta3[k,indexes[w+("t",)*3]]=(-1)**len(w)
    bubble=beta3*T**4*unitmap
    dbase=extract0*D*unitmap;ebase=extract0*E*unitmap
    assert bubble==dbase and bubble.rank()==4
    assert (bubble*ebase).rank()==2
    # The j directions at beta=j contain no i strands, so use the actual
    # rank-one ELV tower with the i coefficient as spectator. Compute its
    # h_j=0 mate inversion, not merely coefficient multiplication.
    import nonvacuum_exterior as R
    regular_j=R.regular((1,0))
    sigma_j=R.mate(regular_j,0,0,0,0)
    assert sigma_j.shape==(8,8) and sigma_j.det()==1
    bubble_j_raw=R.counit(regular_j,0)*sigma_j.inv()*R.unit(regular_j,0)
    # R's basis is [1,x,delta,x*delta], with source d_j=-delta;
    # ours is [1,x,d_j,d_j*x], hence the indicated change of basis.
    change=s.diag(1,1,-1,1)
    bubble_j=s.kronecker_product(s.diag(1,-1),change.inv()*bubble_j_raw*change)
    assert bubble_j==ebase and bubble_j.rank()==4
    assert (bubble*bubble_j).rank()==2
    print(f"PASS {overlaps} rewrite overlaps; 32D connected cyclotomic corner")
    print("PASS canonical unit/dot rank-4 B-basis inversion; exterior product rank 8")
    print("PASS f_i(t) nonzero control; scope beta=alpha_j, i absent")
    print("PASS inverse-coordinate i bubble=d_i (rank4), product with d_j rank2")
    print("PASS actual j mate inversion (8x8); two connected bubble composites product rank2")


if __name__ == "__main__":
    run()
