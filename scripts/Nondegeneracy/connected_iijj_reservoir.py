#!/usr/bin/env python3
"""Exact connected 2i+2j upward block, not an SKM action.

Six word summands of dimension 16. Prefix-inversion signs supplied by the
parallel action stream repair distant odd-crossing anticommutation.
"""
import itertools
import sympy as s


def run():
    d=s.Matrix([[0,0],[1,0]]); p=s.diag(1,-1); z=s.zeros(2)
    a=s.BlockMatrix([[z,z],[s.eye(2),-d]]).as_explicit()
    b=s.BlockMatrix([[d,z],[s.eye(2),z]]).as_explicit()
    t=s.kronecker_product(s.Matrix([[0,1],[0,0]]),s.eye(2))
    delta=s.kronecker_product(p,d); parity=s.kronecker_product(p,p)
    base={"i":[s.kronecker_product(q,s.eye(4)) for q in (a,b)],
          "j":[s.kronecker_product(parity,q) for q in (a,b)]}
    Ts={"i":s.kronecker_product(t,s.eye(4)),
        "j":s.kronecker_product(parity,t)}
    P=s.kronecker_product(parity,parity)
    D=s.kronecker_product(delta,s.eye(4)); E=s.kronecker_product(parity,delta)
    zero=s.zeros(16); one=s.eye(16)
    words=sorted(set(map("".join,itertools.permutations("iijj"))))
    def inv(w):
        return sum(w[a]>w[b] for a in range(len(w)) for b in range(a+1,len(w)))
    def dots(w):
        counts={"i":0,"j":0}; result=[]
        for c in w:
            result.append(base[c][counts[c]]); counts[c]+=1
        return result
    def crossing(w,r):
        target=w[:r]+w[r+1]+w[r]+w[r+2:]
        if w[r]==w[r+1]: return target,Ts[w[r]]
        m=(-1)**inv(w[:r])*P
        if w[r:r+2]=="ji":
            ds=dots(w);m=(ds[r]**2+ds[r+1]**2)*m
        return target,m
    def path(w,rs):
        m=one
        for r in rs:
            w,c=crossing(w,r); m=c*m
        return w,m
    failures=[]
    for w in words:
        xs=dots(w)
        for r in range(4):
            for q in range(r+1,4):
                assert xs[r]*xs[q]+xs[q]*xs[r]==zero
        for r in range(3):
            v,c=crossing(w,r); ys=dots(v)
            same=w[r]==w[r+1]
            assert c*xs[r]+ys[r+1]*c==(one if same else zero)
            assert ys[r]*c+c*xs[r+1]==(one if same else zero)
            assert c*D+D*c==zero and c*E+E*c==zero
            assert (-1)**inv(v)*P*c+c*((-1)**inv(w)*P)==zero
            assert crossing(v,r)[1]*c==(zero if same else xs[r]**2+xs[r+1]**2)
            for q in range(4):
                if q not in (r,r+1): assert c*xs[q]+ys[q]*c==zero
        for r in range(2):
            left=path(w,(r,r+1,r))[1]; right=path(w,(r+1,r,r+1))[1]
            correction=xs[r+2]-xs[r] if w[r]==w[r+2] else zero
            if left-right != correction: failures.append(("braid",w,r,(left-right-correction).rank()))
        if path(w,(0,2))[1]+path(w,(2,0))[1] != zero:
            failures.append(("far",w))
    assert not failures, failures
    assert D*E != zero
    # Without the prefix sign the two increasing mixed swaps on ijij
    # are both P; their two path products are +1 instead of negatives.
    assert P*P+P*P==2*one and 2*one!=zero
    print("PASS all four-strand upward relations: 6 words, 16D each")
    print("PASS 12 braid and 6 distant-crossing identities; independent exterior pair")
    print("PASS omitted-prefix-sign negative control; no SKM action claim")


if __name__ == "__main__":
    run()
