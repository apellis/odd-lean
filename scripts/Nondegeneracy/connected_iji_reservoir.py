#!/usr/bin/env python3
"""Exact connected 2i+j upward block; no SKM action is asserted.

Checks every three-strand QH relation on iij, iji, jii for odd i,j,
off-diagonal -2, Q=x²+y², including the NONZERO iji braid correction.
No fourth-strand distant-crossing check, cups/caps, or bubble realization.
"""
import sympy as s


def run():
    d=s.Matrix([[0,0],[1,0]]); p=s.diag(1,-1); z=s.zeros(2)
    a=s.BlockMatrix([[z,z],[s.eye(2),-d]]).as_explicit()
    b=s.BlockMatrix([[d,z],[s.eye(2),z]]).as_explicit()
    t=s.kronecker_product(s.Matrix([[0,1],[0,0]]),s.eye(2))
    delta=s.kronecker_product(p,d); parity=s.kronecker_product(p,p)
    A=s.kronecker_product(a,s.eye(4))
    B=s.kronecker_product(b,s.eye(4))
    C=s.kronecker_product(parity,a)
    T=s.kronecker_product(t,s.eye(4))
    D=s.kronecker_product(delta,s.eye(4))
    E=s.kronecker_product(parity,delta)
    P=s.kronecker_product(parity,parity)
    zero=s.zeros(16); one=s.eye(16)
    words=("iij","iji","jii")

    def dots(w):
        it=iter((A,B))
        return [next(it) if c=="i" else C for c in w]

    def grading(w):
        return (-1)**sum(w[a]=="j" and w[b]=="i"
                         for a in range(3) for b in range(a+1,3))*P

    def crossing(w,r):
        target=w[:r]+w[r+1]+w[r]+w[r+2:]
        if w[r:r+2]=="ii":
            return target,T
        if w[r:r+2]=="ij":
            return target,P
        ds=dots(w)
        return target,(ds[r]**2+ds[r+1]**2)*P

    def path(w,rs):
        m=one
        for r in rs:
            w,c=crossing(w,r)
            m=c*m
        return w,m

    for w in words:
        xs=dots(w)
        for r in range(3):
            assert grading(w)*xs[r]+xs[r]*grading(w)==zero
            assert xs[r]*D+D*xs[r]==zero and xs[r]*E+E*xs[r]==zero
            for q in range(r+1,3):
                assert xs[r]*xs[q]+xs[q]*xs[r]==zero
        for r in (0,1):
            v,c=crossing(w,r); ys=dots(v)
            assert grading(v)*c+c*grading(w)==zero
            assert c*D+D*c==zero and c*E+E*c==zero
            same=w[r]==w[r+1]
            assert c*xs[r]+ys[r+1]*c==(one if same else zero)
            assert ys[r]*c+c*xs[r+1]==(one if same else zero)
            far=2 if r==0 else 0
            assert c*xs[far]+ys[far]*c==zero
            back,cc=crossing(v,r)
            assert back==w
            assert cc*c==(zero if same else xs[r]**2+xs[r+1]**2)
        target,left=path(w,(0,1,0))
        target2,right=path(w,(1,0,1))
        assert target==target2
        correction=B-A if w=="iji" else zero
        assert left-right==correction
    assert B-A!=zero and (B-A).rank()==8
    assert D*E!=zero and (D*E).rank()==4
    assert D*D==E*E==zero and D*E+E*D==zero
    # Omitting the connected repeated-colour correction is detected.
    assert path("iji",(0,1,0))[1]!=path("iji",(1,0,1))[1]
    print("PASS all 3-strand upward relations on iij, iji, jii (16D each)")
    print("PASS genuine iji braid correction x3-x1, rank 8; exterior pair rank 4")
    print("SCOPE: fixed-weight finite algebra representation; no full SKM action")


if __name__ == "__main__":
    run()
