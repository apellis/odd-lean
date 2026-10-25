#!/usr/bin/env python3
"""Exact skew-polynomial normality, including the even-cutoff obstruction.

Normal order x^a d^e, d²=0, dx=−xd; polynomial even chi coefficients.
This checks the proposed Ore twist, not KKO projectivity or an SKM action.
"""
import sympy as s


def run():
    for n in range(1,9):
        m=n//2
        chi=(s.Integer(1),)+s.symbols(f"c1:{m+1}")
        def clean(p):
            result={}
            for (a,e),c in p.items():
                if e>1: continue
                if n%2==0 and e: c=c.subs(chi[m],0)
                c=s.expand(c)
                if c: result[a,e]=c
            return result
        def add(*ps):
            out={}
            for p in ps:
                for k,v in p.items():out[k]=out.get(k,0)+v
            return clean(out)
        def scale(p,c):return clean({k:c*v for k,v in p.items()})
        def mul(p,q):
            out={}
            for (a,e),c in p.items():
                for (b,f),v in q.items():
                    key=(a+b,e+f)
                    out[key]=out.get(key,0)+(-1)**(e*b)*c*v
            return clean(out)
        def power(p,r):
            out={(0,0):s.Integer(1)}
            for _ in range(r):out=mul(out,p)
            return out
        X={(1,0):s.Integer(1)}; D={(0,1):s.Integer(1)}
        F=clean({(ell,(n-ell)%2):(-1)**ell*chi[(n-ell)//2]
                 for ell in range(n+1)})
        NX=add(X,scale(D,-2)); ND=scale(D,(-1)**n)
        NF=add(*(scale(mul(power(NX,a),power(ND,e)),c)
                 for (a,e),c in F.items()))
        assert mul(X,F)==mul(F,NX)
        assert mul(D,F)==mul(F,ND)
        assert NF==F and power(NX,2)==power(X,2)
        assert add(NX,scale(ND,2*(-1)**n))==X
        if n%2==0:
            assert mul(X,F)!=mul(F,X)  # ordinary-dot bimodule rule fails
            # Killing the top even parameter leaves this obstruction alive.
            comm=add(mul(X,F),scale(mul(F,X),-1))
            assert any(s.expand(c.subs(chi[m],0))!=0 for c in comm.values())
    print("PASS N=1..8: x f=f(x−2d), d f=f((-1)^N d), ν(f)=f, ν(x²)=x²")
    print("PASS inverse automorphism and even-cutoff noncommutation controls")
    print("SCOPE: normal cyclotomic element and proposed twisted bimodule input")


if __name__ == "__main__":
    run()
