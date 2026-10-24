"""Degree-three/four, theta=0 factor: actual closed Mackey loops.
Degree four uses C=<b,d|db=-bd,b²=-bd²,d³=0>; degree three b=-d².
Checks the indicated factor maps, not a full tensor SKM action.
"""
from fractions import Fraction
from functools import lru_cache
import json
import sys

n=int(sys.argv[1]) if len(sys.argv)>1 else 4
assert n in (3,4)
cb=['','d','dd'] if n==3 else ['','d','dd','b','bd','bdd']
rules={'b':{'dd':-1},'ddd':{}} if n==3 else {'db':{'bd':-1},'bb':{'bdd':-1},'ddd':{}}
def add(*ps):
    z={}
    for p in ps:
        for w,c in p.items(): z[w]=z.get(w,0)+c
    return {w:c for w,c in z.items() if c}
def scale(p,c): return {w:v*c for w,v in p.items() if v*c}
@lru_cache(None)
def nf(w):
    for i in range(len(w)):
        for a,r in rules.items():
            if w.startswith(a,i):
                return add(*(scale(nf(w[:i]+b+w[i+len(a):]),c) for b,c in r.items()))
    assert w in cb,w
    return {w:1}
def mul(a,b): return add(*(scale(nf(u+v),x*y) for u,x in a.items() for v,y in b.items()))
def amul(a,b):
    return [[add(*(mul(a[i][k],b[k][j]) for k in range(2))) for j in range(2)] for i in range(2)]
I=[[{'':1},{}],[{}, {'':1}]]
X=[[{}, {'b':1}],[{'':1},{'d':1}]]
Y=[[{'d':-1},{'b':-1}],[{'':1},{}]]
T=[[{}, {'':1}],[{},{}]]
def powa(a,n):
    r=I
    for _ in range(n): r=amul(r,a)
    return r
def vec(a): return [a[i][j].get(w,0) for i in range(2) for j in range(2) for w in cb]
def cols(cs): return [list(r) for r in zip(*cs)]
def mm(a,b):
    return [[sum(a[i][k]*b[k][j] for k in range(len(b))) for j in range(len(b[0]))] for i in range(len(a))]
def inverse(a):
    n=len(a)
    z=[[Fraction(x) for x in row]+[Fraction(i==j) for j in range(n)] for i,row in enumerate(a)]
    for j in range(n):
        p=next(i for i in range(j,n) if z[i][j])
        z[j],z[p]=z[p],z[j]
        d=z[j][j]; z[j]=[x/d for x in z[j]]
        for i in range(n):
            if i!=j:
                d=z[i][j]; z[i]=[x-d*y for x,y in zip(z[i],z[j])]
    return [row[n:] for row in z]

assert not any(vec(powa(X,n)))
assert amul(T,T)==[[{},{}],[{},{}]]
for a,b in [(X,Y),(Y,X)]:
    assert [[add(amul(T,a)[i][j],amul(b,T)[i][j]) for j in range(2)] for i in range(2)]==I
assert not any(vec([[add(amul(X,Y)[i][j],amul(Y,X)[i][j]) for j in range(2)] for i in range(2)]))
basis=[(a,b) for a in range(n) for b in range(n)]
sigma=cols([[(-1)**a*v for v in vec(amul(amul(powa(X,a),T),powa(X,b)))] for a,b in basis])
def cup(s): return cols([[(-1)**(s*a)*v for v in vec(amul(powa(X,a),powa(Y,s)))] for a in range(n)])
def cap(s): return [[(-1)**(s*a)*int(a+s+b==d) for a,b in basis] for d in range(n)]
dim=4*len(cb)
P=[sigma[i]+sum((cup(s)[i] for s in range(n-2)),[]) for i in range(dim)]
Pinv=inverse(P)
assert mm(P,Pinv)==[[int(i==j) for j in range(dim)] for i in range(dim)]
r=Pinv[:n*n]
nonzero={}
for s in range(n):
    for t in range(2*n-1):
        L=mm(mm(cap(s),r),cup(t))
        if any(v for row in L for v in row): nonzero[f'{s},{t}']=[[str(v) for v in row] for row in L]
        # Every loop strictly raises the x-degree; n products vanish.
        assert all(L[i][j]==0 for i in range(n) for j in range(n) if i<=j),(s,t,L)
print(json.dumps({'cyclotomic_degree':n,'factor_inverse_dimension':len(P),'loops_checked':n*(2*n-1),'nonzero_loops':nonzero,
                  'all_loops_strictly_raise_degree':True,'uniform_product_nilpotence_bound':n},indent=2))
