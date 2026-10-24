"""Actual left degree-two factor loops at its middle weight.
Uses induction/restriction cups/caps and the signed Mackey crossing.
Only this factor calculation is checked, not a full tensor action.
"""
from fractions import Fraction
import json

I=[[1,0],[0,1]]
X=[[0,0],[1,0]]
T=[[0,1],[0,0]]

def mm(a,b):
    return [[sum(a[i][k]*b[k][j] for k in range(len(b)))
             for j in range(len(b[0]))] for i in range(len(a))]

def power(a,n):
    r=I
    for _ in range(n): r=mm(r,a)
    return r

def inverse(a):
    n=len(a)
    z=[[Fraction(x) for x in row]+[Fraction(i==j) for j in range(n)]
       for i,row in enumerate(a)]
    for j in range(n):
        p=next(i for i in range(j,n) if z[i][j])
        z[j],z[p]=z[p],z[j]
        d=z[j][j]; z[j]=[x/d for x in z[j]]
        for i in range(n):
            if i!=j:
                d=z[i][j]; z[i]=[x-d*y for x,y in zip(z[i],z[j])]
    return [row[n:] for row in z]

def flatten(a): return [e for row in a for e in row]
def columns(cs): return [list(row) for row in zip(*cs)]

basis=[(a,b) for a in range(2) for b in range(2)]
sigma=columns([[(-1)**a*v for v in flatten(mm(mm(power(X,a),T),power(X,b)))]
               for a,b in basis])
r=inverse(sigma)
assert mm(r,sigma)==[[int(i==j) for j in range(4)] for i in range(4)]

def cup(s):
    return columns([[(-1)**(s*a)*v for v in flatten(mm(power(X,a),power(X,s)))]
                    for a in range(2)])

def cap(s):
    return [[(-1)**(s*a)*int(a+s+b==d) for a,b in basis] for d in range(2)]

loops={}
for s in range(4):
    for t in range(4):
        out=mm(mm(cap(s),r),cup(t))
        assert all(v==0 for row in out for v in row),(s,t,out)
        loops[f'{s},{t}']=[[int(v) for v in row] for row in out]
print(json.dumps({'sigma':sigma,'inverse':[[int(v) for v in row] for row in r],
                  'closed_loops':loops,'all_zero':True},indent=2))
