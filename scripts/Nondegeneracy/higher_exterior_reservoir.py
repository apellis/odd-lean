# /// script
# requires-python = ">=3.10"
# dependencies = ["sympy==1.14.0"]
# ///
"""Bounded two-strand operators over a nonzero exterior reservoir.

Constructs the odd polynomial LEFT-ideal quotient by f_N and partial(f_N),
with f_N=x1^N+x1^(N-1)delta, at even cutoffs. Checks stability rather than
assuming that a truncated quotient supports divided differences.
Default N=2,4,6. This is an upward module, not a full categorical action.
"""
import sympy as S
from functools import lru_cache

def add(p,q):
 r=p.copy()
 for m,c in q.items():
  r[m]=r.get(m,0)+c
 return {m:c for m,c in r.items() if c}
def scale(c,p):return {m:c*v for m,v in p.items() if c*v}
def mul(p,q):
 r={}
 for (a,b,e),c in p.items():
  for (A,B,E),v in q.items():
   if e+E>1:continue
   m=(a+A,b+B,e+E)
   r[m]=r.get(m,0)+c*v*(-1)**(b*A+e*(A+B))
 return {m:c for m,c in r.items() if c}
x={(1,0,0):1};y={(0,1,0):1};delta={(0,0,1):1}
@lru_cache(None)
def derivative_monomial(a,b,e):
 if a:return add({(a-1,b,e):1},scale(-1,mul(y,derivative_monomial(a-1,b,e))))
 if b:return add({(0,b-1,e):1},scale(-1,mul(x,derivative_monomial(0,b-1,e))))
 return {}
def derivative(p):
 r={}
 for m,c in p.items():r=add(r,scale(c,derivative_monomial(*m)))
 return r
def monomials(d):
 return [(a,d-e-a,e) for e in (0,1) if d>=e for a in range(d-e,-1,-1)]
def vector(p,mons):return S.Matrix([p.get(m,0) for m in mons])
def cols(vs,n):return S.Matrix.hstack(*vs) if vs else S.zeros(n,0)
def reservoir(N):
 assert N%2==0
 f={(N,0,0):1,(N-1,0,1):1};g=derivative(f)
 levels=[]
 for d in range(2*N+1):
  mons=monomials(d);rels=[]
  for polynomial,degree in ((f,N),(g,N-1)):
   if d>=degree:
    rels += [vector(mul({m:1},polynomial),mons) for m in monomials(d-degree)]
  R=cols(rels,len(mons));Q=cols(R.T.nullspace(),len(mons)).T
  piv=Q.rref()[1];sec=cols([S.eye(len(mons))[:,j] for j in piv],len(mons))
  if Q.rows:Q=(Q*sec).inv()*Q
  levels.append((mons,R,Q,sec))
 dims=[l[2].rows for l in levels]
 assert dims[-2:]==[0,0],dims
 offsets=[sum(dims[:d]) for d in range(len(dims))];n=sum(dims)
 def operator(operation,degree):
  M=S.zeros(n)
  for d,(mons,rels,Q,sec) in enumerate(levels):
   target=d+degree
   if not 0<=target<len(levels):continue
   outmons,_,outQ,_=levels[target]
   raw=cols([vector(operation({m:1}),outmons) for m in mons],len(outmons))
   assert outQ*raw*rels==S.zeros(outQ.rows,rels.cols),('unstable',N,d,degree)
   block=outQ*raw*sec
   M[offsets[target]:offsets[target]+dims[target],offsets[d]:offsets[d]+dims[d]]=block
  return M
 X=operator(lambda p:mul(x,p),1);Y=operator(lambda p:mul(y,p),1)
 D=operator(lambda p:mul(delta,p),1);T=operator(derivative,-1)
 I=S.eye(n);Z=S.zeros(n)
 assert T*T==Z and X*Y+Y*X==Z
 assert T*X+Y*T==I and X*T+T*Y==I
 assert all(D*M+M*D==Z for M in (X,Y,T))
 assert D*D==Z and D.rank()==n//2
 assert X**N+X**(N-1)*D==Z
 print('N',N,'graded dimensions',dims,'total',n,'delta rank',D.rank(),flush=True)
 return X,Y,T,D,dims
def check_cutoff(N):
 X,Y,T,D,dims=reservoir(N);n=X.rows
 assert n==2*N*(N-1)
 labels=[(a,b,w,e) for a in range(N) for b in range(N-1)
         for w in (0,1) for e in (0,1)]
 matrices=[X**a*Y**b*T**w*D**e for a,b,w,e in labels]
 rank=cols([m.reshape(n*n,1) for m in matrices],n*n).rank()
 assert rank==len(labels)==4*N*(N-1)
 print('independent rectangular PBW operators',rank,
       '; all coefficient+dot degree <=',N-2,'detected',flush=True)
 g=sum(((-1)**k*X**(N-1-k)*Y**k for k in range(N)),S.zeros(n))
 g+=sum((X**(N-2-k)*Y**k*D for k in range(N-1)),S.zeros(n))
 assert g*T==S.zeros(n)
 print('degree',N-1,'kernel relation (partial f_N)*tau=0 PASS',flush=True)

if __name__=='__main__':
 import argparse
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--cutoffs',type=int,nargs='+',default=[2,4,6])
 for N in parser.parse_args().cutoffs:
  if N<2 or N%2:parser.error('cutoffs must be positive even integers >=2')
  check_cutoff(N)
