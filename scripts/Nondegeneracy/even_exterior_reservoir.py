# /// script
# requires-python = ">=3.10"
# dependencies = ["sympy==1.14.0"]
# ///
"""Cutoff-four two-strand reservoir with chi1=epsilon and d=-delta.

Both epsilon^2 and delta^2 vanish, but epsilon*delta does not. Checks the
actual odd polynomial quotient action and a full96-element cyclotomic PBW
family. No cups/caps or full categorical action are asserted here.
"""
import sympy as S
from functools import lru_cache
from higher_exterior_reservoir import add,scale,cols

# Normal order x^a y^b delta^e epsilon^c, integer degree a+b+e+2c.
def multiply(p,q):
 out={}
 for (a,b,e,c),v in p.items():
  for (A,B,E,C),w in q.items():
   if e+E>1 or c+C>1:continue
   m=(a+A,b+B,e+E,c+C)
   out[m]=out.get(m,0)+v*w*(-1)**(b*A+e*(A+B))
 return {m:c for m,c in out.items() if c}
x={(1,0,0,0):1};y={(0,1,0,0):1}
delta={(0,0,1,0):1};epsilon={(0,0,0,1):1}
@lru_cache(None)
def partial_monomial(a,b,e,c):
 if a:return add({(a-1,b,e,c):1},scale(-1,multiply(y,partial_monomial(a-1,b,e,c))))
 if b:return add({(0,b-1,e,c):1},scale(-1,multiply(x,partial_monomial(0,b-1,e,c))))
 return {}
def partial(p):
 out={}
 for m,c in p.items():out=add(out,scale(c,partial_monomial(*m)))
 return out
def monomials(d):
 return [(a,d-e-2*c-a,e,c) for c in (0,1) for e in (0,1)
         if d>=e+2*c for a in range(d-e-2*c,-1,-1)]
def vector(p,mons):return S.Matrix([p.get(m,0) for m in mons])

def main():
 f={(4,0,0,0):1,(3,0,1,0):1,(2,0,0,1):1,(1,0,1,1):1}
 g=partial(f);levels=[]
 for d in range(11):
  mons=monomials(d);relations=[]
  for polynomial,degree in ((f,4),(g,3)):
   if d>=degree:
    relations += [vector(multiply({m:1},polynomial),mons) for m in monomials(d-degree)]
  rel=cols(relations,len(mons));q=cols(rel.T.nullspace(),len(mons)).T
  piv=q.rref()[1];sec=cols([S.eye(len(mons))[:,j] for j in piv],len(mons))
  if q.rows:q=(q*sec).inv()*q
  levels.append((mons,rel,q,sec))
 dims=[l[2].rows for l in levels];assert dims[-2:]==[0,0]
 offsets=[sum(dims[:d]) for d in range(len(dims))];n=sum(dims)
 assert n==48
 def operator(operation,degree):
  result=S.zeros(n)
  for d,(mons,rel,q,sec) in enumerate(levels):
   target=d+degree
   if not 0<=target<len(levels):continue
   outmons,_,outq,_=levels[target]
   raw=cols([vector(operation({m:1}),outmons) for m in mons],len(outmons))
   assert outq*raw*rel==S.zeros(outq.rows,rel.cols)
   result[offsets[target]:offsets[target]+dims[target],offsets[d]:offsets[d]+dims[d]]=outq*raw*sec
  return result
 X=operator(lambda p:multiply(x,p),1);Y=operator(lambda p:multiply(y,p),1)
 D=operator(lambda p:multiply(delta,p),1);E=operator(lambda p:multiply(epsilon,p),2)
 T=operator(partial,-1);zero=S.zeros(n);identity=S.eye(n)
 assert T*T==zero and X*Y+Y*X==zero
 assert T*X+Y*T==identity and X*T+T*Y==identity
 assert all(D*M+M*D==zero for M in (X,Y,T))
 assert all(E*M==M*E for M in (X,Y,T,D))
 assert D*D==E*E==zero and (D*E).rank()==12
 assert X**4+X**3*D+X**2*E+X*D*E==zero
 mats=[X**a*Y**b*T**w*D**e*E**c for a in range(4) for b in range(3)
       for w in (0,1) for e in (0,1) for c in (0,1)]
 assert cols([m.reshape(n*n,1) for m in mats],n*n).rank()==len(mats)==96
 print('PASS48D polynomial module with stable divided difference; graded dimensions',dims)
 print('PASS independent96-element PBW family over even/exterior base; delta*epsilon rank12')
 print('SCOPE: two-strand upward realization, not full categorical action')

if __name__=='__main__':main()
