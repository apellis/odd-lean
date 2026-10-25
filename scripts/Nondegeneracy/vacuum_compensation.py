# /// script
# requires-python = ">=3.10"
# dependencies = ["sympy==1.14.0"]
# ///
"""Actual fixed-weight compensation retaining even and exterior coefficients.

Reservoir vacuum of weight-4, probe highest vacuum of weight+4. Only their
first tower levels enter the actual height-zero mate. The probe polynomial
is (y^2-a)^2. No general multicolour spectral/unfurling theorem is asserted.
"""
import argparse
from functools import lru_cache
import sympy as S
import nonvacuum_exterior as R
import vacuum_even_exterior as V


def configure(a):
 x=V.matrix({(1,0,0):1})
 reservoir0=R.Alg([V.matrix({m:1}) for m in V.base],[m[2] for m in V.base])
 reservoir1=R.Alg([V.matrix({m:1}) for m in V.basis],[(m[0]+m[2])%2 for m in V.basis])
 y=S.zeros(4)
 for r in range(3):y[r+1,r]=1
 y[0,3]=-a*a;y[2,3]=2*a
 probe0=R.Alg([S.eye(1)],[0])
 probe1=R.Alg([y**r for r in range(4)],[r%2 for r in range(4)])
 R.A=[reservoir0,reservoir1];R.B=[probe0,probe1]
 R.C={(i,j):R.TensorAlg(R.A[i],R.B[j]) for i in range(2) for j in range(2)}
 R.ax1=x
 old_dot=R.dot
 def dot(m,t):
  if t==0:return old_dot(m,t)
  i,j=m.idx
  assert j==1
  eta=R.kron(R.A[i].one,R.B[j].coord(y))
  return (-1)**i*m.action(eta)*R.paritydiag(m.ps)
 R.dot=dot
 return x,y


def use_free_coordinates():
 # At these boundary levels A1 is free over A0 on 1,x,x²,x³ and B1
 # is free over Q on 1,y,y²,y³. These are exact balanced tensor/Hom
 # coordinates, eliminating the redundant spectator-A linear equations.
 @lru_cache(None)
 def ind(m,idx):
  assert m.idx[0]==0 and idx==(1,m.idx[1])
  c=R.C[m.idx];d=R.C[idx];nb=R.B[idx[1]].n;n=m.n*4
  entries={};sections={}
  for im in range(m.n):
   for r in range(4):sections[(im*d.n+4*r*nb,im*4+r)]=1
  for ja,(r,b,e) in enumerate(V.basis):
   ac=V.base.index((0,b,e))
   for jb in range(nb):
    cj=ac*nb+jb;sgn=(-1)**(r*c.ps[cj])
    for (km,im),value in m.act[cj].todok().items():
     entries[(km*4+r,im*d.n+ja*nb+jb)]=sgn*value
  q=S.SparseMatrix(n,m.n*d.n,entries);sec=S.SparseMatrix(m.n*d.n,n,sections)
  assert q*sec==S.eye(n)
  inc=R.inclusion(m.idx,idx)
  for j in range(c.n):
   assert q*R.kron(m.act[j],S.eye(d.n))==q*R.kron(S.eye(m.n),R.lmul(d,inc[:,j]))
  acts=[q*R.kron(S.eye(m.n),R.rmul(d,S.eye(d.n)[:,j]))*sec for j in range(d.n)]
  out=R.Mod(idx,[(p+r)%2 for p in m.ps for r in range(4)],acts,'free induction')
  out.Q=q;out.sec=sec;out.base=m
  return out
 @lru_cache(None)
 def coind(m,idx):
  assert m.idx[1]==0 and idx==(m.idx[0],1)
  c=R.C[m.idx];d=R.C[idx];nb=R.B[1].n;n=nb*m.n
  entries={}
  for ia in range(c.n):
   for jb in range(nb):
    sgn=(-1)**(c.ps[ia]*R.B[1].ps[jb])
    for (km,im),value in m.act[ia].todok().items():
     entries[((ia*nb+jb)*m.n+km,jb*m.n+im)]=sgn*value
  h=S.SparseMatrix(d.n*m.n,n,entries)
  extract=S.SparseMatrix(n,d.n*m.n,{(j,j):1 for j in range(n)})
  assert extract*h==S.eye(n)
  inc=R.inclusion(m.idx,idx)
  for j in range(c.n):
   assert R.kron(R.rmul(d,inc[:,j]).T,S.eye(m.n))*h==R.kron(S.eye(d.n),m.act[j])*h
  acts=[extract*R.kron(R.lmul(d,S.eye(d.n)[:,j]).T,S.eye(m.n))*h for j in range(d.n)]
  out=R.Mod(idx,[(p+q)%2 for p in R.B[1].ps for q in m.ps],acts,'free coinduction')
  out.H=h;out.extract=extract;out.base=m
  return out
 R.ind=ind;R.coind=coind

def fused_mate(m,p,q,s,r):
 if p==0:return R.mate(m,p,q,s,r)
 fr=R.Fi(m,r);src=R.Ei(fr,q);ep=R.Ei(src,p)
 cross=R.T(fr,p,q,s,r)
 cap=R.Em(R.counit(m,r),R.Ei(fr,r),m,s)
 target=R.Fi(R.Ei(m,s),p)
 raw_unit=S.Matrix.vstack(*src.act)
 # Functoriality fuses F(cap)F(cross) with the coinduction unit.
 return (-1)**ep.idx[0]*target.extract*R.kron(S.eye(R.C[target.idx].n),cap*cross)*raw_unit

def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--probe',type=int,default=2)
 a=S.Integer(parser.parse_args().probe)
 if not a:parser.error('probe must be nonzero')
 configure(a)
 use_free_coordinates()
 m=R.regular((0,0))
 # Nonzero EF branches (A after B*, B after B*) and FE branches (A* after A, B* after A).
 src=[R.Ei(R.Fi(m,1),q) for q in (0,1)]
 tar=[R.Fi(R.Ei(m,0),p) for p in (0,1)]
 print('constructing16D reservoir/probe mate block',flush=True)
 C=fused_mate(m,0,1,0,1)
 print('constructing64D mixed mate block',flush=True)
 M=fused_mate(m,1,0,0,1)
 sigma=S.BlockMatrix([[S.zeros(tar[0].n,src[0].n),C],
                     [M,S.zeros(tar[1].n,src[1].n)]]).as_explicit()
 inv=sigma.inv()
 assert sigma*inv==S.eye(80)==inv*sigma
 U=S.Matrix.vstack(R.unit(m,0),S.zeros(tar[1].n,m.n))
 Vcap=S.Matrix.hstack(S.zeros(m.n,src[0].n),R.counit(m,1))
 X=S.diag(*[R.dot(R.Fi(m,1),q) for q in (0,1)])
 moments=[Vcap*X**r*inv*U for r in range(8)]
 delta=R.lmul(R.C[m.idx],R.kron(R.A[0].coord(V.matrix({(0,0,1):1})),R.B[0].one))
 epsilon=R.lmul(R.C[m.idx],R.kron(R.A[0].coord(V.matrix({(0,1,0):1})),R.B[0].one))
 t=S.Symbol('t');scalar=S.series(1/(1+a*t*t)**2,t,0,10).removeO()
 expected=[]
 for n in range(1,9):
  value=S.expand(scalar).coeff(t,n)*S.eye(4)
  value+=S.expand(t*t*scalar).coeff(t,n)*epsilon
  value-=S.expand(t*scalar).coeff(t,n)*delta
  value-=S.expand(t**3*scalar).coeff(t,n)*delta*epsilon
  expected.append(value)
 assert moments==expected
 assert moments[0]==-delta and moments[1]==epsilon-2*a*S.eye(4)
 odd=moments[0];even=2*a*S.eye(4)+moments[1]
 assert even==epsilon and (odd*even).rank()==1
 assert S.Matrix.hstack(*[b.reshape(16,1) for b in (S.eye(4),odd,even,odd*even)]).rank()==4
 # All-order moment recurrence comes from the probe polynomial on the relevant cup image.
 assert (X**4+2*a*X**2+a*a*S.eye(80))*inv*U==S.zeros(80,4)
 for r in range(4):assert moments[r+4]+2*a*moments[r+2]+a*a*moments[r]==S.zeros(4)
 print('PASS actual80D height-zero mate and two-sided inverse; probe a=',a,flush=True)
 print('PASS normalized bubble series (1-delta*t)(1+epsilon*t^2)/(1+a*t^2)^2',flush=True)
 print('PASS odd=-delta, e1=epsilon-2a; independent1,odd,e1+2a,odd*(e1+2a)',flush=True)
 print('SCOPE: actual one-colour compensation corner; no global spectral comparison claim',flush=True)

if __name__=='__main__':main()
