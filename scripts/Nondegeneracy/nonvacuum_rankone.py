# /// script
# requires-python = ">=3.10"
# dependencies = ["sympy==1.14.0"]
# ///
"""Actual degree-two odd EF/FE mate on right supermodules.

Run: uv run --no-project --script scripts/Nondegeneracy/nonvacuum_rankone.py
This finite calculation is not a general action or a nondegeneracy proof.
"""
import sympy as S
from functools import lru_cache
I=S.eye
Z=S.zeros

def kron(a,b): return S.kronecker_product(a,b)
def cols(vs,n): return S.Matrix.hstack(*vs) if vs else Z(n,0)
def sign(p): return (-1)**(p%2)
def paritydiag(ps): return S.diag(*[sign(p) for p in ps])

class Alg:
 def __init__(self, mats, ps):
  self.n=len(ps); self.ps=ps; self.mats=mats
  flat=cols([S.Matrix(m).reshape(m.rows*m.cols,1) for m in mats],mats[0].rows**2)
  self.coord=lambda m: flat.gauss_jordan_solve(S.Matrix(m).reshape(m.rows*m.cols,1))[0]
  self.mul=[[self.coord(u*v) for v in mats] for u in mats]
  self.one=self.coord(I(mats[0].rows))

e00=S.Matrix([[1,0],[0,0]]); e11=S.Matrix([[0,0],[0,1]])
e01=S.Matrix([[0,1],[0,0]]); e10=S.Matrix([[0,0],[1,0]])
A=[Alg([I(1)],[0]),Alg([I(2),e10],[0,1]),Alg([e00,e11,e01,e10],[0,0,1,1])]
B=[Alg([I(1)],[0]),Alg([I(2),e01+e10],[0,1]),Alg([e00,e11,e01,e10],[0,0,1,1])]
class TensorAlg:
 def __init__(self,a,b):
  self.a=a;self.b=b;self.n=a.n*b.n;self.ps=[(p+q)%2 for p in a.ps for q in b.ps]
  self.one=kron(a.one,b.one)
  self.mul=[[sign(b.ps[j]*a.ps[k])*kron(a.mul[i][k],b.mul[j][l]) for k in range(a.n) for l in range(b.n)] for i in range(a.n) for j in range(b.n)]
C={(a,b):TensorAlg(A[a],B[b]) for a in range(3) for b in range(3)}
def inclusion(old,new):
 aa,bb=old; cc,dd=new
 def inc(tower,i,j):
  if i==j:return I(tower[i].n)
  if i==0:return tower[j].one
  return cols([tower[j].coord(m) for m in tower[i].mats],tower[j].n)
 return kron(inc(A,aa,cc),inc(B,bb,dd))
def lmul(c,v):return cols([sum((v[i]*c.mul[i][j] for i in range(c.n)),Z(c.n,1)) for j in range(c.n)],c.n)
def rmul(c,v):return cols([sum((v[j]*c.mul[i][j] for j in range(c.n)),Z(c.n,1)) for i in range(c.n)],c.n)
class Mod:
 # Coordinate maps populated by the induction or coinduction constructor.
 Q: S.MatrixBase
 sec: S.MatrixBase
 H: S.MatrixBase
 extract: S.MatrixBase
 base: 'Mod'
 def __init__(self,idx,ps,act,name=''):
  self.idx=idx;self.ps=ps;self.n=len(ps);self.act=act;self.name=name
 def action(self,v):return sum((v[i]*self.act[i] for i in range(len(self.act))),Z(self.n))
def regular(idx):
 c=C[idx];return Mod(idx,c.ps,[rmul(c,I(c.n)[:,j]) for j in range(c.n)],'regular')
@lru_cache(None)
def shift(m,k):
 k%=2
 if not k:return m
 return Mod(m.idx,[(p+k)%2 for p in m.ps],m.act,'Pi '+m.name)
@lru_cache(None)
def res(m,idx):
 inc=inclusion(idx,m.idx)
 return Mod(idx,m.ps,[m.action(inc[:,j]) for j in range(inc.cols)],'res '+m.name)

@lru_cache(None)
def ind(m,idx):
 c=C[m.idx];d=C[idx];inc=inclusion(m.idx,idx);n=m.n*d.n
 rel=[]
 for j in range(c.n):
  mat=kron(m.act[j],I(d.n))-kron(I(m.n),lmul(d,inc[:,j]))
  rel.extend(mat.columnspace())
 # Quotient via annihilator and pivot-column representatives; homogeneous equations.
 R=cols(rel,n)
 Q=cols(R.T.nullspace(),n).T
 piv=Q.rref()[1]; sec=cols([I(n)[:,j] for j in piv],n)
 Q=(Q*sec).inv()*Q
 ps0=[(p+q)%2 for p in m.ps for q in d.ps]
 out=Mod(idx,[ps0[j] for j in piv],[Q*kron(I(m.n),rmul(d,I(d.n)[:,j]))*sec for j in range(d.n)],'ind '+m.name)
 out.Q=Q;out.sec=sec;out.base=m
 return out

@lru_cache(None)
def coind(m,idx):
 # Hom_C(D,M), vectorization by D input first, M output second.
 c=C[m.idx];d=C[idx];inc=inclusion(m.idx,idx)
 eq=[]
 for j in range(c.n):
  eq.append(kron(rmul(d,inc[:,j]).T,I(m.n))-kron(I(d.n),m.act[j]))
 E=S.Matrix.vstack(*eq)
 basis=E.nullspace(); H=cols(basis,d.n*m.n)
 psraw=[(q+p)%2 for q in d.ps for p in m.ps]
 ps=[]
 for v in basis:
  pp={psraw[i] for i in range(len(v)) if v[i]};assert len(pp)==1;ps.append(pp.pop())
 piv=H.T.rref()[1];extract=I(H.rows)[list(piv),:]; inv=(extract*H).inv()*extract
 out=Mod(idx,ps,[inv*kron(lmul(d,I(d.n)[:,j]).T,I(m.n))*H for j in range(d.n)],'coind '+m.name)
 out.H=H;out.extract=inv;out.base=m
 return out

def Ei(m,t):
 a,b=m.idx
 return ind(m,(a+1,b)) if t==0 else shift(res(m,(a,b-1)),a%2)
def Fi(m,t):
 a,b=m.idx
 return res(m,(a-1,b)) if t==0 else coind(shift(m,a%2),(a,b+1))
def Em(f,m,n,t,p=0):
 if t==0:return Ei(n,t).Q*kron(f,I(C[Ei(n,t).idx].n))*Ei(m,t).sec
 return sign(m.idx[0]*p)*f
def Fm(f,m,n,t,p=0):
 if t==0:return f
 mm=Fi(m,t);nn=Fi(n,t)
 return sign(m.idx[0]*p)*nn.extract*kron(I(C[mm.idx].n),f)*mm.H

def unit(m,t):
 e=Ei(m,t);f=Fi(e,t)
 if t==0:return e.Q*kron(I(m.n),C[e.idx].one)
 d=C[m.idx]
 raw=S.Matrix.vstack(*m.act)
 return f.extract*raw

def counit(m,t):
 f=Fi(m,t);e=Ei(f,t)
 if t==0:return S.Matrix.hstack(*[cols([m.act[j][:,i] for j in range(C[m.idx].n)],m.n) for i in range(m.n)])*e.sec
 return kron(C[f.idx].one.T,I(m.n))*f.H

def dot(m,t):
 a,b=m.idx;e=Ei(m,t)
 if t==0:
  d=C[e.idx];x=A[a+1].coord(e10)
  xi=kron(x,B[b].one)
  return e.Q*kron(paritydiag(m.ps),lmul(d,xi))*e.sec
 eta=kron(A[a].one,B[b].coord(e01+e10 if b==1 else -e01+e10))
 return sign(a)*m.action(eta)*paritydiag(m.ps)

def collapseAA(m):
 e=Ei(m,0);ee=Ei(e,0);d=C[ee.idx];inc=inclusion(e.idx,ee.idx)
 # Collapse m tensor intermediate algebra tensor final algebra.
 c=C[e.idx]; mult=cols([lmul(d,inc[:,j])[:,k] for j in range(c.n) for k in range(d.n)],d.n)
 direct=ind(m,ee.idx)
 K=direct.Q*kron(I(m.n),mult)*kron(e.sec,I(d.n))*ee.sec
 assert K.rows==K.cols and K.det()!=0
 return K,direct

def mixedJ(m):
 # AB = A after B; BA = B after A. Raw comparison m tensor d -> m tensor incl(d).
 b=Ei(m,1);ab=Ei(b,0);a=Ei(m,0);ba=Ei(a,1)
 inc=inclusion(ab.idx,a.idx)
 J=a.Q*kron(I(m.n),inc)*ab.sec
 assert J.rows==J.cols and J.det()!=0
 return J

@lru_cache(None)
def T(m,p,q,s,r):
 # E_p E_q -> E_s E_r, odd.
 src=Ei(Ei(m,q),p);tar=Ei(Ei(m,r),s)
 if p==q==s==r==0:
  K,direct=collapseAA(m);d=C[direct.idx]
  tau=kron(A[2].coord(e01),B[m.idx[1]].one)
  raw=direct.Q*kron(paritydiag(m.ps),lmul(d,tau))*direct.sec
  out=K.inv()*raw*K
 elif p==q==s==r==1:
  tau=kron(A[m.idx[0]].one,B[2].coord(e01))
  out=-m.action(tau)*paritydiag(m.ps)
 else:
  assert p!=q and s!=r
  J=mixedJ(m);b=Ei(m,1);ab=Ei(b,0)
  X=dot(b,0);Y=Em(dot(m,1),b,b,0,1)
  D=X*X-Y*Y;aa=(X-Y)*D.inv();qq=(X*X+Y*Y)*D.inv()**2
  out={(0,1,0,1):aa,(0,1,1,0):J,(1,0,0,1):-qq*J.inv(),(1,0,1,0):-J*aa*J.inv()}[p,q,s,r]
 assert out.shape==(tar.n,src.n)
 # Check right linearity and odd grading for every crossing component.
 assert all(out*src.act[j]==tar.act[j]*out for j in range(len(src.act)))
 assert paritydiag(tar.ps)*out==-out*paritydiag(src.ps)
 return out

def check_adj(m,t):
 e=Ei(m,t);f=Fi(m,t)
 assert counit(e,t)*Em(unit(m,t),m,Fi(e,t),t)==I(e.n)
 assert Fm(counit(m,t),Ei(f,t),m,t)*unit(f,t)==I(f.n)

def check_up(m,words):
 mods=[Ei(Ei(m,q),p) for p,q in words]
 X=S.diag(*[dot(Ei(m,q),p) for p,q in words])
 Y=S.diag(*[Em(dot(m,q),Ei(m,q),Ei(m,q),p,1) for p,q in words])
 TT=S.BlockMatrix([[T(m,p,q,s,r) for p,q in words] for s,r in words]).as_explicit()
 assert X*Y+Y*X==Z(X.rows)
 assert TT*X+Y*TT==I(X.rows)
 assert TT*Y+X*TT==I(X.rows)
 assert TT*TT==Z(X.rows)
 print('upward relations PASS',m.idx,words,'dimension',X.rows,flush=True)

def mate(m,p,q,s,r):
 fr=Fi(m,r);src=Ei(fr,q)
 ep=Ei(src,p);etarget=Ei(Ei(fr,r),s)
 u=unit(src,p)
 cross=Fm(T(fr,p,q,s,r),ep,etarget,p,1)
 cap=Em(counit(m,r),Ei(fr,r),m,s,0)
 finish=Fm(cap,etarget,Ei(m,s),p,0)
 return finish*cross*u

def main():
 m=regular((1,1))
 print('regular input dimension',m.n,flush=True)
 for t in (0,1):
  check_adj(m,t);print('adjunction triangles PASS',t,flush=True)
 for r in (0,1):
  n=Fi(m,r)
  check_up(n,[(0,1),(1,0)])
  check_up(n,[(0,0)] if r==0 else [(1,1)])
 branches=[(q,r) for q in (0,1) for r in (0,1)]
 src=[Ei(Fi(m,r),q) for q,r in branches]
 tar=[Fi(Ei(m,s),p) for p,s in branches]
 blocks=[]
 for p,s in branches:
  row=[]
  for q,r in branches:
   if sorted((p,q))==sorted((s,r)):
    v=mate(m,p,q,s,r)
   else:v=Z(tar[branches.index((p,s))].n,src[branches.index((q,r))].n)
   row.append(v)
  blocks.append(row)
 sigma=S.BlockMatrix(blocks).as_explicit()
 print('EF branch dimensions',[(b,n.n) for b,n in zip(branches,src)],flush=True)
 print('FE branch dimensions',[(b,n.n) for b,n in zip(branches,tar)],flush=True)
 print('sigma shape',sigma.shape,'rank',sigma.rank(),'det',sigma.det(),flush=True)
 assert sigma.inv()*sigma==I(sigma.rows) and sigma*sigma.inv()==I(sigma.rows)
 print('two-sided inverse PASS',flush=True)
 # Central 2x2 block: AA* and BB* to A*A and B*B.
 central=S.BlockMatrix([[blocks[0][0],blocks[0][3]],[blocks[3][0],blocks[3][3]]]).as_explicit()
 print('central block',central.shape,'rank',central.rank(),'det',central.det(),flush=True)
 sa,cc,dd,sb=blocks[0][0],blocks[0][3],blocks[3][0],blocks[3][3]
 print('factor mate ranks',sa.rank(),sb.rank(),'cross diagonal-mate ranks',cc.rank(),dd.rank(),flush=True)
 feedback=dd*sa.inv()*cc*sb.inv(); H=I(sb.rows)-feedback
 assert feedback==Z(feedback.rows) and H==I(H.rows)
 print('feedback rank',feedback.rank(),'feedback squared zero',feedback**2==Z(feedback.rows),'H rank',H.rank(),'H det',H.det(),flush=True)
 for ir,(p,s) in enumerate(branches):
  for ic,(q,r) in enumerate(branches):
   v=blocks[ir][ic]
   if not v.is_zero_matrix:
    assert src[ic].idx==tar[ir].idx
    assert all(v*src[ic].act[j]==tar[ir].act[j]*v for j in range(len(src[ic].act)))
    assert paritydiag(tar[ir].ps)*v==-v*paritydiag(src[ic].ps)
 print('all mate blocks rightlinear and odd PASS',flush=True)
 for j,pf in enumerate(C[m.idx].ps):
  f=lmul(C[m.idx],I(m.n)[:,j])
  ef=S.diag(*[Em(Fm(f,m,m,r,pf),Fi(m,r),Fi(m,r),q,pf) for q,r in branches])
  fe=S.diag(*[Fm(Em(f,m,m,s,pf),Ei(m,s),Ei(m,s),p,pf) for p,s in branches])
  assert sigma*ef==sign(pf)*fe*sigma
 print('regular-module homogeneous supernaturality PASS',flush=True)
 # Compare both off-diagonal mates with the proposed ordered dotted composites.
 def dotted_unit(t,r):
  e=Ei(m,t)
  return Fm(dot(m,t)**r,e,e,t,r%2)*unit(m,t)
 def dotted_cap(t,r):
  return counit(m,t)*dot(Fi(m,t),t)**r
 assert dot(m,0)**2==Z(Ei(m,0).n)
 assert dot(Fi(m,0),0)**2==Z(Ei(Fi(m,0),0).n)
 cp=sum((sign(r)*dotted_unit(0,r)*dotted_cap(1,-r-1) for r in range(2)),Z(*cc.shape))
 dp=sum((sign(r)*dotted_unit(1,-r-1)*dotted_cap(0,r) for r in range(2)),Z(*dd.shape))
 assert cc==cp and dd==dp
 print('actual diagonal-mate expansions C and D PASS',flush=True)
 right=regular((0,1))
 right_mate=mate(right,1,1,1,1)
 assert right_mate.shape==(4,4) and right_mate.det()==-1
 assert right_mate.inv()*right_mate==I(4)==right_mate*right_mate.inv()
 print('pure-right mate',right_mate.shape,'rank',right_mate.rank(),'det',right_mate.det(),flush=True)
if __name__=='__main__':main()
