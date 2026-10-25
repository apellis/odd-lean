# /// script
# requires-python = ">=3.10"
# dependencies = ["sympy==1.14.0"]
# ///
"""One coherent disconnected two-colour finite categorical pilot.

Two genuine degree-two exterior cyclotomic towers. E_j and F_j acquire a
parity shift equal to the first colour height; all functor maps use the
resulting super signs. Upward crossings and EF mates are built from the
SAME functors, units and counits. Mixed crossings are canonical odd maps
between opposite parity shifts, not an independently attached matrix model.
Checks every admissible upward word of lengths2--4 and all legal adjunction
and inversion corners in the nine-weight grid, actual middle-weight bubbles,
and homogeneous naturality.
This finite window is not an asserted arbitrary-cutoff/general-Cartan action.
"""
import nonvacuum_exterior as R
from dataclasses import dataclass
from functools import lru_cache
@dataclass(frozen=True)
class Obj:
 i:object
 j:object
 shift:int=0
 @property
 def size(self):return self.i.n*self.j.n
 @property
 def ps(self):return [(a+b+self.shift)%2 for a in self.i.ps for b in self.j.ps]
def height(o,c):return o.i.idx[0]%2 if c==1 else 0
@lru_cache(None)
def fun(o,c,which):
 f=R.Ei if which=='E' else R.Fi
 return Obj(f(o.i,0) if c==0 else o.i,f(o.j,0) if c==1 else o.j,(o.shift+height(o,c))%2)
def E(o,c):return fun(o,c,'E')
def F(o,c):return fun(o,c,'F')
@dataclass
class Map:
 src:Obj
 tgt:Obj
 i:object
 j:object
 a:int=0
 b:int=0
 scalar:int=1
 @property
 def degree(self):return (self.a+self.b+self.src.shift+self.tgt.shift)%2
 def matrix(self):
  return self.scalar*R.kron(self.i*(R.paritydiag(self.src.i.ps) if self.b%2 else R.I(self.src.i.n)),self.j)
def identity(o):return Map(o,o,R.I(o.i.n),R.I(o.j.n))
def compose(g,f):
 assert f.tgt==g.src
 return Map(f.src,g.tgt,g.i*f.i,g.j*f.j,(g.a+f.a)%2,(g.b+f.b)%2,
            g.scalar*f.scalar*(-1)**(g.b*f.a))
def whisker(f,c,which='E'):
 src=fun(f.src,c,which);tgt=fun(f.tgt,c,which)
 action=R.Em if which=='E' else R.Fm
 fi=action(f.i,f.src.i,f.tgt.i,0,f.a) if c==0 else f.i
 fj=action(f.j,f.src.j,f.tgt.j,0,f.b) if c==1 else f.j
 return Map(src,tgt,fi,fj,f.a,f.b,f.scalar*(-1)**(height(f.src,c)*f.degree))
def unit(o,c):
 return Map(o,F(E(o,c),c),R.unit(o.i,0) if c==0 else R.I(o.i.n),
            R.unit(o.j,0) if c==1 else R.I(o.j.n))
def cap(o,c):
 return Map(E(F(o,c),c),o,R.counit(o.i,0) if c==0 else R.I(o.i.n),
            R.counit(o.j,0) if c==1 else R.I(o.j.n))
def dot(o,c):
 out=E(o,c)
 return Map(out,out,R.dot(o.i,0) if c==0 else R.I(o.i.n),
            R.dot(o.j,0) if c==1 else R.I(o.j.n),1 if c==0 else 0,
            1 if c==1 else 0,(-1)**(o.shift+height(o,c)))
def cross(o,p,q):
 src=E(E(o,q),p);tgt=E(E(o,p),q)
 if p!=q:return Map(src,tgt,R.I(src.i.n),R.I(src.j.n))
 return Map(src,tgt,R.T(o.i,0,0,0,0) if p==0 else R.I(src.i.n),
            R.T(o.j,0,0,0,0) if p==1 else R.I(src.j.n),
            1 if p==0 else 0,1 if p==1 else 0,(-1)**o.shift)
def mate(o,p,q):
 # Crossing E_p E_q -> E_q E_p: source E_q F_p, target F_p E_q.
 fr=F(o,p);src=E(fr,q)
 u=unit(src,p)
 t=whisker(cross(fr,p,q),p,'F')
 c=whisker(whisker(cap(o,p),q),p,'F')
 return compose(c,compose(t,u))
def word(o,w):
 for c in reversed(w):o=E(o,c)
 return o
def crossing_in_word(o,w,r):
 inner=word(o,w[r+2:]);f=cross(inner,w[r],w[r+1])
 for c in reversed(w[:r]):f=whisker(f,c)
 return w[:r]+(w[r+1],w[r])+w[r+2:],f
def dot_in_word(o,w,r):
 f=dot(word(o,w[r+1:]),w[r])
 for c in reversed(w[:r]):f=whisker(f,c)
 return f
def path(o,w,rs):
 f=identity(word(o,w))
 for r in rs:
  w,g=crossing_in_word(o,w,r);f=compose(g,f)
 return w,f.matrix()
def check_upward():
 import itertools
 count=0
 for hi,hj in itertools.product(range(3),repeat=2):
  o=Obj(R.regular((hi,0)),R.regular((hj,0)))
  for length in range(2,5):
   for w in itertools.product((0,1),repeat=length):
    if w.count(0)>2-hi or w.count(1)>2-hj:continue
    count+=1
    dots=[dot_in_word(o,w,r).matrix() for r in range(length)]
    one=R.I(word(o,w).size);zero=R.Z(one.rows)
    for r in range(length):
     for q in range(r+1,length):assert dots[r]*dots[q]+dots[q]*dots[r]==zero
    for r in range(length-1):
     v,f=crossing_in_word(o,w,r);t=f.matrix();ys=[dot_in_word(o,v,q).matrix() for q in range(length)]
     assert R.paritydiag(f.tgt.ps)*t==-t*R.paritydiag(f.src.ps)
     assert t*dots[r]+ys[r+1]*t==(one if w[r]==w[r+1] else zero)
     assert ys[r]*t+t*dots[r+1]==(one if w[r]==w[r+1] else zero)
     for q in range(length):
      if q not in (r,r+1):assert t*dots[q]+ys[q]*t==zero
     _,back=crossing_in_word(o,v,r)
     assert back.matrix()*t==(zero if w[r]==w[r+1] else one)
    for r in range(length-2):assert path(o,w,(r,r+1,r))==path(o,w,(r+1,r,r+1))
    if length==4:assert path(o,w,(0,2))[1]==-path(o,w,(2,0))[1]
 print('PASS all',count,'admissible upward words of length2 through4 at all9 tower weights',flush=True)

def check_boundaries():
 for hi in range(3):
  for hj in range(3):
   o=Obj(R.regular((hi,0)),R.regular((hj,0)))
   for c,h in ((0,hi),(1,hj)):
    if h<2:
     eo=E(o,c)
     assert compose(cap(eo,c),whisker(unit(o,c),c)).matrix()==R.I(eo.size)
    if h>0:
     fo=F(o,c)
     assert compose(whisker(cap(o,c),c,'F'),unit(fo,c)).matrix()==R.I(fo.size)
    if h==0:
     u=unit(o,c);du=compose(whisker(dot(o,c),c,'F'),u)
     inversion=R.S.Matrix.hstack(u.matrix(),du.matrix())
    elif h==1:inversion=mate(o,c,c).matrix()
    else:
     v=cap(o,c);dv=compose(v,dot(F(o,c),c))
     inversion=R.S.Matrix.vstack(v.matrix(),dv.matrix())
    assert inversion.rows==inversion.cols
    inverse=inversion.inv()
    assert inverse*inversion==R.I(inversion.rows)==inversion*inverse
   for p,q in ((0,1),(1,0)):
    hs=(hi,hj)
    if hs[p]>0 and hs[q]<2:
     f=mate(o,p,q);inversion=f.matrix();inverse=inversion.inv()
     assert inversion.rows==inversion.cols
     assert inverse*inversion==R.I(inversion.rows)==inversion*inverse
     assert inversion==(1 if p==0 else (-1)**(hi+1))*R.I(inversion.rows)
 print('PASS all legal adjunction triangles and same/mixed inversions at all9 tower weights',flush=True)
def main():
 check_upward()
 check_boundaries()
 o=Obj(R.regular((1,0)),R.regular((1,0)))
 bubbles=[]
 for c in (0,1):
  eo=E(o,c);fo=F(o,c)
  tri=compose(cap(eo,c),whisker(unit(o,c),c))
  assert tri.matrix()==R.I(eo.size)
  tri=compose(whisker(cap(o,c),c,'F'),unit(fo,c))
  assert tri.matrix()==R.I(fo.size)
  sigma=mate(o,c,c).matrix();inv=sigma.inv()
  assert sigma*inv==R.I(sigma.rows)==inv*sigma
  bubbles.append(cap(o,c).matrix()*inv*unit(o,c).matrix())
  print('colour',c,'samecolour mate',sigma.shape,'det',sigma.det(),'bubble rank',bubbles[-1].rank(),flush=True)
 for p,q in ((0,1),(1,0)):
  f=mate(o,p,q);m=f.matrix()
  assert m.rows==m.cols and m.inv()*m==R.I(m.rows)
  assert R.paritydiag(f.tgt.ps)*m==-m*R.paritydiag(f.src.ps)
  print('actual mixed mate',p,q,m.shape,'det',m.det(),flush=True)
 a,b=bubbles
 assert a*a==b*b==R.Z(o.size) and a*b+b*a==R.Z(o.size)
 assert (a*b).rank()==4
 print('PASS two ACTUAL bubbles and product rank4 on16D; both adjunctions and all tested inversions',flush=True)
 delta=R.lmul(R.C[(1,0)],R.kron(R.A[1].coord(R.ad),R.B[0].one))
 assert a==-R.kron(delta,R.I(4))
 assert b==-R.kron(R.paritydiag(o.i.ps),delta)
 base=R.C[(1,0)]
 for i in range(base.n):
  for j in range(base.n):
   f=Map(o,o,R.lmul(base,R.I(base.n)[:,i]),R.lmul(base,R.I(base.n)[:,j]),base.ps[i],base.ps[j])
   for p in (0,1):
    for q in (0,1):
     sigma=mate(o,p,q)
     ef=whisker(whisker(f,p,'F'),q)
     fe=whisker(whisker(f,q),p,'F')
     assert sigma.matrix()*ef.matrix()==(-1)**f.degree*fe.matrix()*sigma.matrix()
 print('PASS all16 homogeneous regular-module endomorphisms: both same/mixed mates supernatural',flush=True)

if __name__=='__main__':main()
