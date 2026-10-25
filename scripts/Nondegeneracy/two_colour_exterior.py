# /// script
# requires-python = ">=3.10"
# dependencies = ["sympy==1.14.0"]
# ///
"""Two independent actual bubble composites in the supertensor product.

Run: uv run --no-project --script scripts/Nondegeneracy/two_colour_exterior.py
Uses the coupled rank-one inverse, not spectator odd scalars. The checks do
NOT construct all two-colour KLR crossings or establish their braid relations.
The intended datum for this product pilot is disconnected; connected
Cartan interactions require additional work. Runtime: several minutes.
"""
import sympy as S
import nonvacuum_exterior as R


def coupled_data():
 m=R.regular((1,1))
 branches=[(q,r) for q in (0,1) for r in (0,1)]
 src=[R.Ei(R.Fi(m,r),q) for q,r in branches]
 tar=[R.Fi(R.Ei(m,s),p) for p,s in branches]
 blocks=[]
 for p,s in branches:
  row=[]
  for q,r in branches:
   if sorted((p,q))==sorted((s,r)):
    print('constructing coupled mate',p,q,s,r,flush=True)
    row.append(R.mate(m,p,q,s,r))
   else:
    row.append(R.Z(tar[branches.index((p,s))].n,src[branches.index((q,r))].n))
  blocks.append(row)
 sigma=S.BlockMatrix(blocks).as_explicit()
 inv=sigma.inv()
 assert inv*sigma==R.I(sigma.rows)==sigma*inv
 unit=S.Matrix.vstack(*[R.unit(m,p) if p==s else R.Z(n.n,m.n)
   for (p,s),n in zip(branches,tar)])
 cap=S.Matrix.hstack(*[R.counit(m,q) if q==r else R.Z(m.n,n.n)
   for (q,r),n in zip(branches,src)])
 dot=S.diag(*[R.dot(R.Fi(m,r),q) for q,r in branches])
 delta=R.lmul(R.C[m.idx],R.kron(R.A[1].coord(R.ad),R.B[1].one))
 bubble=cap*inv*unit
 assert bubble==-delta and bubble.rank()==4
 return m,unit,cap,sigma,inv,dot,bubble


def main():
 m,u,v,sigma,inv,x,bubble=coupled_data()
 identity=R.I(m.n);parity=R.paritydiag(m.ps)
 # Tensoring an odd map into the SECOND factor supplies the first parity.
 # Cups/caps are even, so no parity occurs in their tensor lifts.
 ui=R.kron(u,identity);vi=R.kron(v,identity)
 uj=R.kron(identity,u);vj=R.kron(identity,v)
 mi=R.kron(sigma,identity);ni=R.kron(inv,identity)
 mj=R.kron(parity,sigma);nj=R.kron(parity,inv)
 assert mi*ni==R.I(mi.rows)==ni*mi
 assert mj*nj==R.I(mj.rows)==nj*mj
 bi=vi*ni*ui;bj=vj*nj*uj
 assert bi==R.kron(bubble,identity)
 assert bj==R.kron(parity,bubble)
 assert bi*bi==R.Z(bi.rows) and bj*bj==R.Z(bj.rows)
 assert bi*bj+bj*bi==R.Z(bi.rows)
 assert bi.rank()==32 and bj.rank()==32 and (bi*bj).rank()==16
 print('two actual coupled bubbles: dimensions',bi.rows,'ranks',bi.rank(),bj.rank(),
       'product rank',(bi*bj).rank(),flush=True)
 print('square-zero and anticommutation PASS; product NONZERO',flush=True)
 # Native h=0 even bubble generator betaDGen(some n) is V X^(2n+1) inv U.
 moments=[v*x**r*inv*u for r in range(9)]
 assert x**7-x**3==R.Z(x.rows)
 # Strong recurrence on the cup image proves the displayed infinite series.
 assert x**5*inv*u==x**3*inv*u
 for moment in moments:
  assert moment==R.lmul(R.C[m.idx],moment*R.C[m.idx].one)
 z=R.lmul(R.C[m.idx],R.I(m.n)[:,6]) # left multiplication by x delta
 assert moments[1]==2*identity-3*z
 for r in range(2,len(moments)):
  assert moments[r]==(2*bubble if r%2==0 else 2*identity-6*z)
 for n in range(1,4):
  assert moments[2*n]==bubble*moments[2*n-1]
 assert all(moments[2*i+1]*moments[2*j+1]==moments[2*j+1]*moments[2*i+1]
            for i in range(4) for j in range(4))
 for r in range(2):
  assert moments[r+5]-moments[r+3]==R.Z(m.n)
 for r,b in enumerate(moments):
  print('moment coefficient vector',r,list(b*R.C[m.idx].one),flush=True)
  print('dotted moment',r,'rank',b.rank(),'scalar identity',
        b==identity,'negative identity',b==-identity,'equals odd bubble',b==bubble,
        'negative odd bubble',b==-bubble,flush=True)
 print('finite reservoir/probe moment recurrence B[r+5]=B[r+3] PASS',flush=True)
 print('Scope: actual tensor bubble composites; mixed-colour KLR braid coherence remains open.',flush=True)

if __name__=='__main__':main()
