# /// script
# requires-python = ">=3.10"
# dependencies = ["sympy==1.14.0"]
# ///
"""Actual vacuum inversion/bubbles with an independent even parameter.

N=4, B=Q[epsilon]/epsilon^2 tensor Lambda(delta),
f=x^4+x^3 delta+x^2 epsilon+x delta epsilon. The source constant chi2=0,
chi1=epsilon, d=-delta. Checks boundary inversion and the Frobenius
induction/coinduction comparison, not the full higher-cutoff SKM action.
"""
import sympy as S
from functools import lru_cache

basis=[(a,b,e) for a in range(4) for b in (0,1) for e in (0,1)]
base=[(0,b,e) for b in (0,1) for e in (0,1)]
index={m:j for j,m in enumerate(basis)}
I=S.eye(16);Z=S.zeros(16)

def add(p,q):
 r=p.copy()
 for m,c in q.items():r[m]=r.get(m,0)+c
 return {m:c for m,c in r.items() if c}

@lru_cache(None)
def reduce(a,b,e):
 if b>1 or e>1:return {}
 if a<4:return {(a,b,e):1}
 r={}
 for aa,bb,ee in ((a-1,b,e+1),(a-2,b+1,e),(a-3,b+1,e+1)):
  r=add(r,{m:-c for m,c in reduce(aa,bb,ee).items()})
 return r

def multiply(p,q):
 r={}
 for (a,b,e),c in p.items():
  for (A,B,E),d in q.items():
   r=add(r,{m:c*d*(-1)**(e*A)*v for m,v in reduce(a+A,b+B,e+E).items()})
 return r

def vec(p):return S.Matrix([p.get(m,0) for m in basis])
def matrix(p,left=True):
 return S.Matrix.hstack(*[vec(multiply(p,{m:1}) if left else multiply({m:1},p)) for m in basis])
def parity(ps):return S.diag(*[(-1)**p for p in ps])

def main():
 elems=[{m:1} for m in basis]
 for a in elems:
  for b in elems:
   for c in elems:assert multiply(multiply(a,b),c)==multiply(a,multiply(b,c))
 X=matrix({(1,0,0):1});D=matrix({(0,0,1):1});E=matrix({(0,1,0):1})
 assert D*D==E*E==Z and D*X+X*D==Z and E*X==X*E
 assert X**4+X**3*D+X**2*E+X*D*E==Z
 assert (D*E).rank()==4
 pa=[(a+e)%2 for a,b,e in basis];pb=[e for a,b,e in base]
 inc=S.Matrix.hstack(*[vec({m:1}) for m in base])
 tr=S.zeros(4,16)
 for j,(a,b,e) in enumerate(basis):
  if a==3:tr[base.index((0,b,e)),j]=1
 assert parity(pb)*tr==-tr*parity(pa)
 # Dotted cups identify FE(vacuum)=A with four shifted copies of B.
 cups=[X**r*inc for r in range(4)]
 inversion=S.Matrix.hstack(*cups)
 inverse=inversion.inv()
 assert inversion*inverse==I==inverse*inversion
 assert inverse[12:16,:]==tr
 assert parity(pa)*inversion==inversion*parity([p+r for r in range(4) for p in pb])
 # Frobenius comparison a -> (b -> tr(ab)), with explicit right B-linearity.
 pairing=S.Matrix.vstack(*[tr*matrix({b:1},left=False) for b in basis])
 assert pairing.rank()==16
 assert parity([p+q for p in pa for q in pb])*pairing==-pairing*parity(pa)
 for c in base:
  rightA=matrix({c:1},left=False)
  rightB=tr*matrix({c:1},left=False)*cups[3]
  # Hom_B(A,B) is the kernel of right-linearity constraints.
  relation=S.kronecker_product(rightA.T,S.eye(4))-S.kronecker_product(S.eye(16),rightB)
  assert relation*pairing==S.zeros(64,16)
 for c in basis:
  assert S.kronecker_product(matrix({c:1}).T,S.eye(4))*pairing==pairing*matrix({c:1},left=False)
 # Establish the entire Hom space dimension, not only an injective pairing.
 constraints=[]
 for c in base:
  rightA=matrix({c:1},left=False)
  rightB=tr*matrix({c:1},left=False)*cups[3]
  constraints.append(S.kronecker_product(rightA.T,S.eye(4))-S.kronecker_product(S.eye(16),rightB))
 assert 64-S.Matrix.vstack(*constraints).rank()==16
 moments=[tr*X**r*inc for r in range(7)]
 d0=tr*matrix({(0,0,1):1},left=False)*cups[3];e0=tr*E*cups[3]
 assert moments[3]==S.eye(4)
 assert moments[4]==-d0 and moments[5]==-e0 and moments[6]==d0*e0
 # Native source signs at weight -4: oddBubble=tr x4; beta(e1)=-tr x5.
 odd=moments[4];even=-moments[5];mixed=-moments[6]
 assert odd*even==mixed and mixed.rank()==1
 assert odd*odd==even*even==S.zeros(4) and odd*even==even*odd
 assert S.Matrix.hstack(*[m.reshape(16,1) for m in (S.eye(4),odd,even,mixed)]).rank()==4
 print('PASS associative16D cyclotomic algebra; delta*epsilon nonzero')
 print('PASS actual vacuum dotted-cup inversion; odd Frobenius Hom comparison isomorphism')
 print('PASS normalized bubbles: odd=-delta, e1=epsilon, odd*e1=-delta*epsilon; mixed rank1')
 print('PASS independent operators 1, odd, e1, odd*e1; no full higher-cutoff action claim')

if __name__=='__main__':main()
