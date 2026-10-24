"""Exact determinant checks for the proposed factor-companion formulas.
These finite matrix tests are not the abstract nilpotence proof.
"""
from fractions import Fraction as F
import json

def mm(a,b):
    return [[sum(a[i][k]*b[k][j] for k in range(len(b)))
             for j in range(len(b[0]))] for i in range(len(a))]

def ident(n): return [[int(i==j) for j in range(n)] for i in range(n)]
def power(a,s):
    b=ident(len(a))
    for _ in range(s): b=mm(b,a)
    return b

def det(a):
    a=[[F(v) for v in row] for row in a]; d=F(1)
    for j in range(len(a)):
        p=next((i for i in range(j,len(a)) if a[i][j]),None)
        if p is None: return F(0)
        if p!=j: a[p],a[j]=a[j],a[p]; d=-d
        q=a[j][j]; d*=q
        a[j]=[v/q for v in a[j]]
        for i in range(j+1,len(a)):
            q=a[i][j]; a[i]=[v-q*w for v,w in zip(a[i],a[j])]
    return d

x=[[0,1,2],[0,0,3],[0,0,0]]
w=[[1],[2],[-1]]
v=[[2,-1,3]]
c=[mm(mm(v,power(x,s)),w)[0][0] for s in range(len(x))]
checked=0
for a in range(5):
    b=[(-1)**j*(j+1) for j in range(a)]
    size=len(x)+a
    for orientation in ([0] if a==0 else [-1,1]):
        M=[[0]*size for _ in range(size)]
        for i in range(3):
            for j in range(3): M[i][j]=-x[i][j]
        if a==0:
            outer=mm(w,v)
            for i in range(3):
                for j in range(3): M[i][j]+=outer[i][j]
        elif orientation==-1:
            for i in range(3): M[i][-1]=w[i][0]; M[3][i]=v[0][i]
            for j in range(a-1): M[3+j+1][3+j]=1
            for j in range(a): M[3+j][-1]+=b[j]
        else:
            # Transpose the small companion, interchanging the two rectangular maps.
            for i in range(3): M[i][3]=w[i][0]; M[-1][i]=v[0][i]
            for j in range(a-1): M[3+j][3+j+1]=1
            for j in range(a): M[-1][3+j]+=b[j]
        for z in range(-3,4):
            lhs=det([[int(i==j)-z*M[i][j] for j in range(size)] for i in range(size)])
            rhs=1-sum(b[j]*z**(a-j) for j in range(a))
            rhs-=sum((-1)**s*c[s]*z**(a+1+s) for s in range(len(c)))
            assert lhs==rhs,(a,orientation,z,lhs,rhs)
            checked+=1
# Source slide: y sigma - q sigma x = u v.  In the positive-weight
# companion the unnormalized upper-right entry is -q u, not always +u.
# This two-dimensional nilpotent example catches the incorrect even sign.
source_sign_cases=0
for q in (-1,1):
    dot=[[0,-q],[0,0]]
    sigma=[[1,0]]
    uv=[[0,1]]
    assert [[-q*z for z in row] for row in mm(sigma,dot)]==uv
    assert mm(dot,dot)==[[0,0],[0,0]]
    assert dot[0][1]==-q
    if q==1:
        assert dot[0][1]!=1  # Reject changing only the diagonal signs.
    normalized_Q=[[-q,0],[0,1]]
    assert mm(normalized_Q,normalized_Q)==ident(2)
    assert mm(mm(normalized_Q,dot),normalized_Q)==[[0,1],[0,0]]
    source_sign_cases+=1
print(json.dumps({'exact_cases':checked,'all_passed':True,'transfer_coefficients':c,
                  'source_sign_cases':source_sign_cases,'even_sign_mutation_rejected':True}))
