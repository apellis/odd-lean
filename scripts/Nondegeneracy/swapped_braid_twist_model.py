#!/usr/bin/env python3
"""Exact twist model of the swapped crossing entries; a consistency check, not a proof.

The swapped generators of `SwappedAssembly/Generators/Cross.lean` act on paths of letters,
each on the probe side (P) or the reservoir side (R).  This script models them on a skew
polynomial ring with one variable per letter (odd variables pairwise anticommute):

* a crossing of two distinct colours, or of one colour across the two sides, is the twist
  f -> (-1)^(p|f|) f, p the product of the two parities;
* the factor Q_ij = t_ij x^dn(ij) + t_ji y^dn(ji) + sum s_ij(p,q) x^p y^q sits on the PP/RR
  crossing from c1 > c2 and on the mixed RP -> PR entry;
* a same-side same-colour crossing is the (odd) Demazure operator;
* the mixed same-colour entries are a on RP -> RP, J on PR -> RP, -(a a J^-1) on RP -> PR and
  -(J a J^-1) on PR -> PR, with a = (y - x)^-1 (even) or (x - y)(x^2 - y^2)^-1 (odd),
  x the probe dot and y the reservoir dot: the Lean diagonal of `swappedCross`.

These are the parities, supernaturality and dot slides of the proved Lean lemmas, and the
model reproduces the proved slide relation and the proved braid blocks of the pattern iii.
It then checks the braid relation (1.9) with its correction (for i j i) on every block of
every three-letter word (iii, iji, iij, ijj, jii, jij, ijk), every parity assignment and
several values of the exponents dn, on all test monomials of degree at most 2, in exact
arithmetic.  With `flip` as second argument it negates a; then iii and the mixed jij blocks
fail, so the check is sensitive to the sign of the diagonal.

Usage: swapped_braid_twist_model.py iii,iji,iij,ijj,jii,jij,ijk [flip]
"""
from fractions import Fraction as Fr
import itertools, random, sys
class Ring:
    def __init__(s, names, par, Dkind):
        s.names=names; s.par=par; s.n=len(names); s.Dkind=Dkind
    def mono_mul(s,a,b):
        sg=0
        for k in range(s.n):
            for l in range(k+1,s.n):
                sg+= s.par[k]*s.par[l]*a[l]*b[k]
        return (-1)**(sg%2), tuple(x+y for x,y in zip(a,b))
    def mparity(s,m): return sum(e*p for e,p in zip(m,s.par))%2
    def mul(s,f,g):
        r={}
        for a,ca in f.items():
            for b,cb in g.items():
                sg,m=s.mono_mul(a,b); r[m]=r.get(m,0)+sg*ca*cb
        return {m:c for m,c in r.items() if c!=0}
    def add(s,f,g,cg=1):
        r=dict(f)
        for m,c in g.items(): r[m]=r.get(m,0)+cg*c
        return {m:c for m,c in r.items() if c!=0}
    def var(s,name,e=1):
        m=[0]*s.n; m[s.names.index(name)]=e; return {tuple(m):Fr(1)}
    def one(s): return {tuple([0]*s.n):Fr(1)}
    def tw(s,p,f): return {m:c*(-1)**(p*s.mparity(m)) for m,c in f.items()}
    def pw(s,f,e):
        r=s.one()
        for _ in range(e): r=s.mul(r,f)
        return r

COLS='ijk'
def build(par, dmat, seed=0, flip_a=False):
    # par: dict colour->parity ; dmat: dict (c1,c2)->dn
    rnd=random.Random(seed)
    names=[]; vpar=[]
    for c in COLS:
        for sd in 'PR':
            for o in range(3):
                names.append(f'{c}{sd}{o}'); vpar.append(par[c])
    R=Ring(names,vpar,None)
    t={}; s={}
    for c1 in COLS:
        for c2 in COLS:
            if c1!=c2: t[(c1,c2)]=Fr(rnd.randint(1,9))
    for c1 in COLS:
        for c2 in COLS:
            if c1<c2:
                for p in range(1,dmat[(c1,c2)]):
                    for q in range(1,dmat[(c2,c1)]):
                        v=0 if (p*par[c1])%2 or (q*par[c2])%2 else rnd.randint(-5,5)
                        s[(c1,c2,p,q)]=Fr(v); s[(c2,c1,q,p)]=Fr(v)
    for c1 in COLS:
        for c2 in COLS:
            if c1<c2 and dmat[(c1,c2)]==0: t[(c2,c1)]=t[(c1,c2)]
    E=dict(R=R,t=t,s=s,par=par,dn=dmat,flip=flip_a)
    return E

def var(path_word, sides, pos):
    c=path_word[pos]; sd=sides[pos]
    occ=sum(1 for k in range(pos) if path_word[k]==c and sides[k]==sd)
    return f'{c}{sd}{occ}'


def run(E, word, probe, res, verbose=False):
    R=E['R']; par=E['par']; dn=E['dn']; t=E['t']; s=E['s']
    one=R.one()
    # denominators: D_{x,y} for same-colour mixed pairs, keyed by (xname,yname)
    def Dpoly(x,y,p):
        X=R.var(x); Y=R.var(y)
        return R.add(Y,X,-1) if p==0 else R.add(R.pw(X,2),R.pw(Y,2),-1)
    # element: dict den-tuple -> poly
    def emul(f,g):
        r={}
        for d1,a in f.items():
            for d2,b in g.items():
                d=tuple(sorted(d1+d2)); r[d]=R.add(r.get(d,{}),R.mul(a,b))
        return {d:a for d,a in r.items() if a}
    def eadd(f,g,c=1):
        r=dict(f)
        for d,b in g.items(): r[d]=R.add(r.get(d,{}),b,c)
        return {d:a for d,a in r.items() if a}
    def etw(p,f): return {d:R.tw(p,a) for d,a in f.items()}
    def ecanon(f):
        dens=set()
        for d in f: dens|=set(d)
        # common denominator: product over distinct D of max power
        mx={}
        for d in f:
            for D in set(d): mx[D]=max(mx.get(D,0),d.count(D))
        tot={}
        for d,a in f.items():
            m=a
            for D,k in mx.items():
                m=R.mul(m,R.pw(Dpoly(*D),k-d.count(D)))
            tot=R.add(tot,m)
        return tot
    def L(g): return lambda f: emul(g,f)
    def tau(p): return lambda f: etw(p%2,f)
    def comp(*fs):
        def h(f):
            for g in fs: f=g(f)
            return f
        return h
    def plus(A,B,c=1): return lambda f: eadd(A(f),B(f),c)
    def sc(A,c): return lambda f: {d:{m:c*v for m,v in a.items()} for d,a in A(f).items()}
    zero=lambda f:{}
    def poly(p): return {():p}
    def Qword(c1,v1,c2,v2):
        if dn[(c1,c2)]==0 and dn[(c2,c1)]==0: return {m:t[(c1,c2)]*v for m,v in one.items()}
        q=R.add({m:t[(c1,c2)]*v for m,v in R.var(v1,dn[(c1,c2)]).items()},
                {m:t[(c2,c1)]*v for m,v in R.var(v2,dn[(c2,c1)]).items()})
        for p in range(1,dn[(c1,c2)]):
            for qq in range(1,dn[(c2,c1)]):
                c=s[(c1,c2,p,qq)]
                if c: q=R.add(q,R.mul(R.var(v1,p),R.var(v2,qq)),c)
        return q
    def demazure(u,v,p):
        q=(-1)**p
        def psi_mono(m):
            # m exponent tuple
            idx=next((k for k,e in enumerate(m) if e),None)
            if idx is None: return {}
            w=R.names[idx]; mm=list(m); mm[idx]-=1; mp={tuple(mm):Fr(1)}
            rest=psi_mono(tuple(mm))
            if w==u: return R.add(mp,R.mul(R.var(v),rest),q)
            if w==v: return R.add({k:q*c for k,c in R.mul(R.var(u),rest).items()},mp,-q)
            sg=(-1)**((R.par[idx]*p)%2)
            return {k:sg*c for k,c in R.mul(R.var(w),rest).items()}
        def op(f):
            r={}
            for d,a in f.items():
                nd=list(d)
                for D in d:
                    if u in D[:2] or v in D[:2]:
                        sw=lambda n: v if n==u else (u if n==v else n)
                        D2=(sw(D[0]),sw(D[1]),D[2])
                        a=R.mul(a,Dpoly(*D2)); nd.append(D2)
                d=tuple(sorted(nd))
                acc={}
                for m,c in a.items():
                    acc=R.add(acc,psi_mono(m),c)
                r[d]=R.add(r.get(d,{}),acc)
            return {d:a for d,a in r.items() if a}
        return op
    def entry(w,u,vv,r):
        for k in range(len(w)):
            if k not in (r,r+1) and u[k]!=vv[k]: return zero
        c1,c2=w[r],w[r+1]; s1,s2=u[r],u[r+1]; t1,t2=vv[r],vv[r+1]
        w2=list(w); w2[r],w2[r+1]=c2,c1
        if c1!=c2:
            pp=par[c1]*par[c2]
            tv1=var(w2,vv,r); tv2=var(w2,vv,r+1)
            if (s1,s2)==(t1,t2) and s1==s2:  # PP or RR
                if c1<c2: return tau(pp)
                return comp(tau(pp),L(poly(Qword(c2,tv1,c1,tv2))))
            if (s1,s2,t1,t2)==('P','R','R','P'): return tau(pp)
            if (s1,s2,t1,t2)==('R','P','P','R'):
                return comp(tau(pp),L(poly(Qword(c2,tv1,c1,tv2))))
            return zero
        c=c1; p=par[c]
        if s1==s2:
            if (t1,t2)!=(s1,s2): return zero
            return demazure(var(w,u,r),var(w,u,r+1),p)
        # mixed same colour: probe var and reservoir var
        xv=var(w,u,r) if s1=='P' else var(w,u,r+1)
        yv=var(w,u,r) if s1=='R' else var(w,u,r+1)
        D=(xv,yv,p)
        if p==0: a={(D,):one}
        else: a={(D,):R.add(R.var(xv),R.var(yv),-1)}
        if E['flip']: a={d:{m:-c for m,c in g.items()} for d,g in a.items()}
        La=L(a)
        if (s1,s2,t1,t2)==('R','P','R','P'): return La
        if (s1,s2,t1,t2)==('P','R','R','P'): return tau(p)
        if (s1,s2,t1,t2)==('R','P','P','R'): return sc(comp(La,La,tau(p)),-1)
        if (s1,s2,t1,t2)==('P','R','P','R'): return sc(comp(tau(p),La,tau(p)),-1)
        return zero
    def paths(w):
        out=[]
        for sides in itertools.product('PR',repeat=len(w)):
            if sorted(c for c,sd in zip(w,sides) if sd=='P')==sorted(probe) and \
               sorted(c for c,sd in zip(w,sides) if sd=='R')==sorted(res): out.append(sides)
        return out
    i,j,k=word
    w0=(i,j,k); wl1=(j,i,k); wl2=(j,k,i); wr1=(i,k,j); wr2=(k,i,j); wf=(k,j,i)
    tests=[]
    vs=[n for n in R.names
        if any(n.startswith(c+sd) for c in set(word) for sd in 'PR') and int(n[2])<3]
    import itertools as it
    for deg in range(0,3):
        for combo in it.combinations_with_replacement(vs,deg):
            m=[0]*R.n
            for v in combo: m[R.names.index(v)]+=1
            tests.append({():{tuple(m):Fr(1)}})
    allok=True; bad=[]
    for p in paths(w0):
        for q in paths(wf):
            Lt=zero
            for m1 in paths(wl1):
                for m2 in paths(wl2):
                    Lt=plus(Lt,comp(entry(w0,p,m1,0),entry(wl1,m1,m2,1),entry(wl2,m2,q,0)))
            Rt=zero
            for m1 in paths(wr1):
                for m2 in paths(wr2):
                    Rt=plus(Rt,comp(entry(w0,p,m1,1),entry(wr1,m1,m2,0),entry(wr2,m2,q,1)))
            diff=plus(Lt,Rt,-1)
            if i==k and i!=j and p==q:
                d=dn[(i,j)]
                def D_(pos): return L(poly(R.var(var(w0,p,pos))))
                def pw(op,e): return comp(*([op]*e)) if e else (lambda f:f)
                corr=zero
                for a_ in range(d):
                    sg=(-1)**((par[i]*(par[j]+a_))%2)
                    corr=plus(corr,sc(comp(pw(D_(2),a_),pw(D_(0),d-1-a_)),sg*t[(i,j)]))
                for b in range(1,d):
                    for c in range(1,dn[(j,i)]):
                        for a_ in range(b):
                            cc=s.get((i,j,b,c),0)
                            if cc:
                                sg=(-1)**((par[i]*(par[j]+a_))%2)
                                term=comp(pw(D_(2),a_),pw(D_(1),c),pw(D_(0),b-1-a_))
                                corr=plus(corr,sc(term,sg*cc))
                diff=plus(diff,corr,-1)
            ok=all(not ecanon(diff(f)) for f in tests)
            if not ok: allok=False; bad.append((p,q))
    return allok,bad

def sweep(flip=False):
    results=[]
    for word in WORDS:
        letters=word
        for pi,pj,pk in itertools.product((0,1),repeat=3):
            par={'i':pi,'j':pj,'k':pk}
            for dij,dji in [(1,1),(2,2),(2,1),(1,2),(3,2),(2,4)]:
                if pi and dij%2: continue
                if pj and dji%2: continue
                dm={}
                for a in COLS:
                    for b in COLS:
                        dm[(a,b)]=0
                dm[('i','j')]=dij; dm[('j','i')]=dji
                dm[('i','k')]=2 if pi else 1; dm[('k','i')]=2 if pk else 1
                dm[('j','k')]=0; dm[('k','j')]=0
                if 'k' not in word and pk: continue
                E=build(par,dm,seed=dij*7+dji,flip_a=flip)
                n=len(word)
                for sides in itertools.product('PR',repeat=n):
                    probe=tuple(sorted(c for c,sd in zip(word,sides) if sd=='P'))
                    res_=tuple(sorted(c for c,sd in zip(word,sides) if sd=='R'))
                    key=(word,pi,pj,pk,dij,dji,probe,res_)
                    if key in [r[0] for r in results]: continue
                    ok,bad=run(E,word,probe,res_)
                    results.append((key,ok,bad))
                    if not ok: print('FAIL',key,bad,flush=True)
    print('total',len(results),'fails',sum(1 for r in results if not r[1]))

WORDS=[tuple(w) for w in (sys.argv[1] if len(sys.argv)>1 else 'iii').split(',')]
if __name__=='__main__':
    sweep(flip=len(sys.argv)>2)
