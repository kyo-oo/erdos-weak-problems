#!/usr/bin/env python3
"""Exact graded DGA audit. Run: python research/experiments/gst_all_degree_curvature_checks.py"""
from fractions import Fraction as F
from itertools import product
import json

ASSERTIONS=0
def check(x):
    global ASSERTIONS
    ASSERTIONS+=1
    assert x,ASSERTIONS

def rank(rows,ncols=None):
    a=[[F(x) for x in r] for r in rows]
    if not a:return 0
    n=len(a[0]) if ncols is None else ncols;r=0
    for j in range(n):
        k=next((i for i in range(r,len(a)) if a[i][j]),None)
        if k is None:continue
        a[r],a[k]=a[k],a[r];q=a[r][j];a[r]=[x/q for x in a[r]]
        for i in range(len(a)):
            if i!=r and a[i][j]:
                q=a[i][j];a[i]=[x-q*y for x,y in zip(a[i],a[r])]
        r+=1
        if r==len(a):break
    return r

def nullspace(rows,n):
    a=[[F(x) for x in r] for r in rows];piv=[];r=0
    for j in range(n):
        k=next((i for i in range(r,len(a)) if a[i][j]),None)
        if k is None:continue
        a[r],a[k]=a[k],a[r];q=a[r][j];a[r]=[x/q for x in a[r]]
        for i in range(len(a)):
            if i!=r and a[i][j]:
                q=a[i][j];a[i]=[x-q*y for x,y in zip(a[i],a[r])]
        piv.append(j);r+=1
        if r==len(a):break
    out=[]
    for j in range(n):
        if j not in piv:
            v=[F(0)]*n;v[j]=1
            for i,k in enumerate(piv):v[k]=-a[i][j]
            out.append(v)
    return out

def fixtures():
    # name, truncated-even exponents, odd generators, p, actual alpha monomials
    return [
      ('P1-flat',[1],0,1,[([0],0,0)]),
      ('P1-point',[1],0,1,[([1],0,1)]),
      ('P2-h',[2],0,1,[([1],0,1)]),
      ('P2-point',[2],0,2,[([2],0,1)]),
      ('P2xP2-square',[2,2],0,2,[([2,0],0,1)]),
      ('P2xP2-mixed',[2,2],0,2,[([1,1],0,1)]),
      ('P2xP2-rational',[2,2],0,2,[([2,0],0,F(1,2)),([1,1],0,F(-2,3))]),
      ('E-flat',[],2,1,[([],0,0)]),
      ('E-point',[],2,1,[([],3,1)]),
      ('P1xE-mixed',[1],2,1,[([1],0,1),([0],3,1)]),
      ('P1xE-top',[1],2,2,[([1],3,1)]),
      ('ExE-symplectic',[],4,1,[([],3,1),([],12,1)]),
      ('ExE-top',[],4,2,[([],15,1)]),
    ]

def run():
    tables=[]
    for name,caps,nodd,p,terms in fixtures():
        base=[(tuple(e),mask) for e in product(*(range(c+1) for c in caps)) for mask in range(1<<nodd)]
        bi={a:i for i,a in enumerate(base)};aN=len(base);s=2*p-1;d=2*sum(caps)+nodd;D=d+2*s
        alpha={bi[(tuple(e),m)]:F(c) for e,m,c in terms if c}
        def base_deg(a):return 2*sum(a[0])+a[1].bit_count()
        def base_mul(a,b):
            e=tuple(x+y for x,y in zip(a[0],b[0]));m,n=a[1],b[1]
            if any(x>c for x,c in zip(e,caps)) or m&n:return None,0
            inv=sum((n&((1<<i)-1)).bit_count() for i in range(nodd) if m>>i&1)
            return bi[(e,m|n)],(-1)**inv
        words=[(i,u,v) for i in range(aN) for u in (0,1) for v in (0,1)]
        wi={w:i for i,w in enumerate(words)};N=len(words)
        deg=[base_deg(base[i])+s*(u+v) for i,u,v in words]
        bydeg=[[i for i,k in enumerate(deg) if k==q] for q in range(D+2)]
        def mul(i,j):
            a,u,v=words[i];b,U,V=words[j]
            if u+U>1 or v+V>1:return None,0
            c,sgn=base_mul(base[a],base[b])
            if not sgn:return None,0
            return wi[(c,u+U,v+V)],sgn*(-1)**((u+v)*base_deg(base[b])+v*U)
        differential=[{} for _ in words]
        for j,(a,u,v) in enumerate(words):
            if u:
                for b,c in alpha.items():
                    k,sgn=base_mul(base[a],base[b])
                    if sgn:differential[j][wi[(k,0,v)]]=c*sgn*(-1)**base_deg(base[a])
        def vector_add(*vs):
            out={}
            for c,v in vs:
                for i,a in v.items():out[i]=out.get(i,F(0))+c*a
            return {i:a for i,a in out.items() if a}
        for j in range(N):
            check(all(deg[i]==deg[j]+1 for i in differential[j]))
            check(not vector_add(*[(c,differential[i]) for i,c in differential[j].items()]))
        # The entire multiplication table checks the odd-base and uv signs.
        for i,j in product(range(N),repeat=2):
            k,c=mul(i,j);lhs={} if k is None else {r:c*v for r,v in differential[k].items()}
            rhs={}
            for a,v in differential[i].items():
                b,e=mul(a,j)
                if e:rhs[b]=rhs.get(b,F(0))+v*e
            for a,v in differential[j].items():
                b,e=mul(i,a)
                if e:rhs[b]=rhs.get(b,F(0))+(-1)**deg[i]*v*e
            check(lhs=={k:v for k,v in rhs.items() if v})
        mats=[];ranks=[];cohom=[]
        for k in range(D+1):
            cols=bydeg[k];rows=bydeg[k+1]
            mat=[[differential[j].get(i,F(0)) for j in cols] for i in rows]
            mats.append(mat);ranks.append(rank(mat));cycles=nullspace(mat,len(cols))
            boundaries=[]
            if k:
                prev=bydeg[k-1]
                boundaries=[[differential[j].get(i,F(0)) for i in cols] for j in prev]
            span=boundaries[:];r=rank(span);reps=[]
            for c in cycles:
                r2=rank(span+[c])
                if r2>r:span.append(c);r=r2;reps.append(c)
            cohom.append(reps)
        ad=[sum(base_deg(x)==j for x in base) for j in range(d+1)]
        lr=[]
        for j in range(d+1):
            src=[i for i,a in enumerate(base) if base_deg(a)==j]
            dst=[i for i,a in enumerate(base) if base_deg(a)==j+2*p]
            L={}
            for i in src:
                for a,c in alpha.items():
                    b,e=base_mul(base[i],base[a])
                    if e:L[b,i]=L.get((b,i),F(0))+c*e
            lr.append(rank([[L.get((i,j),F(0)) for j in src] for i in dst]))
        get=lambda row,k:row[k] if 0<=k<len(row) else 0
        betti=[];grams=[];loss=[]
        top=wi[(bi[(tuple(caps),(1<<nodd)-1)],1,1)]
        for k,reps in enumerate(cohom):
            b=len(bydeg[k])-ranks[k]-(ranks[k-1] if k else 0)
            predicted=(get(ad,k)+2*get(ad,k-s)+get(ad,k-2*s)-get(lr,k-2*p)-get(lr,k-s)-get(lr,k-s-2*p)-get(lr,k-2*s))
            check(b==predicted==len(reps));betti.append(b)
            flat=get(ad,k)+2*get(ad,k-s)+get(ad,k-2*s)
            check(flat-b==sum(get(lr,k-s-e-f) for e in (0,1) for f in (0,s)))
            loss.append(flat-b)
            gram=[]
            for x in reps:
                row=[]
                for y in cohom[D-k]:
                    val=F(0)
                    for i,a in zip(bydeg[k],x):
                        for j,bj in zip(bydeg[D-k],y):
                            z,e=mul(i,j)
                            if z==top:val+=a*bj*e
                    row.append(val)
                gram.append(row)
            gr=rank(gram);check(gr==b==len(cohom[D-k]));grams.append(gr)
        check(sum(betti)==4*(aN-sum(lr)))
        check(sum(loss)==4*sum(lr))
        check(all(get(lr,j)==get(lr,d-2*p-j) for j in range(d+1)))
        check(betti==betti[::-1])
        if alpha:
            check(all(not x for x in loss[:s]) and loss[s]==1)
        else:check(not any(loss))
        # Actual first-jet block matrix, independently of the dimension formula.
        fullD=[[differential[j].get(i,F(0)) for j in range(N)] for i in range(N)]
        jet=[[F(0)]*(2*N) for _ in range(2*N)]
        for i in range(N):
            for j in range(N):jet[N+i][j]=fullD[i][j]
        check(rank(fullD)==rank(jet)==2*sum(lr))
        unit=bi[(tuple(0 for _ in caps),0)]
        handle=wi[(unit,1,0)]
        check(differential[handle]=={wi[(a,0,0)]:c for a,c in alpha.items()})
        # A z*L block has two special classes, one torsion class, one Tor class.
        generic=sum(betti);torsion=2*sum(lr);tensor_special=generic+torsion;tor_special=torsion
        check(tensor_special+tor_special==4*aN)
        tables.append({'name':name,'p':p,'formal_dimension':D,'base_betti':ad,'cup_ranks':lr,
          'betti':betti,'pairing_ranks':grams,'total_betti':sum(betti),'torsion_count':torsion,
          'tensor_special':tensor_special,'tor_special':tor_special})
    return {'all_passed':True,'assertions':ASSERTIONS,'tables':tables,
      'scope':'13 fixed exact graded DGA fixtures, complete basis multiplication/Leibniz tables, degree-by-degree cohomology and trace ranks. No finite computation proves the general geometric comparison or constructs a Chow class.'}

if __name__=='__main__':print(json.dumps(run(),sort_keys=True))
