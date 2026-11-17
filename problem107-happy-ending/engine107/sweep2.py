#!/usr/bin/env python3
import sys, itertools, json
from fractions import Fraction as F
import importlib.util
spec = importlib.util.spec_from_file_location('mb', 'doubter/mirror_battery.py')
mb = importlib.util.module_from_spec(spec); sys.modules['mb']=mb; spec.loader.exec_module(mb)
def cross(o,a,b): return (a[0]-o[0])*(b[1]-o[1])-(a[1]-o[1])*(b[0]-o[1])
def intri(p,u,v,w):
    c1,c2,c3 = cross(u,v,p),cross(v,w,p),cross(w,u,p)
    return (c1>0 and c2>0 and c3>0) or (c1<0 and c2<0 and c3<0)
def verify(pts,n):
    N=len(pts)
    for i,j,k in itertools.combinations(range(N),3):
        if cross(pts[i],pts[j],pts[k])==0: return False
    for sub in itertools.combinations(range(N),n):
        S=[pts[i] for i in sub]; found=False
        for i in range(n):
            others=[S[j] for j in range(n) if j!=i]
            for tri in itertools.combinations(others,3):
                if intri(S[i],*tri): found=True;break
            if found:break
        if not found: return False
    return True
best=None; any_ok=0
for eps_e in (7,8,9):
  for wn,wd in ((2,5),(31,80),(39,100),(79,200)):
    for a,b,g,c in ((F(1,3),F(1,2),F(2,3),3),(F(1,3),F(1,2),F(2,3),2),(F(2,7),F(3,7),F(5,7),3),(F(1,3),F(1,2),F(2,3),4)):
      try:
        params=dict(w=F(wn,wd),eps=F(1,2**eps_e),alpha=a,beta=b,gamma=g,c=c)
        pts6,_,_=mb.build_ersz61(6,**params)
        if not verify(pts6,6):
            print(f'eps=2^-{eps_e} w={wn}/{wd} a={a} c={c}: FAILS n=6'); continue
        pts5,_,_=mb.build_ersz61(5,**params)
        if not verify(pts5,5):
            print(f'eps=2^-{eps_e} w={wn}/{wd} a={a} c={c}: FAILS n=5'); continue
        any_ok+=1
        mx6=max(max(abs(p[0]),abs(p[1])) for p in pts6)
        mx5=max(max(abs(p[0]),abs(p[1])) for p in pts5)
        print(f'eps=2^-{eps_e} w={wn}/{wd} a={a} c={c}: mx5={mx5:.3e} mx6={mx6:.3e}')
        if best is None or mx6<best[0]: best=(mx6,mx5,params,pts5,pts6)
      except Exception as e:
        print(f'eps=2^-{eps_e} w={wn}/{wd} a={a} c={c}: EXC {e}')
print('working configs:', any_ok)
if best:
    print('BEST mx6=%.3e mx5=%.3e'%(best[0],best[1]), best[2])
    json.dump({'params':{k:(f'{v.numerator}/{v.denominator}' if isinstance(v,F) else v) for k,v in best[2].items()},'pts5':best[3],'pts6':best[4]},open('witness_best.json','w'))
    print('saved witness_best.json')
