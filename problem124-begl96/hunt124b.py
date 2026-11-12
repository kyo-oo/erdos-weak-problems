import time
from fractions import Fraction
exec(open('hunt124.py').read().split('t0=time.time()')[0])

# 1) table with triples up to 200
tab=[]
for n in gen_S(200):
    if n==1: tab.append((1,0,0,0)); continue
    for a in range(7):
        for b in range(5):
            for c in range(4):
                if 3**a*4**b*7**c==n: tab.append((n,a,b,c))
print("TABLE:", tab)

# 2) which 1/n (n=2..40) split over distinct S347 (bound 400)
t0=time.time()
S=[x for x in gen_S(400) if x>1]
for n in range(2,41):
    if n in [3,4,7,9,12,16,21,27,28,36]: pass
    r,_=subset_search(S, Fraction(1,n), t0+20)
    if isinstance(r,list):
        assert sum(Fraction(1,x) for x in r)==Fraction(1,n)
        print(f"1/{n} SPLITS:", r, flush=True)
    else:
        print(f"1/{n}: NO/timeout", flush=True)

# 3) verify the three task-listed identities
print("1/3+1/4==7/12:", Fraction(1,3)+Fraction(1,4)==Fraction(7,12))
print("1/7+1/9==16/63:", Fraction(1,7)+Fraction(1,9)==Fraction(16,63))
print("1/12+1/16+1/21+1/28==11/48:", Fraction(1,12)+Fraction(1,16)+Fraction(1,21)+Fraction(1,28)==Fraction(11,48))
