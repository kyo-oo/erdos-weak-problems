#!/usr/bin/env python3
"""Exact GST three-free 30-trit coefficient and scale certificate.

A FINITE certificate, not an unconditional proof of Erdős. The infinite
scale extension uses formally proved coefficient-stabilization and tower-read.
Invocation: coefficient OR low --start S --stop T, half-open S..T.
"""
import argparse
from time import monotonic
D=30
MAX=1171317
Q=3**D
C29=28881270545965
N=MAX-MAX//3

def first_two(x):
    p=0
    while x:
        x,d=divmod(x,3)
        if d==2: return p
        p+=1
    return None

def coefficient():
    c=1
    for s in range(D-1):
        c=(c+3**(s+1)*c*c+3**(2*s+1)*c*c*c)%Q
    assert c==C29
    hits=0
    for u in range(1,MAX+2):
        if u%3==0: continue
        p=first_two((u*c)%Q)
        if u==MAX+1: assert p is None
        else:
            assert p is not None,u
            hits+=1
    assert hits==780878==N
    print('C29',c,'CHECKED',hits,'FIRST_3FREE_30TRIT_SURVIVOR',MAX+1)
    print('THREEFREE_COEFFICIENT_PASS=1')

def low(start,stop):
    assert 0<=start<stop<=29
    cases=0
    maxoffset=-1
    argmax=None
    for s in range(start,stop):
        modulus=3**(s+85)
        step=pow(4,3**s,modulus)
        x=1
        for u in range(1,MAX+1):
            x=(x*step)%modulus
            if u%3==0 or u*3**s in (1,4):continue
            cases+=1
            p=first_two(x)
            assert p is not None and p<=s+42,(s,u,p)
            if p-s-1>maxoffset:
                maxoffset=p-s-1
                argmax=(s,u,p)
        print('COMPLETED_SCALE',s,flush=True)
    expected=(stop-start)*N-(2 if start==0 else 0)
    assert cases==expected,(cases,expected)
    print('LOW_SCALES',start,stop,'CASES',cases)
    print('MAX_RELATIVE_OFFSET',maxoffset,argmax)
    print('THREEFREE_LOW_PASS=1')

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('phase',choices=['coefficient','low'])
    ap.add_argument('--start',type=int)
    ap.add_argument('--stop',type=int)
    a=ap.parse_args()
    t=monotonic()
    if a.phase=='coefficient':coefficient()
    else:low(a.start,a.stop)
    print('SECONDS',round(monotonic()-t,2))
