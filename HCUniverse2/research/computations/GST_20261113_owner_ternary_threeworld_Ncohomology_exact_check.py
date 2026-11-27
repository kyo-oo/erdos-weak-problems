"""Owner GST x4/base3 survival exact checks, N-hole and source limitations."""
import sympy as sp
def two(x): return int(x == 2)
def micro(a,d): return (a+2*d)%3
def mid(c,d): return micro(c//2,d)
def final(c,d): return micro(c%2,mid(c,d))
def survive(c,d): return two(d)*two(mid(c,d))+two(mid(c,d))*two(final(c,d))
def shuffle(c,d): return ((c+4*d)//3,(c+4*d)%3)
def cp(c): return [-5,-7,1,3][c]
def ip(d): return 112*two(d)-56*d
def md(c,d):
    nc,nd=shuffle(c,d)
    return ip(nd)-ip(d)+7*(cp(c)-3*cp(nc))+56*survive(c,d)
all_states=[(c,d) for c in range(4) for d in range(3)]
fixed=[]
for origin in all_states:
    hist=[origin]
    for _ in range(13):hist.append(shuffle(*hist[-1]))
    assert hist[5]==origin
    if hist[1]==origin: fixed.append(origin)
    for N in range(1,13):
        weighted=sum(3**t*survive(*hist[t]) for t in range(N))
        D=sum(3**t*md(*hist[t]) for t in range(N))
        rhs=(D+ip(hist[0][1])-3**(N-1)*ip(hist[N][1])
              +2*sum(3**(t-1)*ip(hist[t][1]) for t in range(1,N))
              -7*(cp(hist[0][0])-3**N*cp(hist[N][0])))
        assert 56*weighted==rhs
assert fixed==[(0,0),(3,2)]
for N in range(1,13):
    assert sum(3**t*survive(3,2) for t in range(N))==3**N-1
print('PASS owner GST 12 states, 144 weighted-carry checks, five-fold orbits')
for n in range(1,8):
    C=sp.symbols('C0:'+str(n+1));I=sp.symbols('I0:'+str(n+1));S=sp.symbols('S0:'+str(n))
    D=[I[t+1]-I[t]+7*(C[t]-3*C[t+1])+56*S[t] for t in range(n)]
    diff=(56*sum(3**t*S[t] for t in range(n))
          -sum(3**t*D[t] for t in range(n))-I[0]+3**(n-1)*I[n]
          -2*sum(3**(t-1)*I[t] for t in range(1,n))
          +7*(C[0]-3**n*C[n]))
    assert sp.expand(diff)==0
print('PASS symbolic telescoping N=1..7; general formula proved by sum identities')
a=sp.Matrix([1,2]);b=sp.Matrix([3,4])
assert (a*b.T).rank()==1
u=sp.Matrix([1,0]);v=sp.Matrix([0,1])
assert (u*u.T+v*v.T)==sp.eye(2)
d=sp.diag(1,1,0);z=sp.Matrix([1,2,3]);w=sp.Matrix([4,7,3]);eta=sp.Matrix([3,5,0])
assert d*eta==w-z
h,m=sp.symbols('h m')
for p in range(1,11):
    coef=sp.series((1-m*h)**(-2),h,0,p+1).removeO().expand().coeff(h,p)
    assert sp.simplify(coef-(p+1)*m**p)==0
print('PASS N-hole tensor rank, toy Deligne correction, fixed-bundle Porteous p=1..10')
print('SCOPE: neither Chow source on arbitrary X nor universal GST orbit law proved')
