from fractions import Fraction as F
import itertools, json

# Exact basis: 1,h,h^2,h^3,h^4,s,r. No floating arithmetic.
n=7
deg=(0,1,2,3,4,2,2)
sgn=(1,1,1,1,1,1,-1)
def zero(): return [F(0) for _ in range(n)]
def basis(i):
    v=zero(); v[i]=F(1); return v
e=[basis(i) for i in range(n)]
def add(u,v): return [x+y for x,y in zip(u,v)]
def scale(a,u): return [a*x for x in u]
def bm(i,j):
    if i==0: return e[j]
    if j==0: return e[i]
    if i<5 and j<5:
        return e[i+j] if i+j<=4 else zero()
    if i==j==5: return scale(F(3),e[4])
    if i==j==6: return scale(F(5),e[4])
    return zero()
def mul(u,v):
    z=zero()
    for i,x in enumerate(u):
        for j,y in enumerate(v):
            if x and y: z=add(z,scale(x*y,bm(i,j)))
    return z
def invol(u): return [F(s)*x for s,x in zip(sgn,u)]
def tr(u): return u[4]
def pair(u,v): return tr(mul(u,v))
def mm(a,b):
    return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]
def mv(a,v): return [sum(x*y for x,y in zip(row,v)) for row in a]
def transpose(a): return list(map(list,zip(*a)))
def rref(a):
    a=[list(map(F,row)) for row in a]; piv=[]; rr=0
    for c in range(len(a[0])):
        k=next((i for i in range(rr,len(a)) if a[i][c]),None)
        if k is None: continue
        a[rr],a[k]=a[k],a[rr]
        fac=a[rr][c]; a[rr]=[x/fac for x in a[rr]]
        for i in range(len(a)):
            if i!=rr and a[i][c]:
                fac=a[i][c]; a[i]=[x-fac*y for x,y in zip(a[i],a[rr])]
        piv.append(c); rr+=1
        if rr==len(a): break
    return a,piv
def rank(a): return len(rref(a)[1])
def det(a):
    a=[list(map(F,row)) for row in a]; d=F(1)
    for c in range(len(a)):
        k=next((i for i in range(c,len(a)) if a[i][c]),None)
        if k is None: return F(0)
        if k!=c: a[c],a[k]=a[k],a[c]; d=-d
        fac=a[c][c]; d*=fac
        for i in range(c+1,len(a)):
            q=a[i][c]/fac
            for j in range(c+1,len(a)): a[i][j]-=q*a[c][j]
    return d
def ident(m): return [[F(i==j) for j in range(m)] for i in range(m)]
b=[[pair(u,v) for v in e] for u in e]
delta=[[F(0) for _ in range(n)] for _ in range(n)]
for i in range(5): delta[i][4-i]=F(1)
delta[5][5]=F(1,3); delta[6][6]=F(1,5)
k=[[F(0) for _ in range(n)] for _ in range(n)]; k[6][6]=F(1,5)
# For tensor coefficients C_ij e_i (x) e_j, T_C(v)=C^t B v.
def action(c): return mm(transpose(c),b)
assoc=0
for i,j,l in itertools.product(range(n),repeat=3):
    assert mul(mul(e[i],e[j]),e[l])==mul(e[i],mul(e[j],e[l]))
    assoc+=1
for i,j in itertools.product(range(n),repeat=2):
    assert bm(i,j)==bm(j,i)
    assert invol(bm(i,j))==mul(invol(e[i]),invol(e[j]))
    if bm(i,j)!=zero():
        assert all(deg[t]==deg[i]+deg[j] for t,x in enumerate(bm(i,j)) if x)
for i in range(n): assert mul(e[0],e[i])==e[i]
assert mm(delta,b)==ident(n)
assert det(b)==15
assert action(delta)==ident(n)
tk=action(k)
assert mm(tk,tk)==tk
assert mv(tk,e[6])==e[6]
assert all(mv(tk,e[i])==zero() for i in range(6))
assert sum(tk[i][i] for i in range(n))==1
assert all(sgn[i]*sgn[j]==1 for i in range(n) for j in range(n) if delta[i][j] or k[i][j])
# Primitive middle ker(h: H^4 -> H^6); order h^2,s,r.
primitive_l=[[mul(e[1],e[j])[3] for j in (2,5,6)]]
assert primitive_l==[[F(1),F(0),F(0)]]
assert rank(primitive_l)==1
assert [[pair(e[i],e[j]) for j in (5,6)] for i in (5,6)]==[[3,0],[0,5]]
hl=[]
for codim in (0,1,2):
    src=[i for i in range(n) if deg[i]==codim]
    dst=[i for i in range(n) if deg[i]==4-codim]
    power=4-2*codim
    cols=[]
    for i in src:
        v=e[i]
        for _ in range(power): v=mul(e[1],v)
        cols.append(v)
    mat=[[col[i] for col in cols] for i in dst]
    assert rank(mat)==len(src)==len(dst)
    hl.append({"codimension":codim,"power":power,"rank":rank(mat)})
native_dim=sum(s==1 for s in sgn)
tensor_native_dim=sum(s*t==1 for s in sgn for t in sgn)
assert (native_dim,tensor_native_dim)==(6,37)
# Euler-normalized residual: chi=B, kernel=-K, product pairing=B tensor B.
# On this diagonal tensor only:
doubled=-k[6][6]*pair(e[6],e[6])**2
assert doubled==-5
assert all(pair(e[6],e[i])==0 for i in range(6))
# Degree-e pullback/trace model. Finite tests supplement the uniform written proof.
for degree in (1,2,3,7):
    native_outputs=[scale(F(degree),e[i]) for i in range(6)]
    assert all(pair(e[6],v)==0 for v in native_outputs)
    assert F(degree)*pair(e[6],e[6])==5*degree
# Curve check: bilinearity reduces to these symbolic coefficient identities.
# Work in Q[g] as coefficient lists.
def padd(x,y):
    z=[F(0)]*max(len(x),len(y))
    for i,a in enumerate(x): z[i]+=a
    for i,a in enumerate(y): z[i]+=a
    return z
curve_const=[[0,1,1],[1,0,1],[1,1,2]]
curve_g=[[0,0,0],[0,0,0],[0,0,-2]]
dv=(-1,-1,1)
def curve_pair(u,v):
    return [F(sum(u[i]*m[i][j]*v[j] for i in range(3) for j in range(3)))
            for m in (curve_const,curve_g)]
assert curve_pair(dv,(1,0,0))==[0,0]
assert curve_pair(dv,(0,1,0))==[0,0]
assert curve_pair(dv,dv)==[0,-2]
assert curve_pair(dv,(0,0,1))==[0,-2]
out={
 "status":"all exact assertions passed",
 "basis":["1","h","h^2","h^3","h^4","s","r"],
 "field":"Q; curve calculation also Q[g]",
 "associativity_basis_triples":assoc,
 "automorphism_basis_pairs":49,
 "frobenius_pairing_determinant":str(det(b)),
 "hard_lefschetz":hl,
 "primitive_middle_dimension":2,
 "primitive_middle_gram":[[3,0],[0,5]],
 "one_factor_admissible_dimension":native_dim,
 "two_factor_admissible_dimension":tensor_native_dim,
 "external_product_admissible_dimension":native_dim**2,
 "residual_projector_trace":1,
 "residual_projector_idempotent":True,
 "residual_source_periods":[0]*native_dim,
 "signed_doubled_euler_index":str(doubled),
 "positive_negative_doubled_index":str(-doubled),
 "alteration_degrees_checked":[1,2,3,7],
 "curve_D_squared_coefficients_in_1_g":[0,-2],
 "non_claims":["No actual variety or canonical Chow comparison is modeled.",
               "No counterexample to the Hodge conjecture.",
               "No claim that all geometric GST source hypotheses hold in this model.",
               "No universal algebraic-source existence theorem or Lean compilation."]
}
print(json.dumps(out,indent=2))

