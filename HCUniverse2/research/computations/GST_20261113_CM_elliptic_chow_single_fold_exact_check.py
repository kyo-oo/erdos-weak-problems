"""Exact SymPy test of a genuine CM elliptic original-X Chow single-fold construction.
Mathematical geometry (intersection, pushforward, Hodge weights) is proved
separately in the companion research/derivations .tex file; this test only
checks exact symbolic and rational matrix identities.
"""
import sympy as sp
x, lam, u = sp.symbols('x lam u')
cubic = x*(x-1)*(x-lam)
assert sp.factor(sp.discriminant(cubic,x)) == lam**2*(lam-1)**2
j2 = sp.Rational(256)*(1-2+4)**3/(2**2*(1-2)**2)
assert j2 == 1728
assert sp.expand((-u)**3-(-u)+(u**3-u)) == 0
J = sp.Matrix([[0,-1],[1,0]])
assert J*J == -sp.eye(2)
print('PASS Legendre discriminant, CM j(2)=1728, geometric J^2=-I')

G=sp.Matrix([[0,1,1,1], [1,0,1,1], [1,1,0,2], [1,1,2,0]])
assert G.det()==-4
F1,F2,Delta,Gamma_i=[sp.eye(4)[:,k] for k in range(4)]
S=Delta-F1-F2
R=Gamma_i-F1-F2
pair=lambda a,b:(a.T*G*b)[0]
assert pair(S,S)==-2 and pair(R,R)==-2 and pair(S,R)==0
assert pair(S,F1)==pair(S,F2)==pair(R,F1)==pair(R,F2)==0
print('PASS 4 independent actual divisor classes; CM primitive S,R have norm -2')

T=sp.Matrix([[4,0,0,0], [0,9,0,0], [0,0,0,-6], [0,0,6,0]])
seed=sp.Matrix([1,1,1,0])
orbit=[seed]
for _ in range(6): orbit.append(T*orbit[-1])
K=sp.Matrix.hstack(*orbit[:4])
assert K==sp.Matrix([[1,4,16,64], [1,9,81,729], [1,0,-36,0], [0,6,0,-216]])
assert K.det()==182520
assert sp.factor(T.charpoly(x).as_expr())==(x-4)*(x-9)*(x**2+36)
print('PASS actual finite pushforward f_* and single diagonal seed: det Krylov=182520')

HodgeGram=sp.Matrix([[0,1,0,0], [1,0,0,0], [0,0,-2,0], [0,0,0,-2]])
W=sp.Matrix([sp.Rational(1,585),-sp.Rational(1,260),-sp.Rational(1,936),0])
ell=(HodgeGram*W).T
assert ell==sp.Matrix([[-sp.Rational(1,260),sp.Rational(1,585),sp.Rational(1,468),0]])
assert ell*K==sp.Matrix([[0,0,0,1]])
H=sp.Matrix(4,4,lambda i,j:(ell*orbit[i+j])[0])
assert H==sp.Matrix([[0,0,0,1], [0,0,1,13], [0,1,13,97], [1,13,97,793]])
assert H.det()==1
print('PASS genuine algebraic rational detector: det Hankel=1')
print('SCOPE: exact rational arithmetic; original-X universal GST/Hodge source not claimed')
