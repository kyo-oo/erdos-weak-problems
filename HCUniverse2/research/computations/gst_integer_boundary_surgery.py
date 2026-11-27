#!/usr/bin/env python3
"""GST integer-boundary surgery: exact mass minimization in a finite chain complex.

Input: integral lower boundary A, upper boundary B, and optional homology
signature H, with A B=0 and H B=0; closed integer initial cycle z0.
All admissible replacements are exactly z0+im_Z(B); HNF checks the INTEGER
lattice, not merely rational span. Mass is sum_i w_i*abs(z_i); calibration
period is sum_i p_i*z_i with |p_i|<=w_i and p B=0.

Exhaustively enumerate all chains of mass <= starting mass, so the returned
minimizer is globally optimal within this fixed finite geometric chain
complex. No claim of all-variety Hodge algebraicity or mesh convergence.
"""
from fractions import Fraction
from itertools import product
from math import floor
from sympy import Matrix
from sympy.matrices.normalforms import hermite_normal_form


def optimize(z0, lower, upper, signature, weights, pairing, cap=200000):
    z0=tuple(map(int,z0))
    A,B,H=Matrix(lower),Matrix(upper),Matrix(signature)
    m=len(z0)
    if A.cols!=m or B.rows!=m or H.cols!=m:
        raise ValueError("chain dimension mismatch")
    if A*B!=Matrix.zeros(A.rows,B.cols) or H*B!=Matrix.zeros(H.rows,B.cols):
        raise ValueError("boundary identity or homology invariant fails")
    if A*Matrix(z0)!=Matrix.zeros(A.rows,1):
        raise ValueError("initial integral current is not closed")
    w,p=tuple(map(Fraction,weights)),tuple(map(Fraction,pairing))
    if len(w)!=m or len(p)!=m or any(x<=0 or x<abs(y) for x,y in zip(w,p)):
        raise ValueError("invalid geometric mass or calibration")
    if Matrix([p])*B!=Matrix.zeros(1,B.cols):
        raise ValueError("calibration period is not boundary invariant")
    mass=lambda z:sum((x*abs(y) for x,y in zip(w,z)),Fraction(0))
    period=lambda z:sum((x*y for x,y in zip(p,z)),Fraction(0))
    start=mass(z0)
    limits=[floor(start/x) for x in w]
    size=1
    for n in limits: size*=2*n+1
    if size>cap:
        raise ValueError(f"exhaustive search size {size} exceeds cap {cap}")
    lattice=hermite_normal_form(B) if B.cols else Matrix.zeros(m,0)
    best=z0
    comparable=0
    for z in product(*(range(-n,n+1) for n in limits)):
        if mass(z)>start or A*Matrix(z)!=Matrix.zeros(A.rows,1):
            continue
        if H*Matrix(z)!=H*Matrix(z0):
            continue
        v=Matrix(z)-Matrix(z0)
        if lattice.cols:
            if hermite_normal_form(B.row_join(v))!=lattice:
                continue
        elif any(v):
            continue
        comparable+=1
        if (mass(z),z)<(mass(best),best):
            best=z
    return dict(initial=z0,optimum=best,initial_mass=start,optimal_mass=mass(best),
                initial_defect=start-period(z0),optimal_defect=mass(best)-period(best),
                exhaustive_candidates=size,homologous_candidates=comparable)


if __name__=="__main__":
    # Genuine geometric P1xP1 packet:
    # anti-graph area/period 2/0, diagonal 2/2, holomorphic ruling 1/1.
    a=optimize((1,1,0),[[0,0,0]],[[-1],[-1],[2]],
               [[-1,1,0],[1,1,1]],(2,2,1),(0,2,1))
    assert a["optimum"]==(0,0,2) and a["optimal_defect"]==0
    # All integral carriers of period one in the (2,3) N model
    # retain positive absolute defect.
    b=optimize((-1,1),[[0,0]],[[-3],[2]],[[2,3]],(2,3),(2,3))
    assert b["optimal_defect"]==4
    print("P1xP1 homology-preserving calibrated replacement:",a)
    print("Unsaturated N-lattice fixed-class barrier:",b)
