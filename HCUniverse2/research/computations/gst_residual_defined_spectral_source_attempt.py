#!/usr/bin/env python3
"""Test a bundle constructed from the prescribed primitive Hodge tensor.

Run: python3 research/computations/gst_residual_defined_spectral_source_attempt.py
This tests the proposed constructor itself. It asserts no universal Hodge
theorem and creates no conditional source-existence field.
"""
from fractions import Fraction as Q
from itertools import combinations
from math import comb
import json


def add(a,b):
    return [[x+y for x,y in zip(u,v)] for u,v in zip(a,b)]


def scale(c,a):
    return [[c*x for x in row] for row in a]


def multiply(a,b):
    return [[sum((x*y for x,y in zip(row,col)),Q(0)) for col in zip(*b)] for row in a]


def trace(a):
    return sum((a[i][i] for i in range(len(a))),Q(0))


def wedge(a,b):
    out={}
    for ia,va in a.items():
        for ib,vb in b.items():
            if ia & ib:
                continue
            inversions=sum((ib & ((1<<k)-1)).bit_count() for k in range(8) if ia & (1<<k))
            key=ia|ib
            out[key]=out.get(key,Q(0))+(-1)**inversions*va*vb
    return {key:value for key,value in out.items() if value}


def main():
    identity=[[Q(int(i==j)) for j in range(6)] for i in range(6)]
    zero=[[Q(0)]*6 for _ in range(6)]
    symbol=[[Q(0)]*6 for _ in range(6)]
    symbol[0][5]=symbol[5][0]=Q(1)
    # Independent construction from the actual (2,2) tensor
    # z12 bar(z34)+z34 bar(z12), ordered z1,...,z4,bar(z1),...,bar(z4).
    pairs=list(combinations(range(4),2))
    complex_tensor={195:Q(1),60:Q(1)}
    tensor_symbol=[]
    for pair in pairs:
        row=[]
        hol={sum(1<<i for i in pair):Q(1)}
        for other in pairs:
            antihol={sum(1<<(i+4) for i in other):Q(1)}
            row.append(wedge(wedge(complex_tensor,hol),antihol).get(255,Q(0)))
        tensor_symbol.append(row)
    assert tensor_symbol==symbol
    square=multiply(symbol,symbol)
    assert multiply(square,symbol)==symbol
    positive=scale(Q(1,2),add(square,symbol))
    negative=scale(Q(1,2),add(square,scale(Q(-1),symbol)))
    null=add(identity,scale(Q(-1),square))
    projections=[positive,negative,null]
    for i,projection in enumerate(projections):
        assert multiply(projection,projection)==projection
        for j,other in enumerate(projections):
            if i!=j:
                assert multiply(projection,other)==zero
    assert add(add(positive,negative),null)==identity
    assert [trace(p) for p in projections]==[1,1,4]
    assert multiply(symbol,positive)==positive
    assert multiply(symbol,negative)==scale(Q(-1),negative)
    matrix_detection=trace(multiply(symbol,add(positive,scale(Q(-1),negative))))
    assert matrix_detection==2
    # Real Weil form Re product_j(u_j+i v_j), in complex structure
    # with opposite K embeddings in the last two slots. Its Hermitian
    # (2,2) symbol on Lambda^2 is the displayed matrix up to a nonzero
    # scalar, which has no effect on the two nonzero spectral subspaces.
    residual={}
    for choices in range(16):
        count=choices.bit_count()
        if count%2==0:
            mask=sum(1<<(2*j+((choices>>j)&1)) for j in range(4))
            residual[mask]=Q((-1)**(count//2))
    theta={3:Q(1),12:Q(1),48:Q(-1),192:Q(-1)}
    theta_square=wedge(theta,theta)
    assert wedge(residual,theta)=={}
    assert wedge(residual,residual)=={255:Q(8)}
    assert wedge(theta_square,theta_square)=={255:Q(24)}
    # Image bundles of the CONSTANT algebraic projectors on Omega_A^2
    # are trivial. Twisting any image by L^k gives ch2=rank*k^2*theta^2/2.
    checks=[]
    for rank in (1,2,4,6,8,12):
        for k in (-7,-1,0,1,3,11):
            ch2={key:Q(rank*k*k,2)*value for key,value in theta_square.items()}
            c2={key:Q(comb(rank,2)*k*k)*value for key,value in theta_square.items()}
            assert wedge(residual,ch2)=={}
            assert wedge(residual,c2)=={}
            checks.append({'rank':rank,'twist':k,'native_primitive_period':0})
    # A basepoint-free evaluation construction using a target-selected
    # constant subspace V of H0(L^k) has exact class [M_V]=dim(V)-[L^k].
    # Its primitive ch2 period also vanishes, independent of the matrix
    # used to select V. No base-locus component is assumed algebraic here.
    for k in range(1,25):
        kernel_character={key:-Q(k*k,2)*value for key,value in theta_square.items()}
        assert wedge(residual,kernel_character)=={}
    # Universal integrability check: N is trace-free nilpotent. The
    # smooth (0,1) connection A=N*bar(z1)*dbar(z2) has obstruction
    # F^(0,2)=N*dbar(z1)dbar(z2), although every trace power is zero.
    nilpotent=[[Q(0),Q(1)],[Q(0),Q(0)]]
    assert nilpotent!=[[0,0],[0,0]]
    power=[[Q(1),Q(0)],[Q(0),Q(1)]]
    for j in range(1,13):
        power=multiply(power,nilpotent)
        assert trace(power)==0
        if j>=2:
            assert power==[[0,0],[0,0]]
    print(json.dumps({
        'constructor_tested':'Prescribed primitive residual -> Hermitian spectral symbol on Omega^2 -> actual algebraic image bundle -> original-X smooth incidence center',
        'coefficient_domain':'Q, exact Fraction matrices and exterior products',
        'symbol_basis':['12','13','14','23','24','34'],
        'symbol':[[int(x) for x in row] for row in symbol],
        'spectral_ranks':[1,1,4],
        'symbol_independently_recovered_from_Hodge_tensor':True,
        'nonzero_fiber_operator_detection':int(matrix_detection),
        'actual_primitive_residual_square':8,
        'polarization_top_degree':24,
        'spectral_bundle_center_period_checks':checks,
        'basepoint_free_kernel_twists_checked':[1,24],
        'trace_cancellation_integrability_test':{'full_obstruction_matrix_nonzero':True,'trace_powers_checked':[1,12],'all_checked_traces_zero':True},
        'outcome':'The residual-defined spectral bundles exist algebraically but have zero primitive Chern period; this specific constructor fails the requested detector test.',
        'unrestricted_derivation':'Constant projectors in the trivial translation-invariant Omega^2 bundle have trivial image bundles. Their polarized twists and basepoint-free evaluation kernels have Chern character in Q[theta], killed by the displayed primitive residual.',
        'non_claims':['No counterexample to rational Hodge algebraicity','No no-go for other bundles, nonparallel incidence or component-changing constructions','A nonintegrable chosen connection does not imply its underlying bundle admits no integrable structure','The matrix symbol is normalized by a harmless nonzero scalar; no native Chern class is identified with its matrix eigenvalues']
    },indent=2))


if __name__=='__main__':
    main()
