#!/usr/bin/env python3
"""Exact checks of TWO interacting GST exceptional births.

Run: python3 research/computations/gst_mixed_blowup_birth.py
The scheme dictionary and the all-dimension proofs are recorded separately.
This script implements complete rational matrices and bounded Chern series;
it does not construct schemes or certify arbitrary-X source existence.
"""
from fractions import Fraction as Q
from itertools import product
from math import factorial, prod
import json


def dot(a, b):
    return sum((x*y for x, y in zip(a, b)), Q(0))


def mv(a, x):
    return [dot(row, x) for row in a]


def mm(a, b):
    return [[dot(row, col) for col in zip(*b)] for row in a]


def det3(a):
    return (a[0][0]*(a[1][1]*a[2][2]-a[1][2]*a[2][1])
            - a[0][1]*(a[1][0]*a[2][2]-a[1][2]*a[2][0])
            + a[0][2]*(a[1][0]*a[2][1]-a[1][1]*a[2][0]))


def convolution(a, b, degree):
    return [sum((a[j]*b[k-j] for j in range(k+1)), Q(0))
            for k in range(degree+1)]


def model(m):
    eta = Q((-1)**m)
    a, b = (1+eta)/2, (1-eta)/2
    gram = [[Q(1),Q(0),Q(0)], [Q(0),-a,-b], [Q(0),-b,-a]]
    z, ca = [Q(0),Q(1),Q(-1)], [Q(0),Q(1),Q(0)]
    readout = [-eta*x for x in mv(gram, ca)]
    projector = [[zi*ell for ell in readout] for zi in z]
    return eta, gram, z, ca, readout, projector


def main():
    rows, grid_checks = [], 0
    for m in range(1, 13):
        eta, gram, z, ca, ell, projector = model(m)
        pairing = dot(z, mv(gram, ca))
        mixed_degree = eta*pairing
        assert det3(gram) == eta
        assert dot(z, mv(gram, z)) == -2*eta
        assert z[0] == 0 and mixed_degree == -1 and dot(ell,z) == 1
        assert mm(projector,projector) == projector
        assert all(v.denominator == 1 for row in projector for v in row)
        for u in product(map(Q, range(-2,3)), repeat=3):
            assert mv(projector,mv(projector,u)) == mv(projector,u)
            grid_checks += 1
        for k in (Q(3),Q(7,2),Q(4),Q(9)):
            cup = [[k,Q(1),Q(1)],[Q(-2),k-3,k-3]]
            minor = cup[0][0]*cup[1][1]-cup[0][1]*cup[1][0]
            assert minor == (k-1)*(k-2) and minor != 0
            assert mv(cup,z) == [0,0]
            for t in (Q(-7,3),Q(-1),Q(0),Q(1,2),Q(5)):
                alpha = [t*x for x in z]
                assert mv(cup,alpha) == [0,0]
                assert dot(ell,alpha) == t
                assert mv(projector,alpha) == alpha
        # Actual K0 factor O_F has ch=1-exp(-f). Its p-th derived
        # tensor starts in grade p with coefficient exactly one.
        p, top = m+1, 2*(m+1)
        divisor_ch = [Q(0)] + [Q((-1)**(j+1),factorial(j))
                                for j in range(1,top+1)]
        power = [Q(1)]+[Q(0)]*top
        for _ in range(p):
            power = convolution(power,divisor_ch,top)
        assert all(v == 0 for v in power[:p]) and power[p] == 1
        source_ch = [Q(0)]*p + [Q(1)] + [Q(7*j-11) for j in range(p+1,top+1)]
        combined = convolution(source_ch,power,top)
        assert all(v == 0 for v in combined[:top]) and combined[top] == 1
        # A nontrivial Todd series cannot alter a top-supported character.
        todd = [Q(1)]+[Q(5*j-3,j+1) for j in range(1,top+1)]
        assert convolution(combined,todd,top) == combined
        rows.append({'m':m,'dimension_first_world':top,'second_center_codimension':p,
                     'first_push':int(z[0]),'primitive_square':int(-2*eta),
                     'mixed_top_push':int(mixed_degree),'unit_readout':int(dot(ell,z)),
                     'ambient_gram_determinant':int(det3(gram)),
                     'perfect_source_Euler':int(mixed_degree)})
    word_count = 0
    for arity in range(7):
        for dimensions in product((1,2,3),repeat=arity):
            values = [dot(model(m)[4],model(m)[2]) for m in dimensions]
            assert prod(values) == 1
            mixed = [model(m)[0]*dot(model(m)[2],mv(model(m)[1],model(m)[3]))
                     for m in dimensions]
            assert prod(mixed) == (-1)**arity
            word_count += 1
    assert word_count == sum(3**r for r in range(7)) == 1093
    print(json.dumps({
        'assertion_tested':'Complete middle-pairing and mixed-birth matrices for m=1..12; '
                           'exact Chern convolution through dimension 2m+2; all 1093 words '
                           'of arity 0..6 over dimensions m=1,2,3',
        'coefficient_domain':'Q, exact Fraction arithmetic',
        'middle_basis':['H^(m+1)','C_A','C_B'],
        'rows':rows,'projector_grid_checks':grid_checks,
        'cosmology_words_visited':word_count,
        'structural_results':{'old_push_of_source':0,'new_mixed_push_of_source':-1,
                              'normalized_feedback_readout':1,
                              'ample_cup_minor':'(k-1)*(k-2)',
                              'primitive_dimension':1,
                              'integral_projector_idempotent':True,
                              'derived_K0_source_top_Euler':-1},
        'non_claims':['No general-X source or non-tautological center is constructed',
                      'The rational coordinate model needs the stated canonical blowup comparison',
                      'No Hodge counterexample follows from the old pushforward kernel',
                      'Finite m and word tests do not replace the unrestricted Lean proofs']
    },indent=2))


if __name__=='__main__':
    main()
