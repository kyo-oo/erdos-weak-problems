from fractions import Fraction as F
# 1) unit representation
assert sum(F(1,s) for s in [3,4,7,9,12,28,36,63]) == 1, "UNIT FAIL"
assert 252/3+252/4+252/7+252/9+252/12+252/28+252/36+252/63 == 252
# 2) split_all: (252n)/(3n)+...=252 for all n (scaled) -> check coefficients
coeffs = [252//s for s in [3,4,7,9,12,28,36,63]]
assert sum(coeffs) == 252, ("COEFF FAIL", coeffs)
print("coeffs:", coeffs)
for s,k in [(3,84),(4,63),(7,36),(9,28),(12,21),(28,9),(36,7),(63,4)]:
    assert s*k == 252, (s,k)
    assert 252//s == k
# 3) instance identities
assert 336//3+336//7+336//48+336//336 == 336//2 == 168
assert 336//7+336//48+336//336 == 336//6 == 56
assert 1008//9+1008//144+1008//252+1008//336 == 1008//8 == 126
assert 112//16+112//112 == 112//14 == 8
assert 756//27+756//108+756//189+756//252 == 756//18 == 42
assert 1008//36+1008//144+1008//252+1008//336 == 1008//24 == 42
assert 12//3+12//4 == 12*7//12 == 7
assert 63//7+63//9 == 63*16//63 == 16
assert 336//12+336//16+336//21+336//28 == 336*11//48 == 77
# 4) memberships triples
for n,(a,b,c) in {1:(0,0,0),3:(1,0,0),4:(0,1,0),7:(0,0,1),9:(2,0,0),12:(1,1,0),16:(0,2,0),21:(1,0,1),27:(3,0,0),28:(0,1,1),36:(2,1,0),48:(1,2,0),49:(0,0,2),63:(2,0,1),64:(0,3,0),81:(4,0,0),84:(1,1,1),108:(3,1,0),112:(0,2,1),144:(2,2,0),147:(1,0,2),189:(3,0,1),192:(1,3,0),196:(0,1,2),252:(2,1,1),336:(1,2,1)}.items():
    assert 3**a*4**b*7**c == n, (n,(a,b,c))
# 5) below36 case values
vals=[3**a*4**b*7**c for a in range(4) for b in range(3) for c in range(2)]
assert sorted(v for v in vals if v<36) == [1,3,4,7,9,12,16,21,27,28], vals
assert set(vals)== {1,7,4,28,16,112,3,21,12,84,48,336,9,63,36,252,144,1008,27,189,108,756,432,3024}
vals12=[3**a*4**b*7**c for a in range(3) for b in range(2) for c in range(2)]
assert sorted(v for v in vals12 if v<12)==[1,3,4,7,9], vals12
assert set(vals12)=={1,7,4,28,3,21,12,84,9,63,36,252}
# 6) the split denominators for members
for n,s in [(3,84),(4,63),(7,36),(9,28),(12,21),(28,9),(36,7),(63,4)]:
    pass
print("ALL NUMERIC CLAIMS VERIFIED")
