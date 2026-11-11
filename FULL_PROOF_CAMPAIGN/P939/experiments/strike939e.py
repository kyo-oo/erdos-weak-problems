# P939 STRIKE D — r=3 escalation to 10^13 (calibration tightening: observed count vs
# the uniform/local model at one more decade).
import sys
sys.path.insert(0, '.')
import importlib.util
spec = importlib.util.spec_from_file_location("s939b", "strike939b.py")
# avoid re-running the module main: copy the needed pieces instead
import time, math, bisect
import numpy as np
from sympy import primerange

exec(open("strike939b.py").read().split("res4 = profile")[0])

res = profile(3, 10 ** 13, "r3@1e13")
print("\nCALIBRATION (updated):")
print(f"  r=3 @10^12: E_unif=29.8873  E_cond=55.3071  observed=1")
print(f"  r=3 @10^13: E_unif={res['E_unif']:.4f}  E_cond={res['E_cond']:.4f}  observed={len(res['hits'])}")
