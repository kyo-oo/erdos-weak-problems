import math, time
t0=time.time()
for L in (27720, 55440):
    g = math.gcd((1<<L)-1, pow(3,L)-1)
    print(f"L={L}: gcd bit length {g.bit_length()} ({g.bit_length()*math.log10(2):.0f} digits), t={time.time()-t0:.1f}s")
