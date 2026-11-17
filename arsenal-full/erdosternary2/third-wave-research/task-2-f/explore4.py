def d(p, x):
    return (4**x // (3**p)) % 3

for p in range(1, 7):
    M = 3**p
    row = [d(p, x) for x in range(M)]
    print(f"p={p} row len {M}:")
    print("  ", row)
