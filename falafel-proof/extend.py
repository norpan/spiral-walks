# Check D of the Falafel proof (section 3): the facts that let checks B and C extend from laps 12..296
# to all laps. (1) key() is the spiral order; (2) stretch lengths; (3) the address set repeats every
# 12 laps; (4) each neighbour's quadrant is fixed within an address for all R; (5) so is whether a
# neighbour in the same stretch is visited before the step.  Run from falafel-proof/:
#   python3 extend.py 300
import sys
sys.path.insert(0, '.')
from lapcheck import lap
from walkf import run
from induct import NB, stretches, key
from sim import spiral

Rmax = int(sys.argv[1]); C = 8; R0 = 12

# (1) key() in (u,v) gives the same order as the spiral numbering
sq = [(x, y) for x in range(-60, 61) for y in range(-60, 61) if (x + y) % 2 == 0]
a = sorted(sq, key=lambda p: spiral(*p))
b = sorted(sq, key=lambda p: key(((p[0] + p[1]) // 2, (p[0] - p[1]) // 2)))
print("(1) key order equals spiral order on |x|,|y|<=60:", a == b)

# (2) every stretch length grows by a multiple of 6 when R grows by 12; all lengths nondecreasing in R
ok = all((y - x) % 6 == 0 for R in range(4, 400) for x, y in zip(stretches(R), stretches(R + 12)))
mono = all(y >= x for R in range(4, 400) for x, y in zip(stretches(R), stretches(R + 2)))
print("(2) +12 laps changes each length by a multiple of 6:", ok, "; lengths nondecreasing (same parity):", mono)

# (3) the set of addresses is 12-periodic from some lap on, and every address of laps up to 3000 occurs in 12..Rmax-4
def addrs(R):
    s = set()
    for sid, n in enumerate(stretches(R)):
        for i in range(n): s.add((R % 2, sid, min(i, C), min(n - 1 - i, C), i % 6))
    return s
seen = set()
for R in range(R0, Rmax - 3): seen |= addrs(R)
first_periodic = next(R for R in range(R0, 400) if all(addrs(r) == addrs(r + 12) for r in range(R, 400)))
new = [(R, x) for R in range(Rmax - 3, 3001) for x in addrs(R) - seen]
print("(3) address set 12-periodic from lap", first_periodic, "; addresses in laps", Rmax - 3, "..3000 not seen in laps 12..%d:" % (Rmax - 4), len(new))

# (4) quadrant of each neighbour fixed within an address, and stays fixed for larger R
init = run(80); T = {}; t = 0
for x, y in init: T[((x + y) // 2, (x - y) // 2)] = t; t += 1
paths = {}
for R in range(4, Rmax + 1):
    s, m = lap(R); q = s; P = [s]
    for du, dv in m: q = (q[0] + du, q[1] + dv); T[q] = t; t += 1; P.append(q)
    paths[R] = P
ext = {}  # (addr, j) -> {R: [minU, maxU, minV, maxV]}
for R in range(R0, Rmax - 3):
    P = paths[R]; k = 0
    for sid, n in enumerate(stretches(R)):
        for i in range(n):
            p = P[k]; ad = (R % 2, sid, min(i, C), min(n - 1 - i, C), i % 6)
            for j, (du, dv) in enumerate(NB):
                u, v = p[0] + du, p[1] + dv
                e = ext.setdefault((ad, j), {}).setdefault(R, [u, u, v, v])
                e[0] = min(e[0], u); e[1] = max(e[1], u); e[2] = min(e[2], v); e[3] = max(e[3], v)
            k += 1
def sgn(lo, hi):
    return '+' if lo > 0 else '-' if hi < 0 else '0' if lo == hi == 0 else None
mixed = []; drift = []; nonaff = 0
for (ad, j), byR in ext.items():
    sig = {(sgn(e[0], e[1]), sgn(e[2], e[3])) for e in byR.values()}
    if len(sig) != 1 or None in next(iter(sig)): mixed.append((ad, j, sig)); continue
    su, sv = next(iter(sig))
    for r in range(12):
        Rs = sorted(R for R in byR if R % 12 == r and R >= 12)
        if len(Rs) < 3: continue
        for c in range(4):
            f = [byR[R][c] for R in Rs]
            if any(f[i + 2] - 2 * f[i + 1] + f[i] for i in range(len(f) - 2)): nonaff += 1; continue
            slope = f[1] - f[0]
            s = su if c < 2 else sv
            # a positive minimum must not decrease, a negative maximum must not increase, a zero must stay 0
            if (s == '+' and c in (0, 2) and slope < 0) or (s == '-' and c in (1, 3) and slope > 0) or (s == '0' and slope):
                drift.append((ad, j, r, c, f[0], slope))
print("(4) (address, neighbour) pairs:", len(ext), "; quadrant not fixed:", len(mixed),
      "; extreme coordinates not affine in R per class mod 12:", nonaff, "; drifting toward an axis:", len(drift))
for x in mixed[:5]: print("   mixed", x)
for x in drift[:5]: print("   drift", x)

# (5) visited-before is stable: for a neighbour in the same stretch of the same lap as the step,
#     the index difference i2 - i keeps its sign within an address and does not drift toward 0
src = {}
for R in range(4, Rmax + 1):
    P = paths[R]; k = 1
    for sid, n in enumerate(stretches(R)):
        for i in range(n): src[P[k]] = (R, sid, i); k += 1
dif = {}
for R in range(R0, Rmax - 3):
    P = paths[R]; k = 0
    for sid, n in enumerate(stretches(R)):
        for i in range(n):
            p = P[k]; ad = (R % 2, sid, min(i, C), min(n - 1 - i, C), i % 6)
            for j, (du, dv) in enumerate(NB):
                s = src.get((p[0] + du, p[1] + dv))
                if s and s[0] == R and s[1] == sid:
                    # src index i2 = move that visits the square; the step is move i, so visited before it iff i2 < i
                    e = dif.setdefault((ad, j), {}).setdefault(R, [10**9, -10**9])
                    e[0] = min(e[0], s[2] - i); e[1] = max(e[1], s[2] - i)
            k += 1
bad5 = 0
for key_, byR in dif.items():
    sig = {('+' if lo >= 0 else '-' if hi < 0 else None) for lo, hi in byR.values()}  # i2 >= i: not yet visited
    if len(sig) != 1 or None in sig: bad5 += 1; continue
    s = next(iter(sig))
    for r in range(12):
        Rs = sorted(R for R in byR if R % 12 == r)
        if len(Rs) < 3: continue
        f = [byR[R][0 if s == '+' else 1] for R in Rs]
        if any(f[i + 2] - 2 * f[i + 1] + f[i] for i in range(len(f) - 2)) or (s == '+' and f[1] < f[0]) or (s == '-' and f[1] > f[0]): bad5 += 1
print("(5) same-stretch neighbour pairs:", len(dif), "; sign of index difference not fixed, not affine, or drifting toward 0:", bad5)
