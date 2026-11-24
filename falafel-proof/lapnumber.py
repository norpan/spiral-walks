# Lap-number function for the Falafel walk (A399160), in the coordinates
#   u = (x+y)/2, v = (x-y)/2.
# Claim: every square visited during lap R (R >= 4) has L(u,v) = R.
# Because L is a function of the square alone, squares of different laps can then never coincide.
# Usage: python3 lapnumber.py NMAX_L NMAX_COVER
import sys
from lapcheck import lap
from walkf import run

def L(u, v):
    if u <= 1 and v >= 2 and u + v >= 1:   return v                      # 1 north row
    if v >= 2 and u + v <= 0:              return (v - u)//2 + 1         # 2 north-west staircase
    if u <= -2 and abs(v) <= 1:            return (3 - u)//2             # 3 west corner
    if u <= -2 and v <= -2:                return (1 - u - v)//2         # 4 south-west staircase
    if abs(u) <= 1 and v <= -2:            return (2 - v)//2             # 5 south corner
    if u >= 2 and v <= -2:                 return (u - v)//2             # 6 south-east staircase
    if u >= 2 and abs(v) <= 1:             return (u + 1)//2             # 7 east corner
    if u >= 2 and v >= 2:
        if u - 3*v >= -6:                  return (u + v - 1)//2         # 8 north-east staircase
        if u == 3:                         return 2*(v//2) + 1           # 9 column u = 3
        s = u + 3*v                                                       # 10 descent
        return {0: s//3 - 2, 1: (s-4)//3, 2: (s-5)//3, 3: (s-3)//3, 4: (s-4)//3, 5: (s-2)//3}[s % 6]
    return None                                                           # centre block |u|,|v| <= 1

def squares(R):
    q, m = lap(R); out = []
    for du, dv in m:
        q = (q[0]+du, q[1]+dv); out.append(q)
    return out

if __name__ == "__main__":
    NL = int(sys.argv[1]); NC = int(sys.argv[2])
    bad = 0; total = 0
    for R in range(4, NL+1):
        for q in squares(R):
            total += 1
            if L(*q) != R:
                bad += 1
                if bad <= 20: print("WRONG lap number: lap", R, "square", q, "L =", L(*q))
    print("laps 4..%d: %d squares, wrong lap numbers: %d" % (NL, total, bad))
    # distinct within laps, and exact cover: {L = R} is exactly the set of squares of lap R
    lev = {}
    B = 2*NC + 12
    for u in range(-B, B+1):
        for v in range(-B, B+1):
            l = L(u, v)
            if l is not None and 4 <= l <= NC: lev.setdefault(l, set()).add((u, v))
    nd = 0; nc = 0
    for R in range(4, NC+1):
        s = squares(R)
        if len(set(s)) != len(s): nd += 1; print("repeat inside lap", R)
        if set(s) != lev.get(R, set()):
            nc += 1
            if nc <= 10:
                print("level set differs for lap", R, "only in lap:", sorted(set(s)-lev[R])[:6], "only in level:", sorted(lev[R]-set(s))[:6])
    print("laps 4..%d: laps with a repeated square: %d; laps whose squares differ from {L = R}: %d" % (NC, nd, nc))
    # the first 80 terms
    P = run(80); uv = [((x+y)//2, (x-y)//2) for x, y in P]
    ls = [L(*q) for q in uv]
    print("first 80 squares: last =", uv[-1], "; lap numbers >= 4 among them:", [(q, l) for q, l in zip(uv, ls) if l is not None and l >= 4])
    low = set()
    for u in range(-20, 21):
        for v in range(-20, 21):
            l = L(u, v)
            if l is None or l <= 3: low.add((u, v))
    print("squares with L <= 3 or undefined:", len(low), "; first 80 squares distinct:", len(set(uv)), "; equal as sets:", low == set(uv))
    if low != set(uv):
        print(" in low only:", sorted(low - set(uv))[:20]); print(" in walk only:", sorted(set(uv) - low)[:20])
