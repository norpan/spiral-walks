# Closed-form list of the squares of lap R (u,v coordinates), stretch by stretch,
# compared with the move-list formula in lapcheck.lap(R).  Usage: python3 lapsquares.py NMAX
import sys
from lapcheck import lap
from lapnumber import L
def stretches(R):
    S = []
    if R % 2 == 0: S.append(("T",  [(0, R), (1, R), (-1, R)]));      u0 = -2
    else:          S.append(("T",  [(3, R-1), (3, R), (1, R)]));     u0 = 0
    S.append(("W",  [(u, R) for u in range(u0, -(R-1)-1, -1)]))
    nw = []
    for k in range(0, R-2): nw += [(-(R-1)-k, R-1-k), (-R-k, R-1-k)]
    S.append(("NW", nw))
    a, b = -(2*R-3), -(2*R-2)
    S.append(("WC", [(a, 0), (a, -1), (a, 1), (b, 1), (b, 0), (b, -1)]))
    S.append(("SW", [(-(2*R-2) + j//2, -1 - (j+1)//2) for j in range(1, 4*R-7+1)]))
    a, b = -(2*R-2), -(2*R-1)
    S.append(("SC", [(0, a), (1, a), (-1, a), (-1, b), (0, b), (1, b)]))
    S.append(("SE", [(1 + (j+1)//2, -(2*R-1) + j//2) for j in range(1, 4*R-5+1)]))
    a, b = 2*R-1, 2*R
    S.append(("EC", [(a, 0), (a, 1), (a, -1), (b, -1), (b, 0), (b, 1)]))
    S.append(("NE", [(2*R - j//2, 1 + (j+1)//2) for j in range(1, R+1+1)]))
    d = []
    if R % 2 == 0:
        h = R//2
        for k in range(0, h-1):
            d.append((3*h-3*k-2, h+2+k))
            if k <= h-3: d += [(3*h-3*k-3, h+2+k), (3*h-3*k-3, h+3+k)]
    else:
        p = (3*R-1)//2; w = (R+3)//2
        for k in range(0, (R-3)//2 + 1):
            d += [(p-3*k-2, w+k), (p-3*k-2, w+k+1)]
            if k <= (R-5)//2: d.append((p-3*k-3, w+k+1))
    S.append(("D", d))
    return S
REG = {"T": None, "W": 1, "NW": 2, "WC": 3, "SW": 4, "SC": 5, "SE": 6, "EC": 7, "NE": 8, "D": 10}
def region(u, v):
    if u <= 1 and v >= 2 and u + v >= 1: return 1
    if v >= 2 and u + v <= 0: return 2
    if u <= -2 and abs(v) <= 1: return 3
    if u <= -2 and v <= -2: return 4
    if abs(u) <= 1 and v <= -2: return 5
    if u >= 2 and v <= -2: return 6
    if u >= 2 and abs(v) <= 1: return 7
    if u >= 2 and v >= 2:
        if u - 3*v >= -6: return 8
        return 9 if u == 3 else 10
    return 0
if __name__ == "__main__":
    N = int(sys.argv[1]); bad = 0; badreg = 0; treg = set()
    for R in range(4, N+1):
        q, m = lap(R); path = []
        for du, dv in m: q = (q[0]+du, q[1]+dv); path.append(q)
        S = stretches(R); flat = [s for _, sq in S for s in sq]
        if flat != path:
            bad += 1
            if bad <= 5: print("closed form differs from move list in lap", R)
        for name, sq in S:
            for s in sq:
                r = region(*s)
                if name == "T": treg.add((R % 2, sq.index(s), r))
                elif r != REG[name]: badreg += 1
                if L(*s) != R: bad += 1
    print("laps 4..%d: laps where the closed form differs from the move list or L != R: %d" % (N, bad))
    print("squares outside the region stated for their stretch:", badreg)
    print("regions of the three top squares (parity of R, index, region):", sorted(treg))
