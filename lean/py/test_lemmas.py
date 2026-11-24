# The lemma statements of the Lean proof, evaluated on a box, with the definitions read from the Lean
# files themselves (leanmodel.py). This is a test, not a proof: the proof is the Lean build.
# Usage: python3 test_lemmas.py BOX [NSIM]     squares with |u|, |v| <= BOX; NSIM simulated steps
import sys
from leanmodel import lapnum, pos, lo, hi, du, dv, squ, sqv, ring, rpos, PREFIX
BOX = int(sys.argv[1]); NSIM = int(sys.argv[2]) if len(sys.argv) > 2 else 30000
# Stamp.lean, mirrored by hand
def pidx(u, v): return PREFIX.index((u, v)) if (u, v) in PREFIX else len(PREFIX)      # locate
def pget(i): return PREFIX[i] if i < len(PREFIX) else (0, 0)                           # getD
def lap(u, v): return 3 if lapnum(u, v) <= 3 else lapnum(u, v)
def idx(u, v): return pidx(u, v) if lapnum(u, v) <= 3 else pos(u, v)
def lolap(R): return 0 if R <= 3 else lo(R)
def hilap(R): return 80 if R <= 3 else hi(R)
def stepu(u, v): return pget(pidx(u, v) + 1)[0] if lapnum(u, v) <= 3 and pidx(u, v) < 79 else u + du(u, v)
def stepv(u, v): return pget(pidx(u, v) + 1)[1] if lapnum(u, v) <= 3 and pidx(u, v) < 79 else v + dv(u, v)
def Later(u1, v1, u, v): return lap(u, v) < lap(u1, v1) or (lap(u, v) == lap(u1, v1) and idx(u, v) < idx(u1, v1))
def KeyLE(a, b, c, d): return ring(a, b) < ring(c, d) or (ring(a, b) == ring(c, d) and rpos(a, b) <= rpos(c, d))
def Rook(a, b): return (b == 0 and a in (1, -1, 2, -2)) or (a == 0 and b in (1, -1, 2, -2))
OFF = [(1, 0), (-1, 0), (2, 0), (-2, 0), (0, 1), (0, -1), (0, 2), (0, -2)]
def StepOK(u, v):
    su, sv = stepu(u, v), stepv(u, v)
    return (lap(su, sv) == lap(u, v) and idx(su, sv) == idx(u, v) + 1) or \
           (lap(su, sv) == lap(u, v) + 1 and idx(su, sv) == lolap(lap(u, v) + 1) and idx(u, v) + 1 == hilap(lap(u, v)))
def Greedy(u, v, a, b): return (not Later(u + a, v + b, u, v)) or KeyLE(stepu(u, v), stepv(u, v), u + a, v + b)
def GreedyBig(u, v, a, b, c, d):          # (a, b) is the move, (c, d) the neighbour
    if not (lapnum(u, v) < lapnum(u + c, v + d) or (lapnum(u, v) == lapnum(u + c, v + d) and pos(u, v) < pos(u + c, v + d))): return True
    return KeyLE(u + a, v + b, u + c, v + d)
sq = [(u, v) for u in range(-BOX, BOX + 1) for v in range(-BOX, BOX + 1)]
big = [q for q in sq if lapnum(*q) >= 4]
fails = []
def check(name, f, dom=sq):
    bad = [q for q in dom if not f(*q)]
    if bad: fails.append(name)
    print("%-16s %s %s" % (name, "ok" if not bad else "FAILS", bad[:4]))
print("box |u|,|v| <= %d: %d squares, %d of them with lap number >= 4" % (BOX, len(sq), len(big)))
# Laps.lean
check("pos_range", lambda u, v: lo(lapnum(u, v)) <= pos(u, v) < hi(lapnum(u, v)), big)
check("sq_pos", lambda u, v: (squ(lapnum(u, v), pos(u, v)), sqv(lapnum(u, v), pos(u, v))) == (u, v), big)
def step_big(u, v):
    a, b = u + du(u, v), v + dv(u, v)
    return (lapnum(a, b) == lapnum(u, v) and pos(a, b) == pos(u, v) + 1) or \
           (lapnum(a, b) == lapnum(u, v) + 1 and pos(a, b) == lo(lapnum(u, v) + 1) and pos(u, v) + 1 == hi(lapnum(u, v)))
check("step_big", step_big, big)
check("rook_big", lambda u, v: Rook(du(u, v), dv(u, v)), big)
for c, d in OFF:
    check("greedy %2d %2d" % (c, d), lambda u, v: GreedyBig(u, v, du(u, v), dv(u, v), c, d), big)
# Prefix.lean
ok = all(lapnum(*pget(i)) <= 3 and pidx(*pget(i)) == i and StepOK(*pget(i)) and
         Rook(stepu(*pget(i)) - pget(i)[0], stepv(*pget(i)) - pget(i)[1]) and
         all(Greedy(*pget(i), a, b) for a, b in OFF) for i in range(80))
print("%-16s %s" % ("prefix_table", "ok" if ok else "FAILS")); fails += [] if ok else ["prefix_table"]
ok = all((not lapnum(i - 4, j - 5) <= 3) or (pidx(i - 4, j - 5) < 80 and pget(pidx(i - 4, j - 5)) == (i - 4, j - 5))
         for i in range(11) for j in range(10))
print("%-16s %s" % ("prefix_box", "ok" if ok else "FAILS")); fails += [] if ok else ["prefix_box"]
check("low_bounds", lambda u, v: lapnum(u, v) > 3 or (-4 <= u <= 6 and -5 <= v <= 4))
# Squares.lean
check("step_ok", StepOK)
check("rook_ok", lambda u, v: Rook(stepu(u, v) - u, stepv(u, v) - v))
check("all_greedy", lambda u, v: all(Greedy(u, v, a, b) for a, b in OFF))
check("idx_range", lambda u, v: lap(u, v) >= 3 and lolap(lap(u, v)) <= idx(u, v) < hilap(lap(u, v)))
st = {}
for q in sq: st.setdefault((lap(*q), idx(*q)), []).append(q)
ok = all(len(l) == 1 for l in st.values())
print("%-16s %s" % ("stamp_inj", "ok" if ok else "FAILS")); fails += [] if ok else ["stamp_inj"]
print("%-16s %s" % ("origin", "ok" if (lap(0, 0), idx(0, 0)) == (3, 0) else "FAILS"))
# exact cover: for every lap that lies inside the box, the indices of its squares are exactly lo .. hi - 1
Rmax = (BOX - 4)//2
lev = {}
for q in big: lev.setdefault(lapnum(*q), []).append(pos(*q))
bad = [R for R in range(4, Rmax + 1) if sorted(lev[R]) != list(range(lo(R), hi(R)))]
print("%-16s %s (laps 4..%d) %s" % ("exact cover", "ok" if not bad else "FAILS", Rmax, bad[:4])); fails += ["cover"] if bad else []
# the closed-form path against the write-up's closed forms (falafel-proof/lapsquares.py), lap by lap
import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "falafel-proof"))
try:
    import lapsquares
    bad = [R for R in range(4, Rmax + 1)
           if [(squ(R, j), sqv(R, j)) for j in range(lo(R), hi(R))] != [q for _, l in lapsquares.stretches(R) for q in l]]
    print("%-16s %s (laps 4..%d) %s" % ("path = write-up", "ok" if not bad else "FAILS", Rmax, bad[:4])); fails += ["writeup"] if bad else []
except ImportError:
    print("path = write-up  skipped: ../../falafel-proof/lapsquares.py not found")
# Spiral.lean
def spiral(x, y):
    r = max(abs(x), abs(y))
    if x == r and y > -r: return (2*r - 1)**2 + (y + r)
    if y == r: return (2*r - 1)**2 + 2*r + (r - x)
    if x == -r: return (2*r - 1)**2 + 4*r + (r - y)
    return (2*r - 1)**2 + 6*r + (x + r)
check("spiral_uv", lambda u, v: spiral(u + v, u - v) == (2*ring(u, v) - 1)**2 + rpos(u, v))
check("rpos_bounds", lambda u, v: 0 <= rpos(u, v) <= 8*ring(u, v) and (ring(u, v) < 1 or rpos(u, v) >= 1) and ring(u, v) >= 0)
# the walk of the model against the walk simulated from the statement
MV = [(1,1),(1,-1),(-1,1),(-1,-1),(2,2),(2,-2),(-2,2),(-2,-2)]
a = [(0, 0)]; vis = {(0, 0)}
while len(a) < NSIM:
    x, y = a[-1]
    c = [(x+dx, y+dy) for dx, dy in MV if (x+dx, y+dy) not in vis]
    q = min(c, key=lambda p: spiral(*p)); a.append(q); vis.add(q)
w = [(0, 0)]
while len(w) < NSIM: w.append((stepu(*w[-1]), stepv(*w[-1])))
ok = [(u + v, u - v) for u, v in w] == a
print("%-16s %s (%d steps)" % ("walk = simulation", "ok" if ok else "FAILS", NSIM)); fails += [] if ok else ["walk"]
print("ALL OK" if not fails else "FAILURES: %s" % fails)
