# The Lean model against the write-up (doc/falafel-proof.md). These two facts are checked here by
# program; they are not proved in Lean.
#   1. The lap number `lapnum` of Falafel/Model.lean is the L of section 4 (falafel-proof/lapnumber.py).
#   2. The closed-form squares `(squ R j, sqv R j)`, j = lo R .. hi R - 1, are the squares given by the
#      move table of the write-up (falafel-proof/lapcheck.py).
# Usage: python3 -B test_writeup.py BOX RMAX
import os, sys
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "falafel-proof"))
from leanmodel import lapnum, squ, sqv, lo, hi
import lapnumber, lapcheck
B = int(sys.argv[1]); RMAX = int(sys.argv[2])
bad = [(u, v) for u in range(-B, B + 1) for v in range(-B, B + 1) if lapnum(u, v) != (lapnumber.L(u, v) or 0)]
print("Lean lapnum = L of section 4 for |u|, |v| <= %d (centre block counted as 0):" % B, "ok" if not bad else "FAILS %s" % bad[:5])
def table_squares(R):
    q, m = lapcheck.lap(R); out = []
    for a, b in m:
        q = (q[0] + a, q[1] + b); out.append(q)
    return out
bad = [R for R in range(4, RMAX + 1) if [(squ(R, j), sqv(R, j)) for j in range(lo(R), hi(R))] != table_squares(R)]
print("Lean path (squ, sqv) = move table of the write-up for laps 4..%d:" % RMAX, "ok" if not bad else "FAILS %s" % bad[:5])
