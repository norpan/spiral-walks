#!/usr/bin/env python3
"""Checks for the proof in doc/pieces.md that the (s,s)-leaper (s = 1 Ferz, s = 2 Alfil) is never
trapped on the square spiral: it walks the diamonds |x|+|y| = 2ks, k = 1, 2, 3, ..., clockwise.

  python3 check.py [STEPS] [K]     defaults 2000000 and 400; about a minute for s = 1, 2, 3

1. Simulates the walk by the rule for STEPS steps and compares it with the diamond path.
2. Checks every inequality of the proof (cases Q1-Q4, X1-X4, first square, start) on diamonds 1..K.
3. Checks the step count: diamond k is terms 4k(k-1)+2 .. 4k(k+1)+1.
"""
import sys

def spiral(x, y):
    r = max(abs(x), abs(y))
    if r == 0: return 1
    b = (2*r - 1)**2
    if x == r and y > -r: return b + r + y
    if y == r: return b + 3*r - x
    if x == -r: return b + 5*r - y
    return b + 7*r + x

def diamond(s, k):
    """The 8k squares of diamond k in walking order, from (s,(2k-1)s) clockwise to (0,2ks)."""
    x, y = s, (2*k - 1)*s
    yield x, y
    for dx, dy, n in ((s, -s, 2*k - 1), (-s, -s, 2*k), (-s, s, 2*k), (s, s, 2*k)):
        for _ in range(n):
            x += dx; y += dy
            yield x, y

def path(s):
    yield 0, 0
    k = 1
    while True:
        yield from diamond(s, k)
        k += 1

def simulate(s, steps):
    mv = [(s, s), (s, -s), (-s, s), (-s, -s)]
    x = y = 0; seen = {(0, 0)}; yield 0, 0
    for _ in range(steps - 1):
        c = [(spiral(x+dx, y+dy), x+dx, y+dy) for dx, dy in mv if (x+dx, y+dy) not in seen]
        assert c, "trapped"
        _, x, y = min(c); seen.add((x, y)); yield x, y

def check_cases(s, K):
    n = 0
    assert spiral(s, s) < min(spiral(-s, s), spiral(-s, -s), spiral(s, -s)); n += 1      # start
    for k in range(1, K + 1):
        d = 2*k*s
        assert spiral(2*s, d - 2*s) < spiral(0, d); n += 1                               # first square
        for a in range(s, d, s):
            b = d - a
            assert spiral(a + s, b - s) < spiral(a + s, b + s)                           # Q1
            assert spiral(a - s, -b - s) < spiral(a + s, -b - s)                         # Q4
            assert spiral(-a - s, -b + s) < spiral(-a - s, -b - s)                       # Q3
            assert spiral(-a + s, b + s) < spiral(-a - s, b + s)                         # Q2
            n += 4
        assert spiral(d - s, -s) < min(spiral(d + s, s), spiral(d + s, -s))              # X1 (d,0)
        assert spiral(-s, -d + s) < min(spiral(s, -d - s), spiral(-s, -d - s))           # X2 (0,-d)
        assert spiral(-d + s, s) < min(spiral(-d - s, s), spiral(-d - s, -s))            # X3 (-d,0)
        assert spiral(s, d + s) < spiral(-s, d + s)                                      # X4 (0,d)
        n += 4
    return n

steps = int(sys.argv[1]) if len(sys.argv) > 1 else 2000000
K = int(sys.argv[2]) if len(sys.argv) > 2 else 400
for s in (1, 2, 3):
    m = 0
    for p, q in zip(simulate(s, steps), path(s)):
        assert p == q, (s, m, p, q)
        m += 1
    print(f"s={s}: rule = diamond path for {m} steps; ", end="")
    print(f"{check_cases(s, K)} inequalities hold on diamonds 1..{K}; ", end="")
    t = 1
    for k in range(1, 200):
        sq = list(diamond(s, k))
        assert len(sq) == 8*k and len(set(sq)) == 8*k and t + 1 == 4*k*(k-1) + 2
        assert all(abs(x) + abs(y) == 2*k*s for x, y in sq)
        t += 8*k
        assert t == 4*k*(k+1) + 1
    print("step counts hold for k < 200")
terms = [spiral(x, y) for (x, y), _ in zip(path(1), range(26))]
print("F:", terms)
terms = [spiral(x, y) for (x, y), _ in zip(path(2), range(18))]
print("A:", terms)
