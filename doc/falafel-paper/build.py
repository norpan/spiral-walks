#!/usr/bin/env python3
"""Builds the Falafel paper from paper.template.html, as a web page and as LaTeX.

Every formula in the paper's tables is written here once, as a Python expression. The script
first checks these expressions against the Lean definitions (read from lean/Falafel by
lean/py/leanmodel.py) and against a simulation of the walk, and only then prints them as
TeX. So the formulas a reader sees are the formulas that were tested.

It writes falafel-paper.html (the page, with MathJax) and falafel-paper.tex (LaTeX, made from the
same filled template by to_latex.py). If tectonic is installed it then compiles
falafel-paper.pdf.

Usage: python3 -B build.py [--no-pdf]
"""
import ast, html, os, re, shutil, subprocess, sys
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, "..", "..")
sys.path.insert(0, os.path.join(ROOT, "lean", "py"))
sys.path.insert(0, os.path.join(ROOT, "falafel-proof"))
import leanmodel as LM
import walkf
import to_latex

BOX = 300        # tables in (u, v) are compared with Lean for |u|, |v| <= BOX
RMAX = 300       # the path is compared with Lean for laps 4..RMAX
SIM = 200000     # steps of the simulation the walk is compared with
LBOX = 120       # the lemmas, as worded in the paper, are tested for |u|, |v| <= LBOX
MAPMAX = 120     # the regions are compared with the pieces for laps 4..MAPMAX
SMAX = 5000      # the start of a lap (Corollary 9) is compared with the lap lengths for laps 4..SMAX
SBOX = 200       # formula (1) is compared with the spiral, built step by step, for |x|, |y| <= SBOX
NSPIRAL = (2*SBOX + 1)**2    # the number of those squares
TEXTWIDTH_PT = 5.9 * 72.27   # the text width set in to_latex.PREAMBLE, in TeX points
MONO_ADVANCE = 0.61          # width of a character of DejaVu Sans Mono, in ems (0.602, with a margin)

# ----------------------------------------------------------------------------------------------
# The formulas of the paper
# ----------------------------------------------------------------------------------------------
AUX = {"q": "(u + 3*v)//6", "m": "(u + 3*v) % 6"}          # used in the rows of region 10

REGIONS = [  # number, name, condition
    (1, "north row", "v >= 2 and u <= 1 and u + v >= 1"),
    (2, "north-west staircase", "v >= 2 and u + v <= 0"),
    (3, "west corner", "abs(v) <= 1 and u <= -2"),
    (4, "south-west staircase", "v <= -2 and u <= -2"),
    (5, "south corner", "v <= -2 and abs(u) <= 1"),
    (6, "south-east staircase", "v <= -2 and u >= 2"),
    (7, "east corner", "abs(v) <= 1 and u >= 2"),
    (8, "north-east staircase", "v >= 2 and u >= 2 and u - 3*v >= -6"),
    (9, "column 3", "u == 3 and v >= 4"),
    (10, "return", "v >= 2 and u >= 2 and u != 3 and u - 3*v <= -7"),
    (0, "centre", "abs(u) <= 1 and abs(v) <= 1"),
]
LAMBDA = {  # region -> [(condition, value)]
    1: [("", "v")],
    2: [("", "(v - u)//2 + 1")],
    3: [("", "(3 - u)//2")],
    4: [("", "(1 - u - v)//2")],
    5: [("", "(2 - v)//2")],
    6: [("", "(u - v)//2")],
    7: [("", "(u + 1)//2")],
    8: [("", "(u + v - 1)//2")],
    9: [("", "2*(v//2) + 1")],
    10: [("m == 0", "2*q - 2"), ("1 <= m <= 2", "2*q - 1"), ("3 <= m <= 4", "2*q"), ("m == 5", "2*q + 1")],
    0: [("", "0")],
}
KAPPA = {  # region -> [(condition, value)], with R the lap number of (u, v)
    1: [("v % 2 == 1 or u <= -1", "-u - v"), ("v % 2 == 0 and u == 0", "-v - 1"), ("v % 2 == 0 and u == 1", "-v")],
    2: [("", "-u - v")],
    3: [("u % 2 == 0", "2*R - v"), ("u % 2 == 1 and v == 0", "2*R - 4"),
        ("u % 2 == 1 and v == -1", "2*R - 3"), ("u % 2 == 1 and v == 1", "2*R - 2")],
    4: [("", "4*R - 2 + u - v")],
    5: [("v % 2 == 0 and u == 0", "6*R - 5"), ("v % 2 == 0 and u == 1", "6*R - 4"),
        ("v % 2 == 0 and u == -1", "6*R - 3"), ("v % 2 == 1", "6*R - 1 + u")],
    6: [("", "8*R - 2 + u + v")],
    7: [("u % 2 == 1 and v == 0", "10*R - 4"), ("u % 2 == 1 and v == 1", "10*R - 3"),
        ("u % 2 == 1 and v == -1", "10*R - 2"), ("u % 2 == 0", "10*R + v")],
    8: [("", "12*R - u + v")],
    9: [("v % 2 == 0", "-v - 4"), ("v % 2 == 1", "-v - 2")],
    10: [("m <= 1", "11*R + 3*v - 3*q - 1"), ("2 <= m <= 3", "11*R + 3*v - 3*q - 2"), ("m >= 4", "11*R + 3*v - 3*q - 3")],
}
RHO = "abs(u) + abs(v)"
PI = [("u > 0 and v >= 0", "2*u"), ("u > 0 and v < 0", "2*u - 4*v"), ("u < 0 and v <= 0", "-6*u - 4*v"),
      ("u < 0 and v > 0", "8*v - 6*u"), ("u == 0 and v < 0", "-4*v"), ("u == 0 and v >= 0", "8*v")]
LO = [("R % 2 == 0", "-R - 1"), ("R % 2 == 1", "-R - 3")]
HI = [("R % 2 == 0", "half(25*R - 4)"), ("R % 2 == 1", "half(25*R + 1)")]
LEN = [("R % 2 == 0", "half(27*R - 2)"), ("R % 2 == 1", "half(27*R + 7)")]
START = [("R % 2 == 0", "quarter(27*R**2 - 22*R - 24)"), ("R % 2 == 1", "quarter(27*R**2 - 22*R - 33)")]   # Corollary 9
PAUX = {"h": "R//2", "k": "t//3"}                          # used in the rows of piece I
PIECES = [  # letter, name, first index (None: the piece is given in j), number of squares, rows
    ("A", "north row", None, None, [
        ("R % 2 == 0 and j == -R - 1", "0", "R"), ("R % 2 == 0 and j == -R", "1", "R"),
        ("R % 2 == 1 and j == -R - 3", "3", "R - 1"), ("R % 2 == 1 and j == -R - 2", "3", "R"),
        ("True", "-R - j", "R")]),
    ("B", "north-west staircase", "0", "2*R - 4", [("", "1 - R - (t + 1)//2", "R - 1 - t//2")]),
    ("C", "west corner", "2*R - 4", "6", [("t == %d" % i, a, b) for i, (a, b) in enumerate(
        [("3 - 2*R", "0"), ("3 - 2*R", "-1"), ("3 - 2*R", "1"), ("2 - 2*R", "1"), ("2 - 2*R", "0"), ("2 - 2*R", "-1")])]),
    ("D", "south-west staircase", "2*R + 2", "4*R - 7", [("", "2 - 2*R + (t + 1)//2", "-2 - t//2")]),
    ("E", "south corner", "6*R - 5", "6", [("t == %d" % i, a, b) for i, (a, b) in enumerate(
        [("0", "2 - 2*R"), ("1", "2 - 2*R"), ("-1", "2 - 2*R"), ("-1", "1 - 2*R"), ("0", "1 - 2*R"), ("1", "1 - 2*R")])]),
    ("F", "south-east staircase", "6*R + 1", "4*R - 5", [("", "2 + t//2", "1 - 2*R + (t + 1)//2")]),
    ("G", "east corner", "10*R - 4", "6", [("t == %d" % i, a, b) for i, (a, b) in enumerate(
        [("2*R - 1", "0"), ("2*R - 1", "1"), ("2*R - 1", "-1"), ("2*R", "-1"), ("2*R", "0"), ("2*R", "1")])]),
    ("H", "north-east staircase", "10*R + 2", "R + 1", [("", "2*R - (t + 1)//2", "2 + t//2")]),
    ("I", "return", "11*R + 3", None, [
        ("R % 2 == 0 and t == 3*k", "3*h - 3*k - 2", "h + k + 2"),
        ("R % 2 == 0 and t == 3*k + 1", "3*h - 3*k - 3", "h + k + 2"),
        ("R % 2 == 0 and t == 3*k + 2", "3*h - 3*k - 3", "h + k + 3"),
        ("R % 2 == 1 and t == 3*k", "3*h - 3*k - 1", "h + k + 2"),
        ("R % 2 == 1 and t == 3*k + 1", "3*h - 3*k - 1", "h + k + 3"),
        ("R % 2 == 1 and t == 3*k + 2", "3*h - 3*k - 2", "h + k + 3")]),
]

TERMS = {  # piece -> [(condition, the number of the square)]; Table 5 and the Lean table `term`
    "A": [("R % 2 == 0 and j == -R - 1", "(2*R - 1)**2 + 8*R"), ("R % 2 == 0 and j == -R", "(2*R + 1)**2 + 2"),
          ("R % 2 == 1 and j == -R - 3", "(2*R + 3)**2 + 6"), ("R % 2 == 1 and j == -R - 2", "(2*R + 5)**2 + 6"),
          ("R % 2 == 1 and j == -R - 1", "(2*R + 1)**2 + 2"), ("True", "(4*R + 2*j - 1)**2 + 14*R + 6*j")],
    "B": [("t % 2 == 0", "(4*R - 5)**2 + 14*R - t - 14"), ("t % 2 == 1", "(4*R - 3)**2 + 14*R - t - 7")],
    "C": [("t == %d" % i, e) for i, e in enumerate(
        ["(4*R - 7)**2 + 12*R - 18", "(4*R - 5)**2 + 12*R - 14", "(4*R - 5)**2 + 12*R - 10",
         "(4*R - 3)**2 + 12*R - 4", "(4*R - 5)**2 + 12*R - 12", "(4*R - 3)**2 + 12*R - 8"])],
    "D": [("t % 2 == 0", "(4*R - 1)**2 + 12*R - t - 4"), ("t % 2 == 1", "(4*R - 3)**2 + 12*R - t - 9")],
    "E": [("t == %d" % i, e) for i, e in enumerate(
        ["(4*R - 5)**2 + 8*R - 8", "(4*R - 3)**2 + 8*R - 6", "(4*R - 3)**2 + 8*R - 2",
         "(4*R - 1)**2 + 8*R + 2", "(4*R - 3)**2 + 8*R - 4", "(4*R - 1)**2 + 8*R - 2"])],
    "F": [("t % 2 == 0", "(4*R + 1)**2 + 8*R - t"), ("t % 2 == 1", "(4*R - 1)**2 + 8*R - t - 3")],
    "G": [("t == %d" % i, e) for i, e in enumerate(
        ["(4*R - 3)**2 + 4*R - 2", "(4*R - 1)**2 + 4*R - 2", "(4*R - 1)**2 + 4*R + 2",
         "(4*R + 1)**2 + 4*R + 4", "(4*R - 1)**2 + 4*R", "(4*R + 1)**2 + 4*R"])],
    "H": [("t % 2 == 0", "(4*R + 3)**2 + 4*R - t"), ("t % 2 == 1", "(4*R + 1)**2 + 4*R - t - 1")],
    "I": [("R % 2 == 0 and t == 3*k", "(4*R - 4*k - 1)**2 + 3*R - 6*k - 4"),
          ("R % 2 == 0 and t == 3*k + 1", "(4*R - 4*k - 3)**2 + 3*R - 6*k - 6"),
          ("R % 2 == 0 and t == 3*k + 2", "(4*R - 4*k - 1)**2 + 3*R - 6*k - 6"),
          ("R % 2 == 1 and t == 3*k", "(4*R - 4*k - 3)**2 + 3*R - 6*k - 5"),
          ("R % 2 == 1 and t == 3*k + 1", "(4*R - 4*k - 1)**2 + 3*R - 6*k - 5"),
          ("R % 2 == 1 and t == 3*k + 2", "(4*R - 4*k - 3)**2 + 3*R - 6*k - 7")],
}

# ----------------------------------------------------------------------------------------------
# Evaluating the formulas
# ----------------------------------------------------------------------------------------------
def half(x):
    assert x % 2 == 0, x
    return x // 2
def quarter(x):
    assert x % 4 == 0, x
    return x // 4
G = {"abs": abs, "half": half, "quarter": quarter, "__builtins__": {}}
_code = {}
def ev(expr, **env):
    c = _code.get(expr)
    if c is None: c = _code[expr] = compile(expr or "True", "<paper>", "eval")
    return eval(c, G, env)
def pick(rows, **env):
    """The value of the one row whose condition holds."""
    hit = [r for r in rows if ev(r[0], **env)]
    assert len(hit) == 1, (rows, env, hit)
    return hit[0]
def region(u, v):
    hit = [n for n, _, c in REGIONS if ev(c, u=u, v=v)]
    assert len(hit) == 1, (u, v, hit)
    return hit[0]
def aux(u, v): return {k: ev(e, u=u, v=v) for k, e in AUX.items()}
def lam(u, v):
    env = dict(u=u, v=v, **aux(u, v))
    return ev(pick(LAMBDA[region(u, v)], **env)[1], **env)
def kappa(u, v):
    env = dict(u=u, v=v, R=lam(u, v), **aux(u, v))
    return ev(pick(KAPPA[region(u, v)], **env)[1], **env)
def rho(u, v): return ev(RHO, u=u, v=v)
def pi(u, v): return ev(pick(PI, u=u, v=v)[1], u=u, v=v)
def lo(R): return ev(pick(LO, R=R)[1], R=R)
def hi(R): return ev(pick(HI, R=R)[1], R=R)
def start(R): return ev(pick(START, R=R)[1], R=R)       # the step at which lap R starts
def P(R, j):
    assert lo(R) <= j < hi(R), (R, j)
    starts = [None if s is None else ev(s, R=R) for _, _, s, _, _ in PIECES]
    i = max([n for n, s in enumerate(starts) if s is not None and s <= j], default=0)
    letter, _, start, count, rows = PIECES[i]
    if start is None:                                     # piece A: first row that applies
        env = dict(R=R, j=j)
        row = next(r for r in rows if ev(r[0], **env))
    else:
        t = j - starts[i]
        if count is not None: assert t < ev(count, R=R), (R, j)
        env = dict(R=R, j=j, t=t); env.update({k: ev(e, **env) for k, e in PAUX.items()})
        row = pick(rows, **env)
    return (ev(row[1], **env), ev(row[2], **env))
def term(R, j):                                           # Table 5: the number of the square P(R, j)
    assert lo(R) <= j < hi(R), (R, j)
    starts = [None if s is None else ev(s, R=R) for _, _, s, _, _ in PIECES]
    i = max([n for n, s in enumerate(starts) if s is not None and s <= j], default=0)
    rows = TERMS[PIECES[i][0]]
    if PIECES[i][2] is None:                              # piece A: first row that applies
        env = dict(R=R, j=j)
        row = next(r for r in rows if ev(r[0], **env))
    else:
        env = dict(R=R, j=j, t=j - starts[i]); env.update({k: ev(e, **env) for k, e in PAUX.items()})
        row = pick(rows, **env)
    return ev(row[1], **env)
def lean_terms():
    """The tables `term` and `backTerm` of PathStatement.lean, read from the Lean text."""
    text = open(os.path.join(os.path.dirname(LM.SRC), "..", "PathStatement.lean"), encoding="utf-8").read()
    ns = {}
    for name in ("backTerm", "term"):
        head, body = re.search(r"^def %s \((\w+) (\w+) : ℤ\) : ℤ :=\n(.*?)\n\n" % name, text, flags=re.S | re.M).group(0).split(":=\n", 1)
        args = re.search(r"\((\w+) (\w+) : ℤ\)", head).groups()
        body = re.sub(r"--[^\n]*", "", body)
        toks = re.findall(r"\bif\b|\bthen\b|\belse\b|[^\s]+", body)
        pos = [0]
        def expr():
            if toks[pos[0]] == "if":
                pos[0] += 1; c = []
                while toks[pos[0]] != "then": c.append(toks[pos[0]]); pos[0] += 1
                pos[0] += 1; a = expr(); assert toks[pos[0]] == "else"; pos[0] += 1; b = expr()
                return "((%s) if (%s) else (%s))" % (a, " ".join(c).replace(" = ", " == "), b)
            out = []
            while pos[0] < len(toks) and toks[pos[0]] not in ("if", "then", "else"): out.append(toks[pos[0]]); pos[0] += 1
            return " ".join(out)
        e = expr(); assert pos[0] == len(toks)
        e = e.replace("^", "**").replace(" / ", " // ").replace("backTerm R (j - (11 * R + 3))", "backTerm(R, j - (11 * R + 3))")
        exec("def %s(%s): return %s" % (name, ", ".join(args), e), ns)
    first = re.search(r"^def first \(R : ℤ\) : ℤ := (.*)$", text, flags=re.M).group(1)
    assert first == "-(R + 1 + 2 * (R % 2))", first
    return ns["term"]
def sigma(x, y):                                          # formula (1), as in Statement.lean
    r = max(abs(x), abs(y))
    if x == r and y > -r: return (2*r - 1)**2 + (y + r)
    if y == r: return (2*r - 1)**2 + 2*r + (r - x)
    if x == -r: return (2*r - 1)**2 + 4*r + (r - y)
    return (2*r - 1)**2 + 6*r + (x + r)
def sig(s): return sigma(s[0] + s[1], s[0] - s[1])       # spiral number of the square s = (u, v)
T = LM.PREFIX                                             # the first 80 squares
TPOS = {s: i for i, s in enumerate(T)}
STEPS = [(1, 0), (-1, 0), (0, 1), (0, -1), (2, 0), (-2, 0), (0, 2), (0, -2)]
def stamp(s):
    L = lam(*s)
    return (3, TPOS[s]) if L <= 3 else (L, kappa(*s))
def lo3(R): return 0 if R == 3 else lo(R)
def hi3(R): return 80 if R == 3 else hi(R)
def succ(s):                                              # the square s+ of Section 4
    L = lam(*s)
    if L <= 3:
        i = TPOS[s]
        return T[i + 1] if i < 79 else P(4, lo(4))
    j = kappa(*s)
    return P(L, j + 1) if j + 1 < hi(L) else P(L + 1, lo(L + 1))

# ----------------------------------------------------------------------------------------------
# Checks. Every one must pass before the page is written.
# ----------------------------------------------------------------------------------------------
REPORT = []
def check(name, ok):
    REPORT.append((name, ok)); print(("ok    " if ok else "FAIL  ") + name, flush=True)
    assert ok, name

def run_checks():
    box = [(u, v) for u in range(-BOX, BOX + 1) for v in range(-BOX, BOX + 1)]
    bad = 0; rbad = 0
    for u, v in box:
        L = lam(u, v)                                     # also asserts: exactly one region, one row
        if not (L <= rho(u, v) <= 2*L + 2 if L >= 4 else rho(u, v) <= 10): rbad += 1
        if L != LM.lapnum(u, v): bad += 1
        elif L >= 4 and kappa(u, v) != LM.pos(u, v): bad += 1
        elif rho(u, v) != LM.ring(u, v) or pi(u, v) != LM.rpos(u, v): bad += 1
        elif sig((u, v)) != (2*rho(u, v) - 1)**2 + pi(u, v): bad += 1
    check("Tables 2, 4 and the ring position equal the Lean definitions, and Lemma 1 holds, for |u|, |v| <= %d" % BOX, bad == 0)
    bad = 0
    for R in range(4, RMAX + 1):
        if lo(R) != LM.lo(R) or hi(R) != LM.hi(R): bad += 1
        if hi(R) - lo(R) != ev(pick(LEN, R=R)[1], R=R): bad += 1
        sq = [P(R, j) for j in range(lo(R), hi(R))]
        if sq != [(LM.squ(R, j), LM.sqv(R, j)) for j in range(lo(R), hi(R))]: bad += 1
    check("Table 1, lo, hi and the lap length equal the Lean definitions for laps 4..%d" % RMAX, bad == 0)
    bad = 0
    for R in range(4, RMAX + 2):                          # the remarks of Section 8
        sq = [P(R, j) for j in range(lo(R), hi(R))]
        rr = [rho(*s) for s in sq]
        if (min(rr), max(rr)) != (R, 2*R + 2): bad += 1
        st = {letter: ev(start, R=R) for letter, _, start, _, _ in PIECES if start is not None}
        for letter, nxt, low in (("B", "C", 2*R - 2), ("D", "E", 2*R - 1), ("F", "G", 2*R), ("H", "I", 2*R + 1)):
            if {rho(*P(R, j)) for j in range(st[letter], st[nxt])} != {low, low + 1}: bad += 1
        if any(s[1] != R for s in sq[2 + 2*(R % 2):sq.index(P(R, 0))]): bad += 1
        nxt = P(R + 1, lo(R + 1))
        if (nxt[0] - sq[-1][0], nxt[1] - sq[-1][1]) not in STEPS: bad += 1
    check("Section 3: the rings of lap R and of its staircases, for laps 4..%d, and R <= ring <= 2R + 2 for the "
          "lap number R of every square with |u|, |v| <= %d" % (RMAX + 1, BOX), bad == 0 and rbad == 0)
    order = [(letter, start) for letter, _, start, _, _ in PIECES if start is not None]
    want = dict(zip("ABCDEFGHI", (1, 2, 3, 4, 5, 6, 7, 8, 10))); bad = 0
    for R in range(4, MAPMAX + 1):
        st = [(letter, ev(start, R=R)) for letter, start in order]
        for j in range(lo(R), hi(R)):
            letter = "A" if j < 0 else [l for l, a in st if a <= j][-1]
            if region(*P(R, j)) != (9 if R % 2 == 1 and j < lo(R) + 2 else want[letter]): bad += 1
    check("Section 4: regions 1 to 8 hold the pieces A to H, region 10 holds piece I, and region 9 the first two "
          "squares of an odd lap, for laps 4..%d" % MAPMAX, bad == 0)
    W = list(T); R = 4; starts = {}
    while len(W) < SIM:
        starts[R] = len(W); W += [P(R, j) for j in range(lo(R), hi(R))]; R += 1
    walkf_xy = walkf.run(SIM)
    S = [((x + y)//2, (x - y)//2) for x, y in walkf_xy]
    check("the 80 squares followed by the laps equal a simulation of the walk for %d steps" % SIM, W[:SIM] == S)
    check("laps 4 to 9 start at steps 80, 133, 204, 284, 382, 489",
          [starts[r] for r in range(4, 10)] == [80, 133, 204, 284, 382, 489])
    n = 80; bad = 0
    for r in range(4, SMAX + 1):
        if start(r) != n: bad += 1
        n += hi(r) - lo(r)
    LT = lean_terms(); bad = 0
    for R in range(4, RMAX + 1):
        for j in range(lo(R), hi(R)):
            if not (term(R, j) == sig(P(R, j)) == LT(R, j)): bad += 1
    R = 4; sbad = 0
    for n in range(80, SIM):
        while start(R + 1) <= n: R += 1
        if term(R, lo(R) + n - start(R)) != sigma(*walkf_xy[n]): sbad += 1
    check("Table 5 gives the number of every square of Table 1 and equals the Lean table `term` (PathStatement.lean) "
          "for laps 4..%d, and it gives the terms of a simulation of the rule for steps 80..%d" % (RMAX, SIM - 1),
          bad == 0 and sbad == 0)
    lean_start = "def start (R : ℤ) : ℤ := (27 * R ^ 2 - 22 * R - 24 - 9 * (R % 2)) / 4"
    src = open(os.path.join(os.path.dirname(LM.SRC), "..", "PathStatement.lean"), encoding="utf-8").read()
    check("Corollary 9: the Lean definition of start (PathStatement.lean) is the formula of the paper, for laps 4..%d" % SMAX,
          lean_start in src and all((27*r*r - 22*r - 24 - 9*(r % 2))//4 == start(r) for r in range(4, SMAX + 1)))
    check("Corollary 9: start(R) is 80 plus the lengths of the laps 4..R-1 for R = 4..%d, and it is the step at which "
          "lap R starts in the simulated walk for the %d laps inside %d steps" % (SMAX, len(starts), SIM),
          bad == 0 and all(start(r) == a for r, a in starts.items()))
    bad = 0
    for u in range(-LBOX, LBOX + 1):
        for v in range(-LBOX, LBOX + 1):
            s = (u, v); L = lam(u, v); st = stamp(s)
            if L <= 3:
                if s not in TPOS: bad += 1
            else:
                if s in TPOS: bad += 1
                j = kappa(u, v)
                if not (lo(L) <= j < hi(L) and P(L, j) == s): bad += 1          # Lemma 3
            n = succ(s); a, b = st
            want = (a, b + 1) if b + 1 < hi3(a) else (a + 1, lo3(a + 1))
            if (n[0] - u, n[1] - v) not in STEPS or stamp(n) != want: bad += 1     # Lemma 5
            for e in STEPS:                                                         # Lemma 6
                q = (u + e[0], v + e[1])
                if stamp(q) > st and sig(n) > sig(q): bad += 1
    check("Lemmas 2, 3, 5 and 6, as worded in the paper, hold for all squares with |u|, |v| <= %d" % LBOX, bad == 0)
    # The spiral by construction: from (0,0) go 1 right, 1 up, 2 left, 2 down, 3 right, 3 up, ...
    x = y = 0; dx, dy = 1, 0; leg = 1; done = 0; seen = set(); bad = 0
    for k in range(1, NSPIRAL + 1):
        seen.add((x, y))
        if sigma(x, y) != k or k % 2 != (x + y + 1) % 2: bad += 1
        x += dx; y += dy; done += 1
        if done == leg:
            done = 0; dx, dy = -dy, dx                    # turn left
            if dy == 0: leg += 1                          # the legs grow after every second turn
    check("formula (1) gives the numbers 1..%d of the squares along the spiral, which are all squares with "
          "|x|, |y| <= %d, and Lemma 7 holds for them" % (NSPIRAL, SBOX),
          bad == 0 and seen == {(a, b) for a in range(-SBOX, SBOX + 1) for b in range(-SBOX, SBOX + 1)})
    check("the squares one move from square 1 have the numbers 3, 5, 7, 9, 13, 17, 21, 25",
          sorted(sigma(a, b) for a in (-2, -1, 1, 2) for b in (-a, a)) == [3, 5, 7, 9, 13, 17, 21, 25])
    check("the example after Lemma 3: (-5, -2) has lap number 4 and index 11, and P_4(11) = (-5, -2)",
          lam(-5, -2) == 4 and kappa(-5, -2) == 11 and P(4, 11) == (-5, -2) and region(-5, -2) == 4)
    check("the first terms are 1, 3, 7, 19, 5, 9, 11, 15, 33, 13, 29, 53",
          [sig(s) for s in W[:12]] == [1, 3, 7, 19, 5, 9, 11, 15, 33, 13, 29, 53])
    return W

# ----------------------------------------------------------------------------------------------
# Printing the formulas as TeX
# ----------------------------------------------------------------------------------------------
ATOM, MUL, ADD, CMP, BOOL = 5, 4, 3, 2, 1
CMPOP = {ast.Eq: "=", ast.NotEq: r"\ne", ast.Lt: "<", ast.LtE: r"\le", ast.Gt: ">", ast.GtE: r"\ge"}
def _t(n):
    if isinstance(n, ast.Constant):
        return (r"\text{otherwise}", BOOL) if n.value is True else (str(n.value), ATOM)
    if isinstance(n, ast.Name): return (n.id, ATOM)
    if isinstance(n, ast.Call):
        (a, _), = [_t(x) for x in n.args]
        return ("|%s|" % a, ATOM) if n.func.id == "abs" else ("(%s)/%d" % (a, {"half": 2, "quarter": 4}[n.func.id]), MUL)
    if isinstance(n, ast.UnaryOp):
        a, p = _t(n.operand)
        return ("-" + (a if p >= MUL else "(%s)" % a), ADD)
    if isinstance(n, ast.BinOp):
        a, pa = _t(n.left); b, pb = _t(n.right)
        if isinstance(n.op, (ast.Add, ast.Sub)):
            minus = isinstance(n.op, ast.Sub)
            if isinstance(n.right, ast.UnaryOp) or (minus and pb <= ADD): b = "(%s)" % b
            return ("%s %s %s" % (a, "-" if minus else "+", b), ADD)
        if isinstance(n.op, ast.Mult):
            if isinstance(n.left, ast.UnaryOp) and isinstance(n.left.operand, ast.Constant):   # -6*u is (-6)*u
                return ("-%s%s" % (n.left.operand.value, b if pb >= MUL else "(%s)" % b), ADD)
            if pa < MUL: a = "(%s)" % a
            if pb < MUL: b = "(%s)" % b
            tight = isinstance(n.left, ast.Constant) and not isinstance(n.right, ast.Constant)
            return ((a + b) if tight else (a + r" \cdot " + b), MUL)
        if isinstance(n.op, ast.Pow):
            assert pb == ATOM
            return ("%s^%s" % (a if pa == ATOM else "(%s)" % a, b), ATOM)
        if isinstance(n.op, ast.FloorDiv):
            if pa < ATOM: a = "(%s)" % a
            return (r"\lfloor %s/%s \rfloor" % (a, b), ATOM)
        if isinstance(n.op, ast.Mod):
            if pa < ATOM: a = "(%s)" % a
            return (r"%s \bmod %s" % (a, b), MUL)
    if isinstance(n, ast.Compare):
        if (len(n.ops) == 1 and isinstance(n.ops[0], ast.Eq) and isinstance(n.left, ast.BinOp)
                and isinstance(n.left.op, ast.Mod) and _t(n.left.right)[0] == "2"):
            return (r"%s \text{ %s}" % (_t(n.left.left)[0], "even" if _t(n.comparators[0])[0] == "0" else "odd"), CMP)
        out = _t(n.left)[0]
        for op, c in zip(n.ops, n.comparators): out += " %s %s" % (CMPOP[type(op)], _t(c)[0])
        return (out, CMP)
    if isinstance(n, ast.BoolOp):
        sep = r",\ " if isinstance(n.op, ast.And) else r" \text{ or } "
        return (sep.join(_t(x)[0] for x in n.values), BOOL)
    raise ValueError(ast.dump(n))
def tex(expr): return html.escape(_t(ast.parse(expr, mode="eval").body)[0], quote=False)
def m(expr): return r"\(%s\)" % tex(expr)                 # inline math from an expression
def cond(c): return m(c) if c else ""

def table(head, rows, cls=""):
    out = ['<div class="tablewrap"><table class="%s"><thead><tr>' % cls]
    out += ["<th>%s</th>" % h for h in head]
    out.append("</tr></thead><tbody>")
    for r in rows:
        if r is None: out.append('<tr class="gap"><td colspan="%d"></td></tr>' % len(head)); continue
        out.append("<tr>" + "".join("<td>%s</td>" % c for c in r) + "</tr>")
    out.append("</tbody></table></div>")
    return "\n".join(out)

def table_path():
    rows = []
    def par(c): return r"even \(R\), " if "% 2 == 0" in c else r"odd \(R\), " if "% 2 == 1" in c else ""
    def strip(c): return c.replace("R % 2 == 0 and ", "").replace("R % 2 == 1 and ", "")
    def sq(a, b): return r"\((%s,\ %s)\)" % (tex(a), tex(b))
    for letter, name, start, count, cases in PIECES:
        label = "%s. %s" % (letter, name.capitalize())
        if start is None:                                 # piece A, given in j
            for i, (c, a, b) in enumerate(cases):
                idx = (par(c) + m(strip(c))) if c != "True" else r"all other \(j\) with \(\mathrm{lo}(R) \le j &lt; 0\)"
                rows.append([label if i == 0 else "", idx, sq(a, b)])
        elif cases[0][0].startswith("t == 0"):            # a corner: six squares
            idx = r"\(j = %s + t\), \(t = 0, \dots, 5\)" % tex(start)
            sqs = [r"(%s,\,%s)" % (tex(a), tex(b)) for _, a, b in cases]      # the comma is inside the formula,
            rows.append([label, idx, " ".join(r"\(%s%s\)" % (q, "," if i < len(sqs) - 1 else "")   # so no line starts with one
                                              for i, q in enumerate(sqs))])
        elif len(cases) == 1:                             # a staircase
            idx = (r"\(j = t\), \(0 \le t &lt; %s\)" % tex(count)) if start == "0" else \
                  (r"\(j = %s + t\), \(0 \le t &lt; %s\)" % (tex(start), tex(count)))
            rows.append([label, idx, sq(cases[0][1], cases[0][2])])
        else:                                             # the return, up to the end of the lap
            rows.append([label, r"\(j = %s + t &lt; \mathrm{hi}(R)\), \(t \ge 0\)" % tex(start), ""])
            for c, a, b in cases:
                rows.append(["", par(c) + m(strip(c)), sq(a, b)])
        rows.append(None)
    return table(["Piece", r"Index \(j\)", r"Square \(P_R(j)\)"], rows[:-1], "path")

def table_terms():
    rows = []
    def par(c): return r"even \(R\), " if "R % 2 == 0" in c else r"odd \(R\), " if "R % 2 == 1" in c else ""
    def strip(c): return c.replace("R % 2 == 0 and ", "").replace("R % 2 == 1 and ", "")
    for letter, name, start, count, _ in PIECES:
        label = "%s. %s" % (letter, name.capitalize())
        cases = TERMS[letter]
        if start is None:                                 # piece A, given in j
            for i, (c, e) in enumerate(cases):
                idx = (par(c) + m(strip(c))) if c != "True" else r"all other \(j &lt; 0\)"
                rows.append([label if i == 0 else "", idx, m(e)])
        elif letter == "I":
            rows.append([label, r"\(j = %s + t\)" % tex(start), ""])
            for c, e in cases: rows.append(["", par(c) + m(strip(c)), m(e)])
        else:                                             # a staircase or a corner
            for i, (c, e) in enumerate(cases):
                pre = (r"\(j = t\), " if start == "0" else r"\(j = %s + t\), " % tex(start)) if i == 0 else ""
                rows.append([label if i == 0 else "", pre + m(c), m(e)])
        rows.append(None)
    return table(["Piece", r"Index \(j\)", "Term"], rows[:-1], "terms")

def table_lambda():
    rows = []
    for n, name, c in REGIONS:
        for i, (c2, val) in enumerate(LAMBDA[n]):
            rows.append([("%d. %s" % (n, name.capitalize()) if n else "Centre") if i == 0 else "", m(c) if i == 0 else "",
                         cond(c2), m(val)])
    return table(["Region", r"Squares \((u, v)\)", "Case", r"\(\lambda(u, v)\)"], rows, "reg")

def table_kappa():
    rows = []
    for n, name, c in REGIONS:
        if n == 0: continue
        for i, (c2, val) in enumerate(KAPPA[n]):
            rows.append(["%d. %s" % (n, name.capitalize()) if i == 0 else "", cond(c2), m(val)])
        rows.append(None)
    return table(["Region", "Case", r"\(\kappa(u, v)\)"], rows[:-1], "reg")

def cases_tex(rows):
    return r"\begin{cases} " + r" \\ ".join(r"%s &amp; \text{if } %s" % (tex(v), tex(c)) for c, v in rows) + r" \end{cases}"

def table_prefix():
    cells = [r"\((%d,\,%d)\)" % s for s in T]
    out = ['<div class="tablewrap"><table class="prefix"><thead><tr><th>\\(i\\)</th>'
           '<th colspan="8">\\(T_i,\\ T_{i+1},\\ \\dots,\\ T_{i+7}\\)</th></tr></thead><tbody>']
    for i in range(0, 80, 8):
        out.append("<tr><td>%d</td>" % i + "".join("<td>%s</td>" % c for c in cells[i:i + 8]) + "</tr>")
    out.append("</tbody></table></div>")
    return "\n".join(out)

# ----------------------------------------------------------------------------------------------
# Figures (inline SVG, drawn from the same functions)
# ----------------------------------------------------------------------------------------------
def fig_spiral():
    n, c = 3, 44; w = (2*n + 1)*c + 2
    out = ['<svg viewBox="0 0 %d %d" role="img" aria-label="The square spiral with the numbers 1 to 49">' % (w, w)]
    near = {(a, b) for a in (-2, -1, 1, 2) for b in (-a, a)}
    for y in range(n, -n - 1, -1):
        for x in range(-n, n + 1):
            px, py = 1 + (x + n)*c, 1 + (n - y)*c
            cls = "cell" + (" on" if (x + y) % 2 == 0 else "") + (" near" if (x, y) in near else "") + (" home" if (x, y) == (0, 0) else "")
            out.append('<rect class="%s" x="%d" y="%d" width="%d" height="%d"/>' % (cls, px, py, c, c))
            out.append('<text class="num" x="%d" y="%d">%d</text>' % (px + c//2, py + c//2 + 5, sigma(x, y)))
    for (x, y) in sorted(near) + [(0, 0)]:
        px, py = 1 + (x + n)*c, 1 + (n - y)*c
        out.append('<rect class="%s" x="%d" y="%d" width="%d" height="%d"/>' % ("ring home" if (x, y) == (0, 0) else "ring", px + 2, py + 2, c - 4, c - 4))
    out.append("</svg>")
    return "\n".join(out)

def fig_lambda():
    n, c, pad = 9, 26, 36; w = (2*n + 1)*c + pad + 4
    out = ['<svg viewBox="0 0 %d %d" role="img" aria-label="The lap number of every square with |u| and |v| at most 9">' % (w, w)]
    for v in range(n, -n - 1, -1):
        for u in range(-n, n + 1):
            L = lam(u, v); px, py = pad + (u + n)*c, 2 + (n - v)*c
            cls = "cell " + ("pre" if L <= 3 else "even" if L % 2 == 0 else "odd")
            out.append('<rect class="%s" x="%d" y="%d" width="%d" height="%d"/>' % (cls, px, py, c, c))
            if L >= 4:    # below 4 the value is not a lap number: those squares get the tint only
                out.append('<text class="num small" x="%d" y="%d">%d</text>' % (px + c//2, py + c//2 + 4, L))
    for k in range(-n, n + 1, 3):
        out.append('<text class="tick" x="%d" y="%d">%d</text>' % (pad + (k + n)*c + c//2, 2 + (2*n + 1)*c + 16, k))
        out.append('<text class="tick" x="%d" y="%d" text-anchor="end">%d</text>' % (pad - 10, 2 + (n - k)*c + c//2 + 4, k))
    px, py = pad + n*c, 2 + n*c
    out.append('<rect class="ring home" x="%d" y="%d" width="%d" height="%d"/>' % (px + 1, py + 1, c - 2, c - 2))
    out.append("</svg>")
    return "\n".join(out)

def lap_layout(W, R):
    """Lap R for a picture: its squares, the squares before it, and where the piece letters go."""
    lapsq = [P(R, j) for j in range(lo(R), hi(R))]
    before = W[:W.index(lapsq[0])]
    starts = [ev(s, R=R) if s is not None else lo(R) for _, _, s, _, _ in PIECES] + [hi(R)]
    labels = []
    for i, (letter, _, _, _, _) in enumerate(PIECES):
        sq = [P(R, j) for j in range(starts[i], starts[i + 1])]
        mu = sum(a for a, _ in sq)/len(sq); mv = sum(b for _, b in sq)/len(sq)
        d = (mu*mu + mv*mv) ** .5
        lu, lv = mu + 1.5*mu/d, mv + 1.5*mv/d
        if letter == "A": lu, lv = mu - 1.0, mv + 1.1
        if letter == "I": lu, lv = mu + 1.2, mv + 1.4
        labels.append((letter, lu, lv))
    return lapsq, before, labels, (-2*R - 1, 2*R + 3, -2*R - 1, R + 3)

def fig_lap(W, R=6):
    lapsq, before, labels, (u0, u1, v0, v1) = lap_layout(W, R)
    c = 22
    X = lambda u: 14 + (u - u0)*c; Y = lambda v: 14 + (v1 - v)*c
    w, h = X(u1) + 14, Y(v0) + 14
    out = ['<svg viewBox="0 0 %d %d" role="img" aria-label="Lap %d of the walk">' % (w, h, R)]
    out.append('<line class="axis" x1="%d" y1="%d" x2="%d" y2="%d"/>' % (X(u0), Y(0), X(u1), Y(0)))
    out.append('<line class="axis" x1="%d" y1="%d" x2="%d" y2="%d"/>' % (X(0), Y(v0), X(0), Y(v1)))
    out.append('<text class="tick ax" x="%d" y="%d">u</text>' % (X(u1) + 2, Y(0) + 14))
    out.append('<text class="tick ax" x="%d" y="%d">v</text>' % (X(0) + 10, Y(v1) + 4))
    for s in before: out.append('<circle class="old" cx="%d" cy="%d" r="2.4"/>' % (X(s[0]), Y(s[1])))
    out.append('<polyline class="path" points="%s"/>' % " ".join("%d,%d" % (X(a), Y(b)) for a, b in lapsq))
    for s in lapsq: out.append('<circle class="dot" cx="%d" cy="%d" r="3"/>' % (X(s[0]), Y(s[1])))
    a, b = lapsq[0]; out.append('<circle class="start" cx="%d" cy="%d" r="5.5"/>' % (X(a), Y(b)))
    a, b = lapsq[-1]; out.append('<circle class="end" cx="%d" cy="%d" r="5.5"/>' % (X(a), Y(b)))
    for letter, lu, lv in labels:
        out.append('<text class="piece" x="%.1f" y="%.1f">%s</text>' % (X(lu), Y(lv) + 5, letter))
    out.append("</svg>")
    return "\n".join(out)

# ----------------------------------------------------------------------------------------------
# The same three figures as TikZ pictures, for the LaTeX version. Square (x, y) is the unit cell
# with lower left corner (x, y).
# ----------------------------------------------------------------------------------------------
def tikz_spiral():
    n = 3
    near = {(a, b) for a in (-2, -1, 1, 2) for b in (-a, a)}
    cells = [(x, y) for y in range(n, -n - 1, -1) for x in range(-n, n + 1)]
    out = [r"\begin{tikzpicture}[x=8.4mm,y=8.4mm]"]
    out += [r"\fill[tintA] (%d,%d) rectangle +(1,1);" % c for c in cells if sum(c) % 2 == 0]
    out.append(r"\draw[hair,step=1] (%d,%d) grid (%d,%d);" % (-n, -n, n + 1, n + 1))
    out += [r"\node at (%.1f,%.1f) {%d};" % (x + .5, y + .5, sigma(x, y)) for x, y in cells]
    out += [r"\draw[line width=0.9pt] (%.2f,%.2f) rectangle +(0.84,0.84);" % (x + .08, y + .08) for x, y in sorted(near)]
    out.append(r"\draw[accent,line width=1.3pt] (0.08,0.08) rectangle +(0.84,0.84);")
    out.append(r"\end{tikzpicture}")
    return "\n".join(out)

def tikz_lambda():
    n = 9
    cells = [(u, v) for v in range(n, -n - 1, -1) for u in range(-n, n + 1)]
    out = [r"\begin{tikzpicture}[x=6.4mm,y=6.4mm,every node/.style={font=\footnotesize,inner sep=0pt}]"]
    for u, v in cells:
        L = lam(u, v)
        out.append(r"\fill[%s] (%d,%d) rectangle +(1,1);" % ("tintO" if L <= 3 else "tintA" if L % 2 == 0 else "tintB", u, v))
    out.append(r"\draw[hair,step=1] (%d,%d) grid (%d,%d);" % (-n, -n, n + 1, n + 1))
    out += [r"\node at (%.1f,%.1f) {%d};" % (u + .5, v + .5, lam(u, v)) for u, v in cells if lam(u, v) >= 4]
    for k in range(-n, n + 1, 3):
        out.append(r"\node[anchor=north] at (%.1f,%.2f) {$%d$};" % (k + .5, -n - .35, k))
        out.append(r"\node[anchor=east] at (%.2f,%.1f) {$%d$};" % (-n - .35, k + .5, k))
    out.append(r"\draw[accent,line width=1.3pt] (0.06,0.06) rectangle +(0.88,0.88);")
    out.append(r"\end{tikzpicture}")
    return "\n".join(out)

def tikz_lap(W, R=6):
    lapsq, before, labels, (u0, u1, v0, v1) = lap_layout(W, R)
    out = [r"\begin{tikzpicture}[x=3.3mm,y=3.3mm]"]     # small enough to share a page with Table 1
    out.append(r"\draw[hair] (%d,0) -- (%d,0) node[below,text=black,font=\small] {$u$};" % (u0, u1))
    out.append(r"\draw[hair] (0,%d) -- (0,%d) node[right,text=black,font=\small] {$v$};" % (v0, v1))
    out += [r"\fill[old] (%d,%d) circle[radius=0.11];" % s for s in before]
    pts = ["(%d,%d)" % s for s in lapsq]
    out.append(r"\draw[accent,line width=0.7pt,line join=round]")
    out += ["  " + " -- ".join(pts[i:i + 10]) + (" --" if i + 10 < len(pts) else ";") for i in range(0, len(pts), 10)]
    out += [r"\fill[accent] (%d,%d) circle[radius=0.14];" % s for s in lapsq]
    out.append(r"\fill[black] (%d,%d) circle[radius=0.27];" % lapsq[0])
    out.append(r"\draw[black,line width=0.9pt,fill=white] (%d,%d) circle[radius=0.25];" % lapsq[-1])
    out += [r"\node[font=\bfseries\itshape] at (%.2f,%.2f) {%s};" % (lu, lv, letter) for letter, lu, lv in labels]
    out.append(r"\end{tikzpicture}")
    return "\n".join(out)

# ----------------------------------------------------------------------------------------------
def statement_listing():
    s = open(os.path.join(ROOT, "lean", "Statement.lean"), encoding="utf-8").read()
    a = s.index("/-- The number of the square"); b = s.index("/-- The picture on the OEIS page")
    c = s.index("/-- The Falafel (Fers + Alfil)"); d = s.index("end Falafel")
    return html.escape(s[a:b].rstrip("\n") + "\n\n" + s[c:d].rstrip("\n"))

def fill_template(page, fill):
    for k, v in fill.items():
        assert "@@%s@@" % k in page, k
        page = page.replace("@@%s@@" % k, v)
    left = re.findall(r"@@\w+@@", page)
    assert not left, left
    return page

def main():
    W = run_checks()
    fill = {
        "TABLE_PATH": table_path(), "TABLE_LAMBDA": table_lambda(), "TABLE_KAPPA": table_kappa(),
        "TABLE_PREFIX": table_prefix(), "TABLE_TERMS": table_terms(),
        "PI_CASES": cases_tex(PI), "RHO": tex(RHO),
        "LO_CASES": cases_tex(LO), "HI_CASES": cases_tex(HI), "LEN_CASES": cases_tex(LEN),
        "AUX_Q": tex(AUX["q"]), "AUX_M": tex(AUX["m"]), "PAUX_H": tex(PAUX["h"]), "PAUX_K": tex(PAUX["k"]),
        "FIG_SPIRAL": fig_spiral(), "FIG_LAMBDA": fig_lambda(), "FIG_LAP": fig_lap(W),
        "LEAN_STATEMENT": statement_listing(),
        "BOX": str(BOX), "RMAX": str(RMAX), "SIM": "{:,}".format(SIM), "LBOX": str(LBOX),
        "NSPIRAL": "{:,}".format(NSPIRAL), "SMAX": str(SMAX),
        "START_CASES": cases_tex(START), "FIRST_TERMS": ", ".join(str(sig(s)) for s in T),
    }
    template = open(os.path.join(HERE, "paper.template.html"), encoding="utf-8").read()
    page = fill_template(template, fill)
    open(os.path.join(HERE, "falafel-paper.html"), "w", encoding="utf-8").write(page)
    print("wrote falafel-paper.html, %d bytes, %d checks passed" % (len(page.encode()), len(REPORT)))

    # The LaTeX version: the same filled template, with TikZ pictures in place of the SVG ones.
    figures = {"spiral": tikz_spiral(), "lambda": tikz_lambda(), "lap": tikz_lap(W)}
    fill_tex = dict(fill, FIG_SPIRAL='<tikz name="spiral"></tikz>', FIG_LAMBDA='<tikz name="lambda"></tikz>',
                    FIG_LAP='<tikz name="lap"></tikz>')
    longest = max(len(line) for line in html.unescape(fill["LEAN_STATEMENT"]).split("\n"))
    listing_pt = min(8.0, int(10 * TEXTWIDTH_PT / (MONO_ADVANCE * longest)) / 10)   # the longest line just fits
    src, numbers = to_latex.convert(fill_template(template, fill_tex), figures, listing_pt)
    def formulas(text):                                   # every \( .. \) and \[ .. \], in order
        return [re.sub(r"\s+", " ", f[2:-2]).strip() for f in to_latex.MATH.findall(text)]
    in_page = formulas(html.unescape(page[page.index("<article>"):]))
    in_tex = formulas(src.replace(r"\begin{equation}", r"\[").replace(r"\end{equation}", r"\]"))
    check("the LaTeX source has the %d formulas of the page, unchanged and in the same order" % len(in_page),
          in_page == in_tex)
    open(os.path.join(HERE, "falafel-paper.tex"), "w", encoding="utf-8").write(src)
    print("wrote falafel-paper.tex, %d bytes; numbered items: %s" % (len(src.encode()), numbers))
    if "--no-pdf" in sys.argv: return
    if not shutil.which("tectonic"):
        print("tectonic is not installed: falafel-paper.pdf was not made"); return
    subprocess.run(["tectonic", "--keep-logs", "falafel-paper.tex"], cwd=HERE, check=True)
    log = open(os.path.join(HERE, "falafel-paper.log"), encoding="utf-8", errors="replace").read()
    bad = [l for l in log.split("\n") if "Missing character" in l or l.startswith("Overfull")
           or l.startswith(r"Underfull \vbox") or "undefined" in l.lower()]
    for l in bad: print("LOG  " + l)
    if not bad: os.remove(os.path.join(HERE, "falafel-paper.log"))
    print("wrote falafel-paper.pdf, %d bytes, %d log lines to look at" % (os.path.getsize(os.path.join(HERE, "falafel-paper.pdf")), len(bad)))

if __name__ == "__main__":
    main()
