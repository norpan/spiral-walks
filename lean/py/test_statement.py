# Python mirror of ../Statement.lean, written from the Lean text, and checked against OEIS A399160.
OEIS = [1, 3, 7, 19, 5, 9, 11, 15, 33, 13, 29, 53, 25, 27, 47, 23, 45, 21, 41, 69, 17, 35, 39, 67, 37, 63, 97,
        61, 95, 31, 55, 59, 93, 57, 89, 129, 87, 127, 51, 49, 79, 117, 77, 115, 43, 71, 75, 113, 73, 109, 153,
        107, 151, 105, 149, 65, 99, 103, 147, 101, 143, 193, 141, 191, 139, 189, 137, 187, 91, 131]  # DATA, fetched 23 Nov 2026
def spiral(p):
    x, y = p
    r = max(abs(x), abs(y))
    if x == r and y > -r: return (2*r - 1)**2 + (y + r)
    elif y == r: return (2*r - 1)**2 + 2*r + (r - x)
    elif x == -r: return (2*r - 1)**2 + 4*r + (r - y)
    else: return (2*r - 1)**2 + 6*r + (x + r)
def is_move(p, q): return abs(q[0]-p[0]) == abs(q[1]-p[1]) and abs(q[0]-p[0]) in (1, 2)
grid = [[spiral((x, y)) for x in (-2,-1,0,1,2)] for y in (2,1,0,-1,-2)]
print("OEIS picture:", grid == [[17,16,15,14,13],[18,5,4,3,12],[19,6,1,2,11],[20,7,8,9,10],[21,22,23,24,25]])
B = 60
num = {spiral((x, y)): (x, y) for x in range(-B, B+1) for y in range(-B, B+1)}
print("spiral is a bijection from |x|,|y| <= %d onto 1..%d:" % (B, (2*B+1)**2), sorted(num) == list(range(1, (2*B+1)**2 + 1)))
print("consecutive numbers are side by side:", all(abs(num[k][0]-num[k+1][0]) + abs(num[k][1]-num[k+1][1]) == 1 for k in range(1, (2*B+1)**2)))
mv = sorted((dx, dy) for dx in range(-3, 4) for dy in range(-3, 4) if is_move((0, 0), (dx, dy)))
print("IsMove gives the 8 moves:", mv == sorted([(1,1),(1,-1),(-1,1),(-1,-1),(2,2),(2,-2),(-2,2),(-2,-2)]))
def greedy(N):
    a = [(0, 0)]; vis = {(0, 0)}
    while len(a) < N:
        p = a[-1]
        c = [(p[0]+dx, p[1]+dy) for dx, dy in mv if (p[0]+dx, p[1]+dy) not in vis]
        if not c: print("TRAPPED"); break
        q = min(c, key=spiral); a.append(q); vis.add(q)
    return a
a = greedy(3000)
print("first 70 terms of the greedy walk equal the OEIS DATA:", [spiral(p) for p in a[:70]] == OEIS)
def is_walk_prefix(a):          # IsWalk, for the finite piece a[0..len-1]
    if a[0] != (0, 0): return "start"
    if len(set(a)) != len(a): return "injective"
    for n in range(len(a) - 1):
        if not is_move(a[n], a[n+1]): return ("move", n)
        for d in mv:
            q = (a[n][0]+d[0], a[n][1]+d[1])
            if spiral(q) < spiral(a[n+1]) and q not in a[:n+1]: return ("lowest", n)
    return True
print("the greedy walk satisfies IsWalk on 3000 terms:", is_walk_prefix(a))
bad = 0
for n in range(0, 400):
    for d in mv:
        q = (a[n][0]+d[0], a[n][1]+d[1])
        if q != a[n+1] and is_walk_prefix(a[:n+1] + [q]) is True: bad += 1
print("deviations from the greedy walk accepted by IsWalk (should be 0):", bad)
print("every visited square has x + y even:", all((x + y) % 2 == 0 for x, y in a))   # the third claim, VisitsExactlyEvenSquares
t = [spiral(p) for p in a]; ts = set(t)                # the fourth claim, PermutationOfOddNumbers
print("the 3000 terms are odd, positive and distinct:", all(k > 0 and k % 2 == 1 for k in t) and len(ts) == len(t))
print("smallest odd number not among the first 3000 terms:", next(k for k in range(1, 10**7, 2) if k not in ts))
