import sys
from sim import spiral, MV
def run(N):
    x=y=0; vis={(0,0)}; P=[(0,0)]
    for n in range(N-1):
        best=None
        for dx,dy in MV:
            q=(x+dx,y+dy)
            if q in vis: continue
            s=spiral(*q)
            if best is None or s<best[0]: best=(s,q)
        if best is None: print("TRAPPED at",n+1); break
        x,y=best[1]; vis.add((x,y)); P.append((x,y))
    return P
