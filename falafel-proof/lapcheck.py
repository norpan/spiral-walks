# Checks the closed-form description of the Falafel's laps against the simulated walk.
import sys
from walkf import run            # run(N) -> list of (x,y)
def alt(a,b,n): return [a if i%2==0 else b for i in range(n)]
W6=[(0,-2),(0,-1),(0,2),(-1,0),(0,-1),(0,-1)]
S6=[(2,0),(1,0),(-2,0),(0,-1),(1,0),(1,0)]
E6=[(0,2),(0,1),(0,-2),(1,0),(0,1),(0,1)]
def lap(R):
    """start square and moves of the lap that fills the row v=R (in u,v coordinates)"""
    if R%2==0:
        start=(2,R); pole=[(-2,0),(1,0),(-2,0)]; west=R-2
        d=[(-2,0),(-1,0),(0,1)]; nd=3*R//2-5
    else:
        start=(4,R-1); pole=[(-1,0),(0,1),(-2,0)]; west=R
        d=[(-2,0),(0,1),(-1,0)]; nd=(3*R-5)//2
    m = pole + [(-1,0)]*west + alt((0,-1),(-1,0),2*(R-2)) + W6 + alt((0,-1),(1,0),4*R-7) + S6 \
        + alt((1,0),(0,1),4*R-5) + E6 + alt((0,1),(-1,0),R+1) + [d[i%3] for i in range(nd)]
    return start,m
if __name__=="__main__":
    N=int(sys.argv[1]); P=run(N)
    uv=[((x+y)//2,(x-y)//2) for x,y in P]; idx={q:i for i,q in enumerate(uv)}
    good=[]; bad=[]
    R=4
    while True:
        s,m=lap(R)
        if s not in idx or idx[s]+len(m)>=len(uv): break
        i=idx[s]; q=s; ok=True
        for k,(du,dv) in enumerate(m):
            q=(q[0]+du,q[1]+dv)
            if uv[i+k+1]!=q: ok=False; break
        (good if ok else bad).append(R); R+=1
    print("laps tested: R = 4 ..",R-1)
    print("laps that do NOT follow the formula:",bad[:40], "..." if len(bad)>40 else "")
    if good:
        # longest run of consecutive good laps at the end
        r0=good[-1]
        while r0-1 in good: r0-=1
        s0,_=lap(r0); s1,m1=lap(good[-1])
        print("formula holds for every lap from R =",r0,"to R =",good[-1],": steps",idx[s0]+1,"to",idx[s1]+len(m1)+1)
        # chaining: each lap ends where the next begins
        chain=all((lambda s,m:(s[0]+sum(a for a,b in m),s[1]+sum(b for a,b in m)))(*lap(r))==lap(r+1)[0] for r in range(r0,good[-1]))
        print("each lap ends on the start square of the next:",chain)
