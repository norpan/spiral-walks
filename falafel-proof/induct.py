# Machine checks for the Falafel proof, in (u,v) coordinates (u=(x+y)/2, v=(x-y)/2).
# (1) Rule check: with "visited" DEFINED by the closed formula (initial 80 squares, then laps 4,5,...),
#     every step of every lap goes to the lowest-numbered unvisited neighbour.
# (2) Invariance check: the local picture at a step (which of the 8 neighbours are visited, and the order of
#     their numbers) depends only on the step's address: parity of R, stretch, phase, and its distances to the
#     two ends of the stretch when these are below C.
import sys
from lapcheck import lap
from walkf import run
NB=[(1,0),(-1,0),(0,1),(0,-1),(2,0),(-2,0),(0,2),(0,-2)]
def key(q):                       # spiral order in (u,v): ring, then position along the ring
    u,v=q; r=abs(u)+abs(v)
    if r==0: return (0,0)
    if u>0 and v>=0: pos=u
    elif u>=0 and v<0: pos=r-v     # v<0: from (r-1,-1) pos r+1 to (0,-r) pos 2r
    elif u<0 and v<=0: pos=2*r-u   # from (-1,-r+1) pos 2r+1 to (-r,0) pos 3r
    else: pos=3*r+v                # u<=0, v>0: from (-r+1,1) pos 3r+1 to (0,r) pos 4r
    return (r,pos)
def stretches(R):
    west = R-2 if R%2==0 else R
    nd = 3*R//2-5 if R%2==0 else (3*R-5)//2
    return [3,west,2*(R-2),6,4*R-7,6,4*R-5,6,R+1,nd]
if __name__=="__main__":
    Rmax=int(sys.argv[1]); C=int(sys.argv[2]); R0=int(sys.argv[3])
    init=run(80); uv0=[((x+y)//2,(x-y)//2) for x,y in init]
    T={}; t=0
    for q in uv0: T[q]=t; t+=1
    assert uv0[-1]==lap(4)[0], (uv0[-1],lap(4)[0])
    paths={}
    for R in range(4,Rmax+1):
        s,m=lap(R); assert T.get(s)==t-1, R       # each lap starts on the last square visited so far
        q=s; P=[s]
        for du,dv in m:
            q=(q[0]+du,q[1]+dv); assert q not in T, ("revisit",R,q); T[q]=t; t+=1; P.append(q)
        paths[R]=P
    print("laps 4..%d built from the formula: %d squares, all distinct"%(Rmax,t))
    table={}; bad=0; checked=0
    for R in range(4,Rmax-3):
        P=paths[R]; L=stretches(R); assert sum(L)==len(P)-1
        k=0
        for sid,n in enumerate(L):
            for i in range(n):
                p=P[k]; nxt=P[k+1]; tp=T[p]
                flags=tuple(1 if (T.get((p[0]+a,p[1]+b),10**18)<=tp) else 0 for a,b in NB)
                ks=[key((p[0]+a,p[1]+b)) for a,b in NB]
                order=tuple(sorted(range(8),key=lambda j:ks[j]))
                free=[j for j in order if not flags[j]]
                choice=NB[free[0]] if free else None
                if choice!=(nxt[0]-p[0],nxt[1]-p[1]): bad+=1
                checked+=1
                if R>=R0:
                    addr=(R%2,sid,min(i,C),min(n-1-i,C),i%6)
                    st=(flags,order)
                    table.setdefault(addr,set()).add(st)
                k+=1
    print("rule check: %d steps checked (laps 4..%d), %d violations"%(checked,Rmax-4,bad))
    multi=[a for a,s in table.items() if len(s)>1]
    print("invariance check for R>=%d with C=%d: %d addresses, %d of them with more than one local picture"%(R0,C,len(table),len(multi)))
    for a in sorted(multi)[:12]: print("  ambiguous address",a,len(table[a]))
