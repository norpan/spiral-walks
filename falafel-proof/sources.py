# Source-table check for the Falafel proof. For every step of every lap R (R0 <= R <= Rmax-4) and each of
# the 8 neighbours q of the square the step leaves, find which lap and stretch visits q (its "source") and
# test that, within one address class, the source is always the same stretch of the lap R-d with the same d,
# and sits at a fixed offset from the start of that stretch, or a fixed offset from its end, or a fixed
# offset from the current step's own index (allowed only if both stretches grow by the same amount per 12 laps).
import sys
from lapcheck import lap
from walkf import run
from induct import NB, stretches
Rmax=int(sys.argv[1]); C=int(sys.argv[2]); R0=int(sys.argv[3])
init=run(80); src={}
for x,y in init: src[((x+y)//2,(x-y)//2)]=('init',)
paths={}
for R in range(4,Rmax+1):
    s,m=lap(R); L=stretches(R); q=s; P=[s]; k=0
    for sid,n in enumerate(L):
        for i in range(n):
            du,dv=m[k]; q=(q[0]+du,q[1]+dv); assert q not in src; src[q]=(R,sid,i,n); P.append(q); k+=1
    paths[R]=P
grow=lambda sid,R:[b-a for a,b in zip(stretches(R),stretches(R+12))][sid]
tab={}; nsteps=0
for R in range(R0,Rmax-3):
    P=paths[R]; L=stretches(R); k=0
    for sid,n in enumerate(L):
        for i in range(n):
            p=P[k]; addr=(R%2,sid,min(i,C),min(n-1-i,C),i%6); nsteps+=1
            for j,(a,b) in enumerate(NB):
                q=(p[0]+a,p[1]+b); s=src.get(q)
                assert s is not None and s[0]!='init', ("no source",R,sid,i,q,s)
                r,sid2,i2,n2=s
                e=tab.setdefault((addr,j),[set(),set(),set(),set()])
                e[0].add((R-r,sid2)); e[1].add(i2); e[2].add(n2-i2)
                e[3].add(i2-i if grow(sid,R)==grow(sid2,r) else None)
            k+=1
bad=[]; forms={'start':0,'end':0,'same offset':0}
for key,e in tab.items():
    if len(e[0])!=1: bad.append((key,'source stretch varies',sorted(e[0])[:4])); continue
    if len(e[1])==1: forms['start']+=1
    elif len(e[2])==1: forms['end']+=1
    elif len(e[3])==1 and None not in e[3]: forms['same offset']+=1
    else: bad.append((key,'offset varies',sorted(e[1])[:4],sorted(e[2])[:4]))
ds=sorted({d for e in tab.values() for d,_ in e[0]})
print("steps examined:",nsteps,"(laps %d..%d); address/neighbour pairs: %d; unstable: %d"%(R0,Rmax-4,len(tab),len(bad)))
print("source anchored at the start of its stretch / at the end / at a fixed offset from the current step:",forms)
print("lap differences d that occur (source lap = R-d):",ds)
for b in bad[:10]: print("  UNSTABLE",b)
