import sys
def spiral(x,y):
    r=max(abs(x),abs(y))
    if r==0: return 1
    b=(2*r-1)**2
    if x==r and y>-r: return b+(y+r)
    if y==r: return b+2*r+(r-x)
    if x==-r: return b+4*r+(r-y)
    return b+6*r+(x+r)
MV=[(a*sx,a*sy) for a in (1,2) for sx in (1,-1) for sy in (1,-1)]
def walk(N):
    x=y=0; vis={(0,0)}; path=[(0,0)]
    for n in range(N-1):
        c=[(spiral(x+dx,y+dy),x+dx,y+dy) for dx,dy in MV if (x+dx,y+dy) not in vis]
        if not c: print("TRAPPED",n+1); break
        s,x,y=min(c); vis.add((x,y)); path.append((x,y))
    return path
if __name__=="__main__":
    N=int(sys.argv[1]); p=walk(N)
    print([spiral(x,y) for x,y in p[:70]])
    R=int(sys.argv[2]); order={q:i+1 for i,q in enumerate(p)}
    for y in range(R,-R-1,-1):
        print(''.join('%4s'%(order.get((x,y),'.') if (x+y)%2==0 else '') for x in range(-R,R+1)))
