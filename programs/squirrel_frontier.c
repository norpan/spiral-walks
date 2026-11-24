// squirrel_frontier.c -- OEIS A399315, frontier-only version.
// Squirrel (all 16 squares at Chebyshev distance 2) on the square spiral, always moving to the
// lowest-numbered unvisited square. Same walk and same reports as squirrel_search.c, but memory grows
// with the perimeter of the visited region instead of its area (about 72*sqrt(n) bytes: 143 MB at 4e12).
//
// Build:   cc -O2 -o squirrel_frontier squirrel_frontier.c
// Run:     ./squirrel_frontier                 run until Ctrl-C (or until the Squirrel is trapped)
//          ./squirrel_frontier N               stop after N terms
//          ./squirrel_frontier --resume [N]    continue from the checkpoint file squirrel.ckpt
// Options: --thr K     report every square with <= K unvisited neighbours on arrival (default 2)
//          --gap G     report every visit that leaves an unvisited square G or more rings further in on
//                      the same line, with a board picture (default 3)
//          --every M   write a checkpoint and a STATUS block every M steps (default 1e11)
//          --fresh     start from the beginning even if squirrel.ckpt exists (it will be overwritten)
//          --log FILE  log file, appended to (default frontier.txt; "-" for none)
//          --events K  print a board picture for the first K kinds of outer-before-inner event (default 300)
// Everything it prints is also appended to the log file, so no tee is needed.
// The large tables (kinds of few-free squares, kinds of events, moves, height differences) are written to
// stats.txt, which is rewritten in full at every checkpoint and when the program stops.
// Smoothness statistics (squares at least 8 from a corner; counted from the step named in the summary):
//   height of a line = its lowest unvisited ring. After each visit the program records how much the visited
//   line's height differs from the lines 1 and 2 away (on every 8th step, to keep it cheap).
//   deep hole = an unvisited square left 2 or more rings behind a visit on its own line. While one is open
//   the program follows its pit depth = how far ALL five lines around it (its own included) are visited
//   beyond it. A trap on that line needs pit depth 2 or more; reaching 2 is logged with a board picture.
// Statistics added in version 4 (counted from the step named in stats.txt):
//   gap = how many rings further in the lowest unvisited square of the visited line lies; every gap of 1 or
//   more is counted. Kinds: for every arrival with at most 4 unvisited neighbours, and for every
//   outer-before-inner event, the move that led there and which neighbours were unvisited, counted exactly.
//   For each event, how many steps ago the later of the two squares clockwise of the inner square was visited
//   (the event is repaired exactly when both are visited). Pairs of consecutive moves, on every 8th step.
//   At every STATUS: the rings the boundary spans and the unvisited squares that lie below a visited one.
// Ctrl-C finishes the current step, writes the checkpoint, prints the summary and exits.
//
// How it stores the board. Every square lies on exactly one "line": a row or column of one side of the
// spiral, running straight outward (side = right/top/left/bottom as in the numbering, position t along the
// side, ring r outward). Per line it keeps `base` = the lowest unvisited ring on that line, and a 64-bit
// window of visited flags for rings base..base+63. Everything below base is visited by construction, so
// the walk is reproduced exactly. If a square were ever left 64 rings behind a visit on its own line, the
// program checks whether it can still be reached: if not (all 16 neighbours visited) it reports it as
// skipped forever and carries on; otherwise it stops with a message, because the window is too small.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <signal.h>
#include <stdarg.h>
#include <stddef.h>
#include <time.h>
typedef long long ll;
#define LIKELY(x)   __builtin_expect(!!(x),1)
#define UNLIKELY(x) __builtin_expect(!!(x),0)
#define COLD __attribute__((noinline,cold))
enum { RIGHT=0, TOP=1, LEFT=2, BOTTOM=3 };
typedef struct { uint64_t win; int32_t base; int32_t pad; } Ray;
static Ray *side[4]; static ll T;
static ll maxdepth=0, ndead=0, deadlow=-1, lastd=0;
static int mdx[16], mdy[16];
static volatile sig_atomic_t stopflag=0;
static void onsig(int sig){ (void)sig; stopflag=1; }
#define CKPT "squirrel.ckpt"
static FILE *logf;   // everything printed is also appended to the log file
COLD static void out(const char *fmt, ...){ va_list ap; va_start(ap,fmt); vprintf(fmt,ap); va_end(ap);
    if(logf){ va_start(ap,fmt); vfprintf(logf,fmt,ap); va_end(ap); } }
COLD static void prog(const char *fmt, ...){ va_list ap; va_start(ap,fmt); vfprintf(stderr,fmt,ap); va_end(ap);
    if(logf){ va_start(ap,fmt); vfprintf(logf,fmt,ap); va_end(ap); } }

static inline __attribute__((always_inline)) ll spiral(ll x, ll y){
    ll ax = x<0?-x:x, ay = y<0?-y:y; ll r = ax>ay?ax:ay;
    if(r==0) return 1;
    ll base=(2*r-1)*(2*r-1);
    if(x==r && y>-r) return base+(y+r);
    if(y==r) return base+2*r+(r-x);
    if(x==-r) return base+4*r+(r-y);
    return base+6*r+(x+r);
}
static inline __attribute__((always_inline)) void classify(ll x, ll y, int *s, ll *t, ll *r){
    ll ax=x<0?-x:x, ay=y<0?-y:y; ll rr=ax>ay?ax:ay; *r=rr;
    if(x==rr && y>-rr){ *s=RIGHT; *t=y; }
    else if(y==rr){ *s=TOP; *t=x; }
    else if(x==-rr){ *s=LEFT; *t=y; }
    else { *s=BOTTOM; *t=x; }
}
static inline __attribute__((always_inline)) void xy_of(int s, ll t, ll r, ll *x, ll *y){
    switch(s){ case RIGHT: *x=r; *y=t; break; case TOP: *x=t; *y=r; break;
               case LEFT: *x=-r; *y=t; break; default: *x=t; *y=-r; }
}
static inline __attribute__((always_inline)) ll outmin(int s, ll t){   // lowest ring on line (s,t)
    if(s==RIGHT || s==BOTTOM) return t>0 ? t : -t+1;
    return t>=0 ? t+1 : -t;
}
COLD static void alloc_sides(ll newT){
    for(int s=0;s<4;s++){
        Ray *a=malloc((size_t)(2*newT+1)*sizeof(Ray));
        if(!a){ fprintf(stderr,"out of memory\n"); exit(1); }
        for(ll t=-newT;t<=newT;t++){ a[t+newT].win=0; a[t+newT].base=(int32_t)outmin(s,t); a[t+newT].pad=0; }
        if(side[s]){ memcpy(a+(newT-T), side[s], (size_t)(2*T+1)*sizeof(Ray)); free(side[s]); }
        side[s]=a;
    }
    T=newT;
}
static inline __attribute__((always_inline)) int getray(const Ray *R, ll r){
    ll d = r - R->base;
    if(d<0) return 1;
    if(d>=64) return 0;
    return (int)((R->win>>d)&1);
}
static inline __attribute__((always_inline)) int get(ll x, ll y){
    int s; ll t,r; classify(x,y,&s,&t,&r);
    if(r==0) return 1;
    return getray(&side[s][t+T], r);
}
// visited flags of rings o-2..o+2 on one line, bit i <-> ring o-2+i
static inline __attribute__((always_inline)) unsigned ray5(const Ray *R, ll o){
    ll d = (o-2) - R->base;
    if(d>=0){ if(d>=64) return 0; return (unsigned)(R->win>>d)&31u; }
    if(d<=-5) return 31u;
    int k=(int)(-d);
    return (unsigned)(((R->win<<k)|((1ull<<k)-1))&31u);
}
static inline __attribute__((always_inline)) void slide(Ray *R){
    if(LIKELY(R->win&1)){ uint64_t inv=~R->win;
        if(UNLIKELY(inv==0)){ R->base+=64; R->win=0; }
        else { int tz=__builtin_ctzll(inv); R->base+=tz; R->win>>=tz; } }
}
COLD static void skipped(ll hx, ll hy){
    ll sn=spiral(hx,hy);
    out("\nSKIPPED FOREVER: square %lld at (%lld,%lld) is unvisited and all 16 of its neighbours are visited\n",sn,hx,hy);
    ndead++; if(deadlow<0||sn<deadlow) deadlow=sn;
}
COLD static ll overflow(int s, ll t, Ray *R, ll r){
    // the lowest unvisited square of this line is >= 64 rings below the square being visited
    for(;;){
        ll d = r - R->base;
        if(d<64) return d;
        ll hx,hy; xy_of(s,t,R->base,&hx,&hy);
        int freen=0; for(int k=0;k<16;k++) if(!get(hx+mdx[k],hy+mdy[k])) freen++;
        if(freen>0){
            out("\nWINDOW OVERFLOW: square %lld at (%lld,%lld) is still unvisited, has %d unvisited neighbours, and lies %lld rings inside a visit on its own line. Stopping: this needs the full-board program.\n",
                   spiral(hx,hy),hx,hy,freen,d);
            exit(2);
        }
        skipped(hx,hy);
        R->win|=1; slide(R);   // it can never be entered or looked at again, so it may be passed over
    }
}
static inline __attribute__((always_inline)) void setray(int s, ll t, Ray *R, ll r){
    ll d = r - R->base;
    if(UNLIKELY(d>=64)) d=overflow(s,t,R,r);
    if(d>maxdepth) maxdepth=d;
    lastd=d;
    R->win |= 1ull<<d;
    slide(R);
}
static inline __attribute__((always_inline)) ll cl(ll v, ll lo, ll hi){ return v<lo?lo:(v>hi?hi:v); }
static inline __attribute__((always_inline)) void psi(ll x, ll y, ll *px, ll *py){
    ll ax=llabs(x), ay=llabs(y), r=ax>ay?ax:ay;
    if(x==r && y>-r){ *px=r-2; *py=cl(y,-r+3,r-2); }
    else if(y==r){ *px=cl(x,-r+2,r-3); *py=r-2; }
    else if(x==-r){ *px=-r+2; *py=cl(y,-r+2,r-3); }
    else { *px=cl(x,-r+3,r-2); *py=-r+2; }
}
static double now(void){ struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t); return t.tv_sec+t.tv_nsec*1e-9; }

// The 16 neighbours as a bit mask of UNVISITED squares, bit 0 = lowest spiral number.
// m[j] = ray5 of line t-2+j. rev: the spiral number decreases with t on this side (top, left).
static const unsigned char KJ[16]={0,1,2,3,4, 0,4, 0,4, 0,4, 0,1,2,3,4};
static const unsigned char KB[16]={0,0,0,0,0, 1,1, 2,2, 3,3, 4,4,4,4,4};
static inline __attribute__((always_inline,unused)) unsigned nbmask(const unsigned *m, int rev){
    unsigned lo,l1,mid,h1,hi;
    if(rev){ lo=~m[4]; l1=~m[3]; mid=~m[2]; h1=~m[1]; hi=~m[0]; }
    else   { lo=~m[0]; l1=~m[1]; mid=~m[2]; h1=~m[3]; hi=~m[4]; }
    return (lo&1) | (l1&1)<<1 | (mid&1)<<2 | (h1&1)<<3 | (hi&1)<<4
         | ((lo>>1)&1)<<5 | ((hi>>1)&1)<<6 | ((lo>>2)&1)<<7 | ((hi>>2)&1)<<8 | ((lo>>3)&1)<<9 | ((hi>>3)&1)<<10
         | ((lo>>4)&1)<<11 | ((l1>>4)&1)<<12 | ((mid>>4)&1)<<13 | ((h1>>4)&1)<<14 | ((hi>>4)&1)<<15;
}

// Faster form used by the inner loop: the unvisited neighbours as a 25-bit mask over the 5x5 block,
// bit 5*(ring offset+2) + position (position 0 = lowest number), restricted to the 16 squares on its edge.
// K16 gives the bit number of the same square in the 16-bit mask above, K25 the other way.
static uint32_t SP[32], PERIM; static int K16[25], K25[16];
static void init25(void){
    for(unsigned v=0;v<32;v++){ SP[v]=0; for(int i=0;i<5;i++) if((v>>i)&1) SP[v]|=1u<<(5*i); }
    PERIM=0; for(int k=0;k<16;k++){ int b=5*KB[k]+KJ[k]; K25[k]=b; PERIM|=1u<<b; }
    for(int b=0;b<25;b++){ K16[b]=-1; for(int k=0;k<16;k++) if(K25[k]==b) K16[b]=k; }
}
static inline __attribute__((always_inline)) unsigned mask25(const unsigned *m, int rev){
    unsigned v;
    if(rev) v = SP[~m[4]&31] | SP[~m[3]&31]<<1 | SP[~m[2]&31]<<2 | SP[~m[1]&31]<<3 | SP[~m[0]&31]<<4;
    else    v = SP[~m[0]&31] | SP[~m[1]&31]<<1 | SP[~m[2]&31]<<2 | SP[~m[3]&31]<<3 | SP[~m[4]&31]<<4;
    return v & PERIM;
}
static inline unsigned m16(unsigned m){   // the 25-bit mask as the 16-bit mask
    return (m&31) | ((m>>5)&1)<<5 | ((m>>9)&1)<<6 | ((m>>10)&1)<<7 | ((m>>14)&1)<<8 | ((m>>15)&1)<<9 | ((m>>19)&1)<<10 | ((m>>20)&31)<<11;
}

#define RB 64
#define HN 16384
typedef struct {
    char magic[8]; ll version;
    ll n, x, y, T;
    ll viol, unrep, hist[17];
    ll pend, ppx, ppy, follow;
    ll rbx[RB], rby[RB];
    ll maxdepth, ndead, deadlow, thr;
    double elapsed;
    ll gapcount[16];      // added in checkpoint version 2: visits by gap depth (index capped at 15)
    ll from3;             // added in version 3: step from which the smoothness statistics below are counted
    ll adj1[81], adj2[81]; // |height difference| between the visited line and the two lines 1 away / 2 away (each capped at 8), index 9*a+b
    ll holes, pithist[8], maxpit;   // deep holes closed so far, by deepest pit reached (<=0 in [0], capped at 7)
    ll nact, act[4][5];   // deep holes still open: side, t, ring, deepest pit so far, logged
    ll nkind, kcount[40]; char kname[40][88];   // kinds of few-free squares: where it came from and which squares were free
    ll from4;             // added in version 4: step from which the statistics below are counted
    ll lastk, prevk;      // the last two moves as bit numbers of the neighbour mask (-1: made within 8 of a corner)
    ll evage[65];         // events by steps since the later of the two squares clockwise of the inner square was visited (64: longer ago)
    ll evcorner, evpics;  // events within 8 of a corner (not classified by kind); event pictures printed so far
    ll mv2[256];          // pairs of consecutive moves, sampled on every 8th step
    ll hused, hover;      // kinds table: entries in use, arrivals not counted because it was full
    ll hcnt[HN]; uint32_t hkey[HN];   // key = 1 + (event?1<<20:0) + (move<<16) + mask of unvisited neighbours
} State;
#define V1SIZE offsetof(State,gapcount)
#define V2SIZE offsetof(State,from3)
#define V3SIZE offsetof(State,from4)
static State S;
// count one arrival of this kind; returns 1 if the kind is new
static inline int hcount(uint32_t key){
    uint32_t h=(key*2654435761u)>>18;
    for(;;){
        uint32_t kk=S.hkey[h];
        if(kk==key){ S.hcnt[h]++; return 0; }
        if(!kk){ if(S.hused>=HN/4*3){ S.hover++; return 0; } S.hkey[h]=key; S.hcnt[h]=1; S.hused++; return 1; }
        h=(h+1)&(HN-1);
    }
}

COLD static void save_ckpt(void){
    FILE *f=fopen(CKPT ".tmp","wb");
    if(!f){ fprintf(stderr,"warning: cannot write checkpoint\n"); return; }
    memcpy(S.magic,"SQFRONT",8); S.version=4; S.T=T; S.maxdepth=maxdepth; S.ndead=ndead; S.deadlow=deadlow;
    int ok = fwrite(&S,sizeof S,1,f)==1;
    for(int s=0;s<4 && ok;s++) ok = fwrite(side[s],sizeof(Ray),(size_t)(2*T+1),f)==(size_t)(2*T+1);
    ok = (fclose(f)==0) && ok;
    if(!ok){ fprintf(stderr,"warning: checkpoint write failed (disk full?)\n"); remove(CKPT ".tmp"); return; }
    rename(CKPT ".tmp", CKPT);
}
COLD static int load_ckpt(void){
    FILE *f=fopen(CKPT,"rb"); if(!f) return 0;
    memset(&S,0,sizeof S);
    if(fread(&S,V1SIZE,1,f)!=1 || memcmp(S.magic,"SQFRONT",8)!=0 || S.version<1 || S.version>4){ fclose(f); fprintf(stderr,"%s is not a valid checkpoint\n",CKPT); exit(1); }
    if(S.version>=2 && fread((char*)&S+V1SIZE,V2SIZE-V1SIZE,1,f)!=1){ fclose(f); fprintf(stderr,"%s is truncated\n",CKPT); exit(1); }
    if(S.version>=3 && fread((char*)&S+V2SIZE,V3SIZE-V2SIZE,1,f)!=1){ fclose(f); fprintf(stderr,"%s is truncated\n",CKPT); exit(1); }
    if(S.version>=4 && fread((char*)&S+V3SIZE,sizeof S-V3SIZE,1,f)!=1){ fclose(f); fprintf(stderr,"%s is truncated\n",CKPT); exit(1); }
    if(S.version<3){ S.from3=S.n; S.maxpit=-99; }     // older checkpoint: the smoothness statistics start here
    if(S.version<4){ S.from4=S.n; S.lastk=S.prevk=-1; S.gapcount[1]=S.gapcount[2]=0; }   // and the version 4 statistics here
    T=0; alloc_sides(S.T);
    for(int s=0;s<4;s++) if(fread(side[s],sizeof(Ray),(size_t)(2*T+1),f)!=(size_t)(2*T+1)){ fprintf(stderr,"%s is truncated\n",CKPT); exit(1); }
    fclose(f);
    maxdepth=S.maxdepth; ndead=S.ndead; deadlow=S.deadlow;
    return 1;
}
// lowest unvisited number, and squares that can no longer be visited
COLD static void summary(int trapped){
    out("outer-before-inner events: %lld ; not repaired on the next move: %lld\n",S.viol,S.unrep);
    out("free neighbours on arrival:"); for(int i=0;i<=16;i++) out(" %d:%lld",i,S.hist[i]); out("\n");
    ll low=-1,lx=0,ly=0, maxring=0, nholes=0, holes[16]; memset(holes,0,sizeof holes);
    for(int ss=0;ss<4;ss++) for(ll tt=-T;tt<=T;tt++){
        Ray *R=&side[ss][tt+T];
        if(!R->win && R->base>outmin(ss,tt) && R->base-1>maxring) maxring=R->base-1;
        if(R->win){   // unvisited squares below the outermost visited one on this line
            int top=63-__builtin_clzll(R->win);
            if(R->base+top>maxring) maxring=R->base+top;
            for(int k=0;k<top;k++) if(!((R->win>>k)&1)){
                nholes++; holes[top-k>15?15:top-k]++;
                ll qx,qy; xy_of(ss,tt,R->base+k,&qx,&qy);
                ll ddx=llabs(qx-S.x), ddy=llabs(qy-S.y);
                if(!trapped && (ddx>ddy?ddx:ddy)==2) continue;      // the Squirrel can still step onto it
                int freen=0; for(int q=0;q<16;q++) if(!get(qx+mdx[q],qy+mdy[q])) freen++;
                if(freen==0){ skipped(qx,qy); R->win|=1ull<<k; }
            }
            slide(R);
        }
        ll hx,hy; xy_of(ss,tt,R->base,&hx,&hy); ll sn=spiral(hx,hy);
        if(low<0||sn<low){ low=sn; lx=hx; ly=hy; }
    }
    out("lowest unvisited number: %lld at (%lld,%lld)%s\n",low,lx,ly, ndead? "" : "  => every number below it has appeared");
    out("squares skipped forever: %lld",ndead); if(ndead) out(" (lowest %lld)",deadlow); out("\n");
    out("deepest gap behind a visit on one line: %lld rings (window holds 64)\n",maxdepth);
    out("visits leaving a gap of 3 or more rings (counted since this was added):");
    { int any=0; for(int i=3;i<16;i++) if(S.gapcount[i]){ out(" %d%s:%lld",i,i==15?"+":"",S.gapcount[i]); any=1; } if(!any) out(" none"); out("\n"); }
    out("visits leaving a gap of 1 or 2 rings (counted since step %lld): 1:%lld 2:%lld\n",S.from4,S.gapcount[1],S.gapcount[2]);
    { ll lr=llabs(lx)>llabs(ly)?llabs(lx):llabs(ly);
      out("boundary now: lowest unvisited ring %lld, highest visited ring %lld; unvisited squares below a visited square of their line: %lld",lr,maxring,nholes);
      if(nholes){ out(" (by rings below the outermost visited one:"); for(int i=1;i<16;i++) if(holes[i]) out(" %d%s:%lld",i,i==15?"+":"",holes[i]); out(")"); }
      out("\n"); }
    out("kinds since step %lld: %lld kinds of square with at most 4 free moves or of event, %lld events near a corner not classified, %lld arrivals lost to a full table; tables in stats.txt\n",S.from4,S.hused,S.evcorner,S.hover);
    out("smoothness since step %lld, squares at least 8 from a corner (height = lowest unvisited ring of a line; sampled on every 8th step):\n",S.from3);
    for(int w=1;w<=2;w++){ const ll *J = w==1?S.adj1:S.adj2; ll mg[9]; int m=0;
        for(int i=0;i<9;i++){ mg[i]=0; for(int j=0;j<9;j++) mg[i]+=J[i*9+j]+J[j*9+i]; if(mg[i]) m=i; }
        out("  height difference to the lines %d away:",w); for(int i=0;i<=m;i++) out(" %d%s:%lld",i,i==8?"+":"",mg[i]); out("\n"); }
    out("squares with at most %lld free neighbours, by kind (counted since step %lld; positions are (rings out, squares clockwise) from the square):",S.thr,S.from3);
    out(S.nkind?"\n":" none\n");
    { int idx[40]; for(int i=0;i<S.nkind;i++) idx[i]=i;      // most frequent first
      for(int i=1;i<S.nkind;i++){ int v=idx[i], j=i; while(j>0 && S.kcount[idx[j-1]]<S.kcount[v]){ idx[j]=idx[j-1]; j--; } idx[j]=v; }
      for(int i=0;i<S.nkind;i++) out("  %lld x  %s\n",S.kcount[idx[i]],S.kname[idx[i]]); }
    out("  deep holes closed: %lld; by deepest pit reached (a trap needs 2):",S.holes);
    { int any=0; for(int i=0;i<8;i++) if(S.pithist[i]){ out(" %s%d%s:%lld",i==0?"<=":"",i,i==7?"+":"",S.pithist[i]); any=1; } if(!any) out(" none"); out("\n"); }
}

// stats.txt: the large tables, rewritten in full
static int cmpkind(const void *a, const void *b){
    int i=*(const int*)a, j=*(const int*)b; uint32_t ki=S.hkey[i]-1, kj=S.hkey[j]-1;
    int ti=ki>>20, tj=kj>>20; if(ti!=tj) return ti-tj;
    if(!ti){ int fi=__builtin_popcount(ki&0xffff), fj=__builtin_popcount(kj&0xffff); if(fi!=fj) return fi-fj; }
    return S.hcnt[i]<S.hcnt[j] ? 1 : (S.hcnt[i]>S.hcnt[j] ? -1 : (ki<kj?-1:1));
}
COLD static void write_stats(void){
    FILE *f=fopen("stats.txt.tmp","w"); if(!f) return;
    static int idx[HN]; int nk=0; for(int i=0;i<HN;i++) if(S.hkey[i]) idx[nk++]=i;
    qsort(idx,(size_t)nk,sizeof idx[0],cmpkind);
    fprintf(f,"A399315 Squirrel, statistics after %lld steps (this file is rewritten at every checkpoint)\n",S.n);
    fprintf(f,"Offsets are (rings out, squares clockwise) from the square. Kinds cover squares at least 8 from a corner.\n");
    fprintf(f,"Counted since step %lld unless a line says otherwise.\n\n",S.from4);
    fprintf(f,"GAPS: visits by how many rings further in the lowest unvisited square of the same line lies\n ");
    for(int i=1;i<16;i++) if(S.gapcount[i]) fprintf(f," %d%s:%lld",i,i==15?"+":"",S.gapcount[i]);
    fprintf(f,"   (3 and more: counted since gap logging began)\n\n");
    fprintf(f,"SQUARES WITH AT MOST 4 FREE MOVES ON ARRIVAL, by where the Squirrel came from and which squares were free\n");
    fprintf(f,"  free         count  came from  free squares\n");
    for(int q=0;q<nk;q++){ uint32_t key=S.hkey[idx[q]]-1; if(key>>20) continue; int k=(key>>16)&15; unsigned m=key&0xffff;
        fprintf(f,"  %4d %13lld  (%d,%d)%s ",__builtin_popcount(m),S.hcnt[idx[q]],2-KB[k],KJ[k]-2,(2-KB[k]==2&&KJ[k]-2==-2)?"*":" ");
        for(int o=2;o>=-2;o--) for(int c=2;c>=-2;c--) for(int b=0;b<16;b++) if(KB[b]-2==o && 2-KJ[b]==c && ((m>>b)&1)) fprintf(f," (%d,%d)",o,c);
        fprintf(f,"\n"); }
    fprintf(f,"  (* = the square a trap is entered from)\n\n");
    fprintf(f,"OUTER-BEFORE-INNER EVENTS: %lld in all since the start, %lld not repaired; since step %lld, %lld of them within 8 of a corner are not classified below\n",S.viol,S.unrep,S.from4,S.evcorner);
    fprintf(f,"  by kind: where the Squirrel came from, and the 16 neighbours of the square it landed on ('.' unvisited, '#' visited, o = the square;\n");
    fprintf(f,"  rows from 2 rings out down to 2 rings in, columns from 2 squares counter-clockwise to 2 clockwise, as in the board pictures)\n");
    fprintf(f,"          count  came from  out+2  out+1  out 0  out-1  out-2\n");
    for(int q=0;q<nk;q++){ uint32_t key=S.hkey[idx[q]]-1; if(!(key>>20)) continue; int k=(key>>16)&15; unsigned m=key&0xffff;
        fprintf(f,"  %13lld  (%d,%d)   ",S.hcnt[idx[q]],2-KB[k],KJ[k]-2);
        for(int o=2;o>=-2;o--){ fprintf(f,"  "); for(int c=-2;c<=2;c++){ char ch=(o==0&&c==0)?'o':' ';
            for(int b=0;b<16;b++){ if(KB[b]-2==o && 2-KJ[b]==c) ch=((m>>b)&1)?'.':'#'; }
            fputc(ch,f); } }
        fprintf(f,"\n"); }
    fprintf(f,"\n  by steps since the later of the two squares clockwise of the inner square was visited (the repair needs both visited):\n ");
    for(int i=0;i<65;i++) if(S.evage[i]) fprintf(f," %d%s:%lld",i,i==64?"+":"",S.evage[i]);
    fprintf(f,"\n\nMOVES, sampled on every 8th step, as (rings out, squares clockwise)\n");
    { ll one[16], tot=0; for(int a=0;a<16;a++){ one[a]=0; for(int b=0;b<16;b++) one[a]+=S.mv2[b*16+a]; tot+=one[a]; }
      for(int a=0;a<16;a++) if(one[a]) fprintf(f,"  (%d,%d): %lld  %.4f%%\n",KB[a]-2,2-KJ[a],one[a],100.0*(double)one[a]/(double)(tot?tot:1));
      fprintf(f,"  pairs of consecutive moves, most frequent first (first move, then the next):\n");
      int pi[256]; for(int i=0;i<256;i++) pi[i]=i;
      for(int i=1;i<256;i++){ int v=pi[i], j=i; while(j>0 && S.mv2[pi[j-1]]<S.mv2[v]){ pi[j]=pi[j-1]; j--; } pi[j]=v; }
      for(int i=0;i<256 && S.mv2[pi[i]];i++){ int a=pi[i]/16, b=pi[i]%16; fprintf(f,"  (%d,%d) then (%d,%d): %lld  %.4f%%\n",KB[a]-2,2-KJ[a],KB[b]-2,2-KJ[b],S.mv2[pi[i]],100.0*(double)S.mv2[pi[i]]/(double)(tot?tot:1)); } }
    fprintf(f,"\nHEIGHT DIFFERENCES since step %lld, sampled on every 8th step (height of a line = its lowest unvisited ring)\n",S.from3);
    for(int w=1;w<=2;w++){ const ll *J = w==1?S.adj1:S.adj2;
        fprintf(f,"  visited line against the two lines %d away: rows = difference to one of them, columns = to the other (0..8+)\n",w);
        for(int a=0;a<9;a++){ int any=0; for(int b=0;b<9;b++) if(J[a*9+b]||J[b*9+a]) any=1; if(!any) continue;
            fprintf(f,"   %d:",a); for(int b=0;b<9;b++) fprintf(f," %lld",J[a*9+b]); fprintf(f,"\n"); } }
    fprintf(f,"\nkinds table: %lld of %d entries in use, %lld arrivals not counted because it was full\n",S.hused,HN/4*3,S.hover);
    if(fclose(f)==0) rename("stats.txt.tmp","stats.txt");
}

// board picture around the Squirrel at step n. kind 0: FREE=val, kind 1: GAP=val, kind 2: PIT=val, kind 3: first event of a kind
COLD static void picture(int kind, int val, ll n, ll x, ll y, int s, ll r, int fc, int rowsdown, ll hx, ll hy){
    ll ox,oy,cx,cy; const char*sd; ll ax=llabs(x), ay=llabs(y);
    if(s==RIGHT){ox=1;oy=0;cx=0;cy=-1;sd="right";}
    else if(s==TOP){ox=0;oy=1;cx=1;cy=0;sd="top";}
    else if(s==LEFT){ox=-1;oy=0;cx=0;cy=1;sd="left";}
    else {ox=0;oy=-1;cx=-1;cy=0;sd="bottom";}
    if(kind==0) out("\nFREE=%d at n=%lld a(n)=%lld pos=(%lld,%lld) ring %lld side %s, dist to corner %lld\n",val,n,spiral(x,y),x,y,r,sd,r-(ax<ay?ax:ay));
    else if(kind==2) out("\nPIT=%d at n=%lld a(n)=%lld pos=(%lld,%lld) ring %lld side %s, dist to corner %lld, free=%d (the pit is the unvisited square %lld at (%lld,%lld); all five lines around it are visited at least %d rings beyond it)\n",val,n,spiral(x,y),x,y,r,sd,r-(ax<ay?ax:ay),fc,spiral(hx,hy),hx,hy,val);
    if(kind==0 && val>=1 && val<=4 && n>1){
        char nm[88]; int len; ll pxx=S.rbx[(n-1)%RB]-x, pyy=S.rby[(n-1)%RB]-y;
        ll eo=pxx*ox+pyy*oy, ec=pxx*cx+pyy*cy;
        len=snprintf(nm,sizeof nm,"came from (%lld,%lld)%s; free:",eo,ec,(eo==2&&ec==-2)?" = where a trap is entered from":"");
        for(int o=-2;o<=2;o++) for(int c=2;c>=-2;c--){ if((abs(o)>abs(c)?abs(o):abs(c))!=2) continue;
            if(!get(x+o*ox+c*cx,y+o*oy+c*cy) && len<(int)sizeof nm-10) len+=snprintf(nm+len,sizeof nm-len," (%d,%d)",o,c); }
        int i; for(i=0;i<S.nkind;i++) if(!strcmp(S.kname[i],nm)) break;
        if(i==S.nkind && S.nkind<40){ strcpy(S.kname[i],nm); S.kcount[i]=0; S.nkind++; }
        if(i<S.nkind) S.kcount[i]++;
        out(" kind: %s\n",nm);
    }
    if(kind==3) out("\nEVENT of a new kind at n=%lld a(n)=%lld pos=(%lld,%lld) ring %lld side %s, dist to corner %lld, free=%d (the square 2 rows straight below the 0 is still unvisited)\n",n,spiral(x,y),x,y,r,sd,r-(ax<ay?ax:ay),fc);
    if(kind==0 || kind==2 || kind==3) ; else out("\nGAP=%d at n=%lld a(n)=%lld pos=(%lld,%lld) ring %lld side %s, dist to corner %lld, free=%d (the unvisited square is %d rows straight below the 0)\n",val,n,spiral(x,y),x,y,r,sd,r-(ax<ay?ax:ay),fc,val);
    out(" window: rows out=+4..-%d, cols cw=-9..+9 ; '.' unvisited, '#' visited, digits/letters = steps ago (0=now, a=10..z=35)\n",rowsdown);
    for(int o=4;o>=-rowsdown;o--){ out("   ");
        for(int c=-9;c<=9;c++){ ll sx=x+o*ox+c*cx, sy=y+o*oy+c*cy; char ch='.';
            if(get(sx,sy)){ ch='#'; for(int a=0;a<36 && a<n-1;a++){ if(S.rbx[(n-a)%RB]==sx&&S.rby[(n-a)%RB]==sy){ ch = a<10?('0'+a):('a'+a-10); break; } } }
            out("%c",ch); }
        out("  out=%d\n",o); }
}

int main(int argc,char**argv){
    ll N=0, every=100000000000LL; int thr=2, resume=0, fresh=0, gapthr=3; ll evmax=300; const char *logname="frontier.txt";
    for(int i=1;i<argc;i++){
        if(!strcmp(argv[i],"--resume")) resume=1;
        else if(!strcmp(argv[i],"--fresh")) fresh=1;
        else if(!strcmp(argv[i],"--thr") && i+1<argc) thr=atoi(argv[++i]);
        else if(!strcmp(argv[i],"--every") && i+1<argc) every=atoll(argv[++i]);
        else if(!strcmp(argv[i],"--log") && i+1<argc) logname=argv[++i];
        else if(!strcmp(argv[i],"--gap") && i+1<argc) gapthr=atoi(argv[++i]);
        else if(!strcmp(argv[i],"--events") && i+1<argc) evmax=atoll(argv[++i]);
        else if(argv[i][0]>='0' && argv[i][0]<='9') N=atoll(argv[i]);
        else { fprintf(stderr,"usage: %s [N] [--resume] [--fresh] [--thr K] [--every M] [--gap G] [--events K] [--log FILE]\n",argv[0]); return 1; }
    }
    if(every<1000) every=1000;
    init25();
    int nm=0;
    for(int dx=-2;dx<=2;dx++)for(int dy=-2;dy<=2;dy++){int a=abs(dx),b=abs(dy);if((a>b?a:b)==2){mdx[nm]=dx;mdy[nm]=dy;nm++;}}
    setvbuf(stdout,NULL,_IOLBF,0);
    signal(SIGPIPE,SIG_IGN);
    {   FILE *f=fopen(CKPT,"rb"); int have=f!=NULL; if(f) fclose(f);
        if(resume && !have){ fprintf(stderr,"no %s here to resume from\n",CKPT); return 1; }
        if(!resume && have && !fresh){ fprintf(stderr,"%s exists. Use --resume to continue that run, or --fresh to start over and overwrite it.\n",CKPT); return 1; } }
    if(strcmp(logname,"-")){ logf=fopen(logname,"a"); if(!logf){ fprintf(stderr,"cannot open log file %s\n",logname); return 1; } setvbuf(logf,NULL,_IOLBF,0); }

    if(resume){
        if(!load_ckpt()){ fprintf(stderr,"no %s here to resume from\n",CKPT); return 1; }
        thr=(int)S.thr;
        prog("resuming at n=%lld (%.2f h done so far)\n",S.n,S.elapsed/3600);
        out("\nRESUMED at n=%lld\n",S.n);
    } else {
        memset(&S,0,sizeof S); S.n=1; S.thr=thr; deadlow=-1; S.maxpit=-99; S.lastk=S.prevk=-1;
        alloc_sides(4096);
    }
    signal(SIGINT,onsig); signal(SIGTERM,onsig);

    ll x=S.x,y=S.y; int s=0; ll t=0,r=0; classify(x,y,&s,&t,&r);
    unsigned mask=0; int havemask=0;
    ll n=S.n; int trapped=0;
    int lastk = S.lastk>=0 ? K25[S.lastk] : -1, prevk = S.prevk>=0 ? K25[S.prevk] : -1;   // 25-bit numbering inside the loop
    double t0=now()-S.elapsed, tlast=now(); ll lastprog=n;
    ll nextprog = n<1000000000LL ? 1000000000LL : (n/10000000000LL+1)*10000000000LL;
    ll nextck = (n/every+1)*every;
    if(N>0) prog("running to n=%lld; Ctrl-C stops early and saves\n",N); else prog("running until Ctrl-C (saves and prints the summary)\n");

    for(;;){
        if(UNLIKELY(N>0 && n>=N)) break;
        if(UNLIKELY(stopflag)) break;
        n++;
        ll bx=0,by=0,nt=0,nr=0; int found=0, mvk=-1, isev=0, evpic=0;
        int fast = (r >= llabs(t)+8);
        if(LIKELY(fast)){
            int rev=(s==TOP||s==LEFT);
            if(UNLIKELY(!havemask)){ unsigned m5[5]; Ray *A=&side[s][t+T]; for(int j=0;j<5;j++) m5[j]=ray5(A+j-2,r); mask=mask25(m5,rev); }
            if(LIKELY(mask)){
                int k=__builtin_ctz(mask); int jp=k%5; int j=rev?4-jp:jp;
                nt=t+j-2; nr=r+k/5-2; xy_of(s,nt,nr,&bx,&by); found=1; mvk=k;
            }
        } else {
            ll best=-1;
            for(int k=0;k<16;k++){
                ll qx=x+mdx[k], qy=y+mdy[k];
                if(get(qx,qy)) continue;
                ll sn=spiral(qx,qy);
                if(best<0||sn<best){best=sn;bx=qx;by=qy;}
            }
            found = best>=0;
        }
        if(UNLIKELY(!found)){ n--; out("TRAPPED at n=%lld pos=(%lld,%lld) a(n)=%lld\n",n,x,y,spiral(x,y)); trapped=1; break; }
        if(UNLIKELY(S.pend) && !(bx==S.ppx&&by==S.ppy)){ S.unrep++; out("UNREPAIRED at n=%lld: went to (%lld,%lld), inner square (%lld,%lld) left unvisited\n",n,bx,by,S.ppx,S.ppy); }
        S.pend=0;
        x=bx;y=by; prevk=lastk; lastk=mvk;
        if(LIKELY(fast)){ t=nt; r=nr; } else classify(x,y,&s,&t,&r);
        if(UNLIKELY(r>T-12)) alloc_sides(2*T+1000);
        int fast2 = (r >= llabs(t)+8);
        Ray *B=&side[s][t+T];
        int fc, gd;
        if(LIKELY(fast2)){
            unsigned m5[5]; for(int j=0;j<5;j++) m5[j]=ray5(B+j-2,r);
            if(UNLIKELY(!(m5[2]&1))){ S.viol++; S.pend=1; xy_of(s,t,r-2,&S.ppx,&S.ppy); isev=1; }
            setray(s,t,B,r); gd=(int)lastd;
            if(UNLIKELY(!(n&7))){   ll bc=B->base, a;     // smoothness, on every 8th step: heights of the neighbouring lines after this visit
                ll b;
                a=llabs((ll)B[1].base-bc); b=llabs((ll)B[-1].base-bc); S.adj1[(a>8?8:a)*9+(b>8?8:b)]++;
                a=llabs((ll)B[2].base-bc); b=llabs((ll)B[-2].base-bc); S.adj2[(a>8?8:a)*9+(b>8?8:b)]++;
                if(prevk>=0 && lastk>=0) S.mv2[K16[prevk]*16+K16[lastk]]++; }
            mask=mask25(m5,(s==TOP||s==LEFT)); havemask=1;
            fc=__builtin_popcount(mask);
            if(UNLIKELY(isev)){ if(lastk>=0){ if(hcount(1u+(1u<<20)+((uint32_t)K16[lastk]<<16)+m16(mask)) && S.evpics<evmax){ S.evpics++; evpic=1; } } else S.evcorner++; }
        } else {
            if(r>=3){ ll px,py; psi(x,y,&px,&py); if(!get(px,py)){ S.viol++; S.pend=1; S.ppx=px; S.ppy=py; S.evcorner++; } }
            setray(s,t,B,r); gd=(int)lastd;
            havemask=0; fc=0; for(int k=0;k<16;k++) if(!get(x+mdx[k],y+mdy[k])) fc++;
        }
        S.rbx[n%RB]=x; S.rby[n%RB]=y;
        if(UNLIKELY(fc<=4) && fast2 && lastk>=0) hcount(1u+((uint32_t)K16[lastk]<<16)+m16(mask));
        S.hist[fc]++;
        if(UNLIKELY(S.follow>0)){ out("   then n=%lld a(n)=%lld (%lld,%lld) free=%d\n",n,spiral(x,y),x,y,fc); S.follow--; }
        if(UNLIKELY(fc<=thr) && n>20){ picture(0,fc,n,x,y,s,r,fc,5,0,0); S.follow=6; }
        if(UNLIKELY(gd)){ S.gapcount[gd>15?15:gd]++; if(gd>=gapthr){ picture(1,gd,n,x,y,s,r,fc,gd+2>5?gd+2:5,0,0); S.follow=6; } }
        if(UNLIKELY(isev) && fast2){      // how long ago were the two squares clockwise of the inner square visited?
            ll ox,oy,cx,cy; if(s==RIGHT){ox=1;oy=0;cx=0;cy=-1;} else if(s==TOP){ox=0;oy=1;cx=1;cy=0;} else if(s==LEFT){ox=-1;oy=0;cx=0;cy=1;} else {ox=0;oy=-1;cx=-1;cy=0;}
            ll ax1=x-2*ox+cx, ay1=y-2*oy+cy, ax2=x-2*ox+2*cx, ay2=y-2*oy+2*cy; int age=64;
            for(int a=1;a<RB && a<n-1;a++){ ll qx=S.rbx[(n-a)%RB], qy=S.rby[(n-a)%RB]; if((qx==ax1&&qy==ay1)||(qx==ax2&&qy==ay2)){ age=a; break; } }
            S.evage[age]++;
            if(evpic){ picture(3,0,n,x,y,s,r,fc,5,0,0); S.follow=6; }
        }
        if(UNLIKELY(gd>=2) && fast2 && S.nact<4){      // a deep hole has just been left on this line: follow it until it is filled
            int dup=0; for(int a=0;a<S.nact;a++) if(S.act[a][0]==s && S.act[a][1]==t) dup=1;
            if(!dup){ ll *A=S.act[S.nact++]; A[0]=s; A[1]=t; A[2]=B->base; A[3]=-99; A[4]=0; }
        }
        if(UNLIKELY(S.nact)) for(int a=0;a<S.nact;a++){
            ll *A=S.act[a]; const Ray *L=&side[A[0]][A[1]+T];
            if(L->base!=A[2]){               // filled
                ll m=A[3]; S.holes++; S.pithist[m<=0?0:(m>7?7:m)]++;
                memmove(S.act[a],S.act[a+1],(size_t)(S.nact-1-a)*sizeof S.act[0]); S.nact--; a--; continue;
            }
            ll pd=1000000;
            for(int q=-2;q<=2;q++){ const Ray *M=L+q; ll tp = M->win ? (ll)M->base+63-__builtin_clzll(M->win) : (ll)M->base-1; if(tp-A[2]<pd) pd=tp-A[2]; }
            if(pd>A[3]) A[3]=pd;
            if(pd>S.maxpit) S.maxpit=pd;
            if(pd>=2 && !A[4]){ A[4]=1; ll hx,hy; xy_of((int)A[0],A[1],A[2],&hx,&hy); picture(2,(int)pd,n,x,y,s,r,fc,8,hx,hy); S.follow=6; }
        }
        if(UNLIKELY(n==nextprog)){
            double tn=now(); double per=(tn-tlast)/(double)(n-lastprog)*1e9; tlast=tn; lastprog=n;
            nextprog = n<10000000000LL ? n+1000000000LL : n+10000000000LL;
            prog("  %.3e steps, ring %lld, %.2f h elapsed, %.1f s per 1e9 steps",(double)n,r,(tn-t0)/3600,per);
            if(N>0) prog(", about %.1f h left",per*(double)(N-n)/1e9/3600);
            { ll g=0; for(int i=3;i<16;i++) g+=S.gapcount[i];
              prog(" | 2-free %lld, 1-free %lld, unrepaired %lld, skipped %lld, gap>=3 %lld, deepest pit %lld\n",S.hist[2],S.hist[1],S.unrep,ndead,g,S.maxpit<-50?0:S.maxpit); }
        }
        if(UNLIKELY(n==nextck)){
            nextck+=every;
            S.n=n; S.x=x; S.y=y; S.elapsed=now()-t0; S.lastk = lastk>=0?K16[lastk]:-1; S.prevk = prevk>=0?K16[prevk]:-1;
            out("\nSTATUS after %lld steps (%.2f h)\n",n,S.elapsed/3600);
            summary(0); havemask=0;
            save_ckpt(); write_stats();
        }
    }
    S.n=n; S.x=x; S.y=y; S.elapsed=now()-t0; S.lastk = lastk>=0?K16[lastk]:-1; S.prevk = prevk>=0?K16[prevk]:-1;
    if(stopflag && !trapped) out("\nSTOPPED by signal at n=%lld (continue with --resume)\n",n);
    if(!trapped) save_ckpt();
    out("\nsteps done %lld\n", n);
    summary(trapped);
    if(!trapped) save_ckpt();
    write_stats();
    prog("%s after %.2f hours; state saved in %s\n",trapped?"trapped":"stopped",S.elapsed/3600,CKPT);
    return 0;
}
