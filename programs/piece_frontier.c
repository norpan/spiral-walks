// piece_frontier.c -- the "lowest unvisited square" walk on the square spiral for any piece built from the
// leapers W (0,1), F (1,1), D (0,2), N (1,2) and A (2,2): Civet = NDF, Spider = NDFA, Falafel = FA,
// Squirrel = NDA, Knight = N, ... Same method as squirrel_frontier.c: memory grows with the perimeter of
// the visited region, the walk is exact, and the run can be stopped and resumed.
//
// Build:   cc -O2 -o piece_frontier piece_frontier.c
// Start:   ./piece_frontier --piece NDF          run until Ctrl-C, or until the piece is trapped
//          ./piece_frontier --piece NDF N        stop after N terms
// Resume:  ./piece_frontier --resume [N]         continue from piece.ckpt in the current folder
// Options: --kinds K   count by kind every arrival with at most K unvisited moves (default: 2, 4 or 7 for
//                      pieces with up to 8, up to 16, or more moves)
//          --every M   checkpoint and STATUS block every M steps (default 1e11)
//          --fresh     start over even if a checkpoint exists
//          --log FILE  log file, appended to (default frontier.txt; "-" for none)
// Run each piece in its own folder: it writes frontier.txt (log), stats.txt (tables) and piece.ckpt there.
//
// Reports. TRAPPED if the walk ends. For every number of unvisited moves from 0 to 6: a board picture of
// the first 10 arrivals with that number, a one-line record of the next 1000, then only the count.
// A board picture the first time a visit leaves an unvisited square d rings further in on its own line,
// for each d. At every STATUS: the histogram of unvisited moves, the lowest unvisited number (every
// reachable number below it has appeared), squares that can no longer be visited, the rings the boundary
// spans and the open holes. stats.txt: kinds of arrival with few unvisited moves (where the piece came
// from and which moves were free), gaps, moves and pairs of moves, height differences between lines.
//
// A piece without W and N only ever stands on squares with x+y even; the other squares are treated as
// filled. Pieces confined to a sparser lattice (D, A or DA alone) are not supported.
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
#define INL static inline __attribute__((always_inline))
enum { RIGHT=0, TOP=1, LEFT=2, BOTTOM=3 };
typedef struct { uint64_t win; int32_t base; int32_t pad; } Ray;
static Ray *side[4]; static ll T;
static ll maxdepth=0, ndead=0, deadlow=-1, lastd=0;
static int mdx[24], mdy[24], nmv;          // the moves in board coordinates
static uint32_t MOVES, SP[32];             // moves as bits 5*(out+2)+(2-cw); SP spreads bit i to bit 5*i
static uint64_t U; static unsigned P5[2];  // squares the piece can never stand on, as window bits
static int CB;
static volatile sig_atomic_t stopflag=0;
static void onsig(int sig){ (void)sig; stopflag=1; }
#define CKPT "piece.ckpt"
static FILE *logf;
COLD static void out(const char *fmt, ...){ va_list ap; va_start(ap,fmt); vprintf(fmt,ap); va_end(ap);
    if(logf){ va_start(ap,fmt); vfprintf(logf,fmt,ap); va_end(ap); } }
COLD static void prog(const char *fmt, ...){ va_list ap; va_start(ap,fmt); vfprintf(stderr,fmt,ap); va_end(ap);
    if(logf){ va_start(ap,fmt); vfprintf(logf,fmt,ap); va_end(ap); } }

INL ll spiral(ll x, ll y){
    ll ax = x<0?-x:x, ay = y<0?-y:y; ll r = ax>ay?ax:ay;
    if(r==0) return 1;
    ll base=(2*r-1)*(2*r-1);
    if(x==r && y>-r) return base+(y+r);
    if(y==r) return base+2*r+(r-x);
    if(x==-r) return base+4*r+(r-y);
    return base+6*r+(x+r);
}
INL void classify(ll x, ll y, int *s, ll *t, ll *r){
    ll ax=x<0?-x:x, ay=y<0?-y:y; ll rr=ax>ay?ax:ay; *r=rr;
    if(x==rr && y>-rr){ *s=RIGHT; *t=y; }
    else if(y==rr){ *s=TOP; *t=x; }
    else if(x==-rr){ *s=LEFT; *t=y; }
    else { *s=BOTTOM; *t=x; }
}
INL void xy_of(int s, ll t, ll r, ll *x, ll *y){
    switch(s){ case RIGHT: *x=r; *y=t; break; case TOP: *x=t; *y=r; break;
               case LEFT: *x=-r; *y=t; break; default: *x=t; *y=-r; }
}
INL ll outmin(int s, ll t){   // lowest ring on line (s,t)
    if(s==RIGHT || s==BOTTOM) return t>0 ? t : -t+1;
    return t>=0 ? t+1 : -t;
}
COLD static void alloc_sides(ll newT){
    for(int s=0;s<4;s++){
        Ray *a=malloc((size_t)(2*newT+1)*sizeof(Ray));
        if(!a){ fprintf(stderr,"out of memory\n"); exit(1); }
        for(ll t=-newT;t<=newT;t++){ ll b=outmin(s,t); if(CB && ((b+t)&1)) b++; a[t+newT].win=0; a[t+newT].base=(int32_t)b; a[t+newT].pad=0; }
        if(side[s]){ memcpy(a+(newT-T), side[s], (size_t)(2*T+1)*sizeof(Ray)); free(side[s]); }
        side[s]=a;
    }
    T=newT;
}
INL int getray(const Ray *R, ll r){
    ll d = r - R->base;
    if(d<0) return 1;
    if(d>=64) return 0;
    return (int)((R->win>>d)&1);
}
INL int get(ll x, ll y){     // visited, or a square the piece can never stand on
    if(CB && ((x+y)&1)) return 1;
    int s; ll t,r; classify(x,y,&s,&t,&r);
    if(r==0) return 1;
    return getray(&side[s][t+T], r);
}
// filled flags of rings o-2..o+2 on one line, bit i <-> ring o-2+i; par = (o + line position) & 1
INL unsigned ray5(const Ray *R, ll o, int par){
    ll d = (o-2) - R->base; unsigned v;
    if(d>=0){ v = d>=64 ? 0 : (unsigned)(R->win>>d)&31u; }
    else if(d<=-5) v=31u;
    else { int k=(int)(-d); v=(unsigned)(((R->win<<k)|((1ull<<k)-1))&31u); }
    return v|P5[par];
}
INL void slide(Ray *R){
    uint64_t full=R->win|U;
    if(LIKELY(full&1)){ uint64_t inv=~full;
        if(UNLIKELY(inv==0)){ R->base+=64; R->win=0; }
        else { int tz=__builtin_ctzll(inv); R->base+=tz; R->win>>=tz; } }
}
COLD static void skipped(ll hx, ll hy){
    ll sn=spiral(hx,hy);
    out("\nSKIPPED FOREVER: square %lld at (%lld,%lld) is unvisited and every square the piece could come from is visited\n",sn,hx,hy);
    ndead++; if(deadlow<0||sn<deadlow) deadlow=sn;
}
COLD static ll overflow(int s, ll t, Ray *R, ll r){
    for(;;){
        ll d = r - R->base;
        if(d<64) return d;
        ll hx,hy; xy_of(s,t,R->base,&hx,&hy);
        int freen=0; for(int k=0;k<nmv;k++) if(!get(hx+mdx[k],hy+mdy[k])) freen++;
        if(freen>0){
            out("\nWINDOW OVERFLOW: square %lld at (%lld,%lld) is still unvisited, has %d unvisited neighbours, and lies %lld rings inside a visit on its own line. Stopping: the 64-ring window is too small for this piece.\n",
                   spiral(hx,hy),hx,hy,freen,d);
            exit(2);
        }
        skipped(hx,hy);
        R->win|=1; slide(R);
    }
}
INL void setray(int s, ll t, Ray *R, ll r){
    ll d = r - R->base;
    if(UNLIKELY(d>=64)) d=overflow(s,t,R,r);
    if(d>maxdepth) maxdepth=d;
    lastd=d;
    R->win |= 1ull<<d;
    slide(R);
}
static double now(void){ struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t); return t.tv_sec+t.tv_nsec*1e-9; }
// unvisited legal moves as a 25-bit mask in spiral-number order: bit 5*(ring offset+2) + position, position 0 = lowest number
INL unsigned mask25(const unsigned *m, int rev){
    unsigned v;
    if(rev) v = SP[~m[4]&31] | SP[~m[3]&31]<<1 | SP[~m[2]&31]<<2 | SP[~m[1]&31]<<3 | SP[~m[0]&31]<<4;
    else    v = SP[~m[0]&31] | SP[~m[1]&31]<<1 | SP[~m[2]&31]<<2 | SP[~m[3]&31]<<3 | SP[~m[4]&31]<<4;
    return v & MOVES;
}
#define KO(k) ((k)/5-2)        // rings out of move bit k
#define KC(k) (2-(k)%5)        // squares clockwise of move bit k

#define RB 64
#define HN 65536
typedef struct {
    char magic[8]; ll version; char piece[16];
    ll n, x, y, T;
    ll hist[26], follow;
    ll rbx[RB], rby[RB];
    ll maxdepth, ndead, deadlow, kthr;
    double elapsed;
    ll gapcount[16];
    ll adj1[81], adj2[81];     // |height difference| to the two lines 1 away / 2 away, index 9*a+b, on every 8th step
    ll lastk, prevk;           // the last two moves as bit numbers (-1: made within 8 of a corner)
    ll mv2[625];               // pairs of consecutive moves, on every 8th step
    ll hused, hover;
    ll hcnt[HN]; uint32_t hkey[HN];   // key = 1 + (move<<25) + mask of unvisited moves
} State;
static State S;
static inline int hcount(uint32_t key){
    uint32_t h=(key*2654435761u)>>16;
    for(;;){
        uint32_t kk=S.hkey[h];
        if(kk==key){ S.hcnt[h]++; return 0; }
        if(!kk){ if(S.hused>=HN/4*3){ S.hover++; return 0; } S.hkey[h]=key; S.hcnt[h]=1; S.hused++; return 1; }
        h=(h+1)&(HN-1);
    }
}
static int setup_piece(const char *L){
    int hasW=0,hasN=0,hasF=0; nmv=0; MOVES=0;
    for(const char *p=L;*p;p++){ int a,b;
        switch(*p){ case 'W':a=0;b=1;hasW=1;break; case 'F':a=1;b=1;hasF=1;break; case 'D':a=0;b=2;break;
                    case 'N':a=1;b=2;hasN=1;break; case 'A':a=2;b=2;break; default: return 0; }
        for(int sx=-1;sx<=1;sx+=2) for(int sy=-1;sy<=1;sy+=2) for(int sw=0;sw<2;sw++){
            int dx=(sw?b:a)*sx, dy=(sw?a:b)*sy, dup=0;
            for(int k=0;k<nmv;k++) if(mdx[k]==dx&&mdy[k]==dy) dup=1;
            if(!dup){ mdx[nmv]=dx; mdy[nmv]=dy; nmv++; MOVES |= 1u<<(5*(dx+2)+(2-dy)); } } }
    if(!nmv || (!hasW && !hasN && !hasF)) return 0;
    CB = !hasW && !hasN;
    U = CB ? 0xAAAAAAAAAAAAAAAAull : 0; P5[0] = CB ? 10 : 0; P5[1] = CB ? 21 : 0;
    for(unsigned v=0;v<32;v++){ SP[v]=0; for(int i=0;i<5;i++) if((v>>i)&1) SP[v]|=1u<<(5*i); }
    return 1;
}
COLD static void save_ckpt(void){
    FILE *f=fopen(CKPT ".tmp","wb");
    if(!f){ fprintf(stderr,"warning: cannot write checkpoint\n"); return; }
    memcpy(S.magic,"SQPIECE",8); S.version=1; S.T=T; S.maxdepth=maxdepth; S.ndead=ndead; S.deadlow=deadlow;
    int ok = fwrite(&S,sizeof S,1,f)==1;
    for(int s=0;s<4 && ok;s++) ok = fwrite(side[s],sizeof(Ray),(size_t)(2*T+1),f)==(size_t)(2*T+1);
    ok = (fclose(f)==0) && ok;
    if(!ok){ fprintf(stderr,"warning: checkpoint write failed (disk full?)\n"); remove(CKPT ".tmp"); return; }
    rename(CKPT ".tmp", CKPT);
}
COLD static int load_ckpt(void){
    FILE *f=fopen(CKPT,"rb"); if(!f) return 0;
    if(fread(&S,sizeof S,1,f)!=1 || memcmp(S.magic,"SQPIECE",8)!=0 || S.version!=1){ fclose(f); fprintf(stderr,"%s is not a valid checkpoint\n",CKPT); exit(1); }
    S.piece[15]=0; if(!setup_piece(S.piece)){ fprintf(stderr,"bad piece in checkpoint\n"); exit(1); }
    T=0; alloc_sides(S.T);
    for(int s=0;s<4;s++) if(fread(side[s],sizeof(Ray),(size_t)(2*T+1),f)!=(size_t)(2*T+1)){ fprintf(stderr,"%s is truncated\n",CKPT); exit(1); }
    fclose(f);
    maxdepth=S.maxdepth; ndead=S.ndead; deadlow=S.deadlow;
    return 1;
}
COLD static void summary(int trapped){
    out("piece %s, %d moves\n",S.piece,nmv);
    out("unvisited moves on arrival:"); for(int i=0;i<=nmv;i++) out(" %d:%lld",i,S.hist[i]); out("\n");
    ll low=-1,lx=0,ly=0, maxring=0, nholes=0, holes[16]; memset(holes,0,sizeof holes);
    for(int ss=0;ss<4;ss++) for(ll tt=-T;tt<=T;tt++){
        Ray *R=&side[ss][tt+T]; ll b0=outmin(ss,tt); if(CB && ((b0+tt)&1)) b0++;
        if(!R->win && R->base>b0 && R->base-1>maxring) maxring=R->base-1;
        if(R->win){
            int top=63-__builtin_clzll(R->win); uint64_t full=R->win|U;
            if(R->base+top>maxring) maxring=R->base+top;
            for(int k=0;k<top;k++) if(!((full>>k)&1)){
                nholes++; holes[top-k>15?15:top-k]++;
                ll qx,qy; xy_of(ss,tt,R->base+k,&qx,&qy);
                int near=0; if(!trapped) for(int q=0;q<nmv;q++) if(qx+mdx[q]==S.x && qy+mdy[q]==S.y) near=1;
                if(near) continue;      // the piece can still step onto it
                int freen=0; for(int q=0;q<nmv;q++) if(!get(qx+mdx[q],qy+mdy[q])) freen++;
                if(freen==0){ skipped(qx,qy); R->win|=1ull<<k; }
            }
            slide(R);
        }
        ll hx,hy; xy_of(ss,tt,R->base,&hx,&hy); ll sn=spiral(hx,hy);
        if(low<0||sn<low){ low=sn; lx=hx; ly=hy; }
    }
    out("lowest unvisited number: %lld at (%lld,%lld)%s\n",low,lx,ly, ndead? "" : (CB?"  => every number below it on a square the piece can stand on has appeared":"  => every number below it has appeared"));
    out("squares skipped forever: %lld",ndead); if(ndead) out(" (lowest %lld)",deadlow); out("\n");
    out("deepest gap behind a visit on one line: %lld rings (window holds 64)\n",maxdepth);
    out("visits by gap (rings to the lowest unvisited square of the same line):");
    { int any=0; for(int i=1;i<16;i++) if(S.gapcount[i]){ out(" %d%s:%lld",i,i==15?"+":"",S.gapcount[i]); any=1; } if(!any) out(" none"); out("\n"); }
    { ll lr=llabs(lx)>llabs(ly)?llabs(lx):llabs(ly);
      out("boundary now: lowest unvisited ring %lld, highest visited ring %lld; unvisited squares below a visited square of their line: %lld",lr,maxring,nholes);
      if(nholes){ out(" (by rings below the outermost visited one:"); for(int i=1;i<16;i++) if(holes[i]) out(" %d%s:%lld",i,i==15?"+":"",holes[i]); out(")"); }
      out("\n"); }
    out("kinds of arrival with at most %lld unvisited moves: %lld, %lld arrivals lost to a full table; tables in stats.txt\n",S.kthr,S.hused,S.hover);
}
static int cmpkind(const void *a, const void *b){
    int i=*(const int*)a, j=*(const int*)b; uint32_t ki=S.hkey[i]-1, kj=S.hkey[j]-1;
    int fi=__builtin_popcount(ki&0x1ffffff), fj=__builtin_popcount(kj&0x1ffffff); if(fi!=fj) return fi-fj;
    return S.hcnt[i]<S.hcnt[j] ? 1 : (S.hcnt[i]>S.hcnt[j] ? -1 : (ki<kj?-1:1));
}
COLD static void write_stats(void){
    FILE *f=fopen("stats.txt.tmp","w"); if(!f) return;
    static int idx[HN]; int nk=0; for(int i=0;i<HN;i++) if(S.hkey[i]) idx[nk++]=i;
    qsort(idx,(size_t)nk,sizeof idx[0],cmpkind);
    fprintf(f,"Piece %s (%d moves) on the square spiral, statistics after %lld steps (rewritten at every checkpoint)\n",S.piece,nmv,S.n);
    fprintf(f,"Offsets are (rings out, squares clockwise) from the square. Kinds, moves and heights cover squares at least 8 from a corner.\n\n");
    fprintf(f,"UNVISITED MOVES ON ARRIVAL\n "); for(int i=0;i<=nmv;i++) fprintf(f," %d:%lld",i,S.hist[i]);
    fprintf(f,"\n\nGAPS: visits by how many rings further in the lowest unvisited square of the same line lies\n ");
    for(int i=1;i<16;i++) if(S.gapcount[i]) fprintf(f," %d%s:%lld",i,i==15?"+":"",S.gapcount[i]);
    fprintf(f,"\n\nARRIVALS WITH AT MOST %lld UNVISITED MOVES, by where the piece came from and which moves were unvisited\n",S.kthr);
    fprintf(f,"  free         count  came from  unvisited\n");
    for(int q=0;q<nk;q++){ uint32_t key=S.hkey[idx[q]]-1; int k=(int)(key>>25); unsigned m=key&0x1ffffff;
        fprintf(f,"  %4d %13lld  (%d,%d)  ",__builtin_popcount(m),S.hcnt[idx[q]],-KO(k),-KC(k));
        for(int b=24;b>=0;b--) if((m>>b)&1) fprintf(f," (%d,%d)",KO(b),KC(b));
        fprintf(f,"\n"); }
    fprintf(f,"\nMOVES, sampled on every 8th step\n");
    { ll one[25], tot=0; for(int a=0;a<25;a++){ one[a]=0; for(int b=0;b<25;b++) one[a]+=S.mv2[b*25+a]; tot+=one[a]; }
      for(int a=0;a<25;a++) if(one[a]) fprintf(f,"  (%d,%d): %lld  %.4f%%\n",KO(a),KC(a),one[a],100.0*(double)one[a]/(double)(tot?tot:1));
      fprintf(f,"  pairs of consecutive moves, most frequent first (first move, then the next):\n");
      static int pi[625]; for(int i=0;i<625;i++) pi[i]=i;
      for(int i=1;i<625;i++){ int v=pi[i], j=i; while(j>0 && S.mv2[pi[j-1]]<S.mv2[v]){ pi[j]=pi[j-1]; j--; } pi[j]=v; }
      for(int i=0;i<60 && S.mv2[pi[i]];i++){ int a=pi[i]/25, b=pi[i]%25; fprintf(f,"  (%d,%d) then (%d,%d): %lld  %.4f%%\n",KO(a),KC(a),KO(b),KC(b),S.mv2[pi[i]],100.0*(double)S.mv2[pi[i]]/(double)(tot?tot:1)); } }
    fprintf(f,"\nHEIGHT DIFFERENCES, sampled on every 8th step (height of a line = its lowest unvisited ring)\n");
    for(int w=1;w<=2;w++){ const ll *J = w==1?S.adj1:S.adj2;
        fprintf(f,"  visited line against the two lines %d away: rows = difference to one of them, columns = to the other (0..8+)\n",w);
        for(int a=0;a<9;a++){ int any=0; for(int b=0;b<9;b++) if(J[a*9+b]||J[b*9+a]) any=1; if(!any) continue;
            fprintf(f,"   %d:",a); for(int b=0;b<9;b++) fprintf(f," %lld",J[a*9+b]); fprintf(f,"\n"); } }
    fprintf(f,"\nkinds table: %lld of %d entries in use, %lld arrivals not counted because it was full\n",S.hused,HN/4*3,S.hover);
    if(fclose(f)==0) rename("stats.txt.tmp","stats.txt");
}
// what: 0 = arrival with fc unvisited moves (pic: with board picture), 1 = first gap of depth val
COLD static void report(int what, int val, int pic, ll n, ll x, ll y, int s, ll r, int fc){
    ll ox,oy,cx,cy; const char*sd; ll ax=llabs(x), ay=llabs(y);
    if(s==RIGHT){ox=1;oy=0;cx=0;cy=-1;sd="right";}
    else if(s==TOP){ox=0;oy=1;cx=1;cy=0;sd="top";}
    else if(s==LEFT){ox=-1;oy=0;cx=0;cy=1;sd="left";}
    else {ox=0;oy=-1;cx=-1;cy=0;sd="bottom";}
    if(what==0){
        ll px=S.rbx[(n-1)%RB]-x, py=S.rby[(n-1)%RB]-y;
        out("%sFREE=%d at n=%lld a(n)=%lld pos=(%lld,%lld) ring %lld side %s, dist to corner %lld; came from (%lld,%lld); unvisited:",pic?"\n":"",val,n,spiral(x,y),x,y,r,sd,r-(ax<ay?ax:ay),px*ox+py*oy,px*cx+py*cy);
        for(int o=2;o>=-2;o--) for(int c=2;c>=-2;c--) for(int k=0;k<nmv;k++) if(mdx[k]==o && mdy[k]==c && !get(x+o*ox+c*cx,y+o*oy+c*cy)) out(" (%d,%d)",o,c);
        out("\n");
    } else out("\nFIRST GAP OF %d at n=%lld a(n)=%lld pos=(%lld,%lld) ring %lld side %s, dist to corner %lld, unvisited moves %d (the lowest unvisited square of this line is %d rows straight below the 0)\n",val,n,spiral(x,y),x,y,r,sd,r-(ax<ay?ax:ay),fc,val);
    if(!pic) return;
    int down = what==1 && val+2>5 ? (val+2>40?40:val+2) : 5;
    out(" window: rows out=+4..-%d, cols cw=-9..+9 ; '.' unvisited, '#' visited%s, digits/letters = steps ago (0=now, a=10..z=35)\n",down,CB?" or never reachable":"");
    for(int o=4;o>=-down;o--){ out("   ");
        for(int c=-9;c<=9;c++){ ll sx=x+o*ox+c*cx, sy=y+o*oy+c*cy; char ch='.';
            if(get(sx,sy)){ ch = (CB && ((sx+sy)&1)) ? ' ' : '#'; for(int a=0;a<36 && a<n-1;a++){ if(S.rbx[(n-a)%RB]==sx&&S.rby[(n-a)%RB]==sy){ ch = a<10?('0'+a):('a'+a-10); break; } } }
            out("%c",ch); }
        out("  out=%d\n",o); }
}

int main(int argc,char**argv){
    ll N=0, every=100000000000LL, kthr=-1; int resume=0, fresh=0; const char *logname="frontier.txt", *piece=NULL;
    for(int i=1;i<argc;i++){
        if(!strcmp(argv[i],"--resume")) resume=1;
        else if(!strcmp(argv[i],"--fresh")) fresh=1;
        else if(!strcmp(argv[i],"--piece") && i+1<argc) piece=argv[++i];
        else if(!strcmp(argv[i],"--kinds") && i+1<argc) kthr=atoll(argv[++i]);
        else if(!strcmp(argv[i],"--every") && i+1<argc) every=atoll(argv[++i]);
        else if(!strcmp(argv[i],"--log") && i+1<argc) logname=argv[++i];
        else if(argv[i][0]>='0' && argv[i][0]<='9') N=atoll(argv[i]);
        else { fprintf(stderr,"usage: %s --piece LETTERS [N] [--kinds K] [--every M] [--fresh] [--log FILE]\n       %s --resume [N]\n",argv[0],argv[0]); return 1; }
    }
    if(every<1000) every=1000;
    setvbuf(stdout,NULL,_IOLBF,0);
    signal(SIGPIPE,SIG_IGN);
    {   FILE *f=fopen(CKPT,"rb"); int have=f!=NULL; if(f) fclose(f);
        if(resume && !have){ fprintf(stderr,"no %s here to resume from\n",CKPT); return 1; }
        if(!resume && have && !fresh){ fprintf(stderr,"%s exists. Use --resume to continue that run, or --fresh to start over and overwrite it.\n",CKPT); return 1; }
        if(!resume && (!piece || strlen(piece)>8 || !setup_piece(piece))){ fprintf(stderr,"give the piece with --piece, as letters from W F D N A (for example NDF); D, A and DA alone are not supported\n"); return 1; } }
    if(strcmp(logname,"-")){ logf=fopen(logname,"a"); if(!logf){ fprintf(stderr,"cannot open log file %s\n",logname); return 1; } setvbuf(logf,NULL,_IOLBF,0); }

    if(resume){
        if(!load_ckpt()){ fprintf(stderr,"no %s here to resume from\n",CKPT); return 1; }
        prog("resuming piece %s at n=%lld (%.2f h done so far)\n",S.piece,S.n,S.elapsed/3600);
        out("\nRESUMED at n=%lld\n",S.n);
    } else {
        memset(&S,0,sizeof S); strcpy(S.piece,piece); S.n=1; deadlow=-1; S.lastk=S.prevk=-1;
        S.kthr = kthr>=0 ? kthr : (nmv<=8 ? 2 : (nmv<=16 ? 4 : 7));
        alloc_sides(4096);
        out("piece %s, %d moves%s\n",S.piece,nmv,CB?" (stands only on squares with x+y even)":"");
    }
    signal(SIGINT,onsig); signal(SIGTERM,onsig);

    ll x=S.x,y=S.y; int s=0; ll t=0,r=0; classify(x,y,&s,&t,&r);
    unsigned mask=0; int havemask=0; const int kth=(int)S.kthr;
    ll n=S.n; int trapped=0;
    int lastk=(int)S.lastk, prevk=(int)S.prevk;
    double t0=now()-S.elapsed, tlast=now(); ll lastprog=n;
    ll nextprog = n<1000000000LL ? 1000000000LL : (n/10000000000LL+1)*10000000000LL;
    ll nextck = (n/every+1)*every;
    if(N>0) prog("running to n=%lld; Ctrl-C stops early and saves\n",N); else prog("running until Ctrl-C or until the piece is trapped\n");

    for(;;){
        if(UNLIKELY(N>0 && n>=N)) break;
        if(UNLIKELY(stopflag)) break;
        n++;
        ll bx=0,by=0,nt=0,nr=0; int found=0, mvk=-1;
        int fast = (r >= llabs(t)+8);
        if(LIKELY(fast)){
            int rev=(s==TOP||s==LEFT);
            if(UNLIKELY(!havemask)){ unsigned m5[5]; Ray *A=&side[s][t+T]; for(int j=0;j<5;j++) m5[j]=ray5(A+j-2,r,(int)((r+t+j)&1)); mask=mask25(m5,rev); }
            if(LIKELY(mask)){
                int k=__builtin_ctz(mask); int jp=k%5; int j=rev?4-jp:jp;
                nt=t+j-2; nr=r+k/5-2; xy_of(s,nt,nr,&bx,&by); found=1; mvk=k;
            }
        } else {
            ll best=-1;
            for(int k=0;k<nmv;k++){
                ll qx=x+mdx[k], qy=y+mdy[k];
                if(get(qx,qy)) continue;
                ll sn=spiral(qx,qy);
                if(best<0||sn<best){best=sn;bx=qx;by=qy;}
            }
            found = best>=0;
        }
        if(UNLIKELY(!found)){ n--; out("\nTRAPPED at step %lld on square %lld, pos=(%lld,%lld)\n",n,spiral(x,y),x,y); trapped=1; break; }
        x=bx;y=by; prevk=lastk; lastk=mvk;
        if(LIKELY(fast)){ t=nt; r=nr; } else classify(x,y,&s,&t,&r);
        if(UNLIKELY(r>T-12)) alloc_sides(2*T+1000);
        int fast2 = (r >= llabs(t)+8);
        Ray *B=&side[s][t+T];
        int fc, gd;
        if(LIKELY(fast2)){
            unsigned m5[5]; for(int j=0;j<5;j++) m5[j]=ray5(B+j-2,r,(int)((r+t+j)&1));
            setray(s,t,B,r); gd=(int)lastd;
            if(UNLIKELY(!(n&7))){   ll bc=B->base, a, b;
                a=llabs((ll)B[1].base-bc); b=llabs((ll)B[-1].base-bc); S.adj1[(a>8?8:a)*9+(b>8?8:b)]++;
                a=llabs((ll)B[2].base-bc); b=llabs((ll)B[-2].base-bc); S.adj2[(a>8?8:a)*9+(b>8?8:b)]++;
                if(prevk>=0 && lastk>=0) S.mv2[prevk*25+lastk]++; }
            mask=mask25(m5,(s==TOP||s==LEFT)); havemask=1;
            fc=__builtin_popcount(mask);
        } else {
            setray(s,t,B,r); gd=(int)lastd;
            havemask=0; fc=0; for(int k=0;k<nmv;k++) if(!get(x+mdx[k],y+mdy[k])) fc++;
        }
        S.rbx[n%RB]=x; S.rby[n%RB]=y;
        if(UNLIKELY(fc<=kth) && fast2 && lastk>=0) hcount(1u+((uint32_t)lastk<<25)+mask);
        S.hist[fc]++;
        if(UNLIKELY(S.follow>0)){ out("   then n=%lld a(n)=%lld (%lld,%lld) unvisited moves %d\n",n,spiral(x,y),x,y,fc); S.follow--; }
        if(UNLIKELY(fc<=6) && n>100 && S.hist[fc]<=1010){ int pic=S.hist[fc]<=10; report(0,fc,pic,n,x,y,s,r,fc); if(pic) S.follow=6; }
        if(UNLIKELY(gd)){ int g=gd>15?15:gd; if(++S.gapcount[g]==1 && n>100){ report(1,gd,1,n,x,y,s,r,fc); S.follow=6; } }
        if(UNLIKELY(n==nextprog)){
            double tn=now(); double per=(tn-tlast)/(double)(n-lastprog)*1e9; tlast=tn; lastprog=n;
            nextprog = n<10000000000LL ? n+1000000000LL : n+10000000000LL;
            int lo=0; while(lo<nmv && !S.hist[lo]) lo++;
            prog("  %.3e steps, ring %lld, %.2f h elapsed, %.1f s per 1e9 steps | fewest unvisited moves so far %d (%lld times), deepest gap %lld, skipped %lld\n",(double)n,r,(tn-t0)/3600,per,lo,S.hist[lo],maxdepth,ndead);
        }
        if(UNLIKELY(n==nextck)){
            nextck+=every;
            S.n=n; S.x=x; S.y=y; S.elapsed=now()-t0; S.lastk=lastk; S.prevk=prevk;
            out("\nSTATUS after %lld steps (%.2f h)\n",n,S.elapsed/3600);
            summary(0); havemask=0;
            save_ckpt(); write_stats();
        }
    }
    S.n=n; S.x=x; S.y=y; S.elapsed=now()-t0; S.lastk=lastk; S.prevk=prevk;
    if(stopflag && !trapped) out("\nSTOPPED by signal at n=%lld (continue with --resume)\n",n);
    out("\nsteps done %lld\n", n);
    summary(trapped);
    save_ckpt();
    write_stats();
    prog("%s after %.2f hours; state saved in %s\n",trapped?"trapped":"stopped",S.elapsed/3600,CKPT);
    return 0;
}
