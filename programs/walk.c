// generic "lowest unvisited square" walk on the square spiral for a leaper compound.
// usage: walk LETTERS N H   LETTERS from W(0,1) F(1,1) D(0,2) N(1,2) A(2,2)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
typedef long long ll;
static inline ll spiral(ll x, ll y){ ll ax=x<0?-x:x, ay=y<0?-y:y, r=ax>ay?ax:ay; if(!r) return 1; ll b=(2*r-1)*(2*r-1);
  if(x==r&&y>-r) return b+(y+r); if(y==r) return b+2*r+(r-x); if(x==-r) return b+4*r+(r-y); return b+6*r+(x+r); }
static unsigned char *bits; static ll H,W;
static inline size_t idx(ll x,ll y){ return (size_t)(y+H)*(size_t)W+(size_t)(x+H); }
static inline int get(ll x,ll y){ size_t i=idx(x,y); return (bits[i>>3]>>(i&7))&1; }
static inline void set(ll x,ll y){ size_t i=idx(x,y); bits[i>>3]|=(unsigned char)(1u<<(i&7)); }
int main(int c,char**v){
  const char*L=v[1]; ll N=atoll(v[2]); H=atoll(v[3]); W=2*H+1;
  int mx[64],my[64],nm=0;
  for(const char*p=L;*p;p++){ int a,b; switch(*p){case 'W':a=0;b=1;break;case 'F':a=1;b=1;break;case 'D':a=0;b=2;break;case 'N':a=1;b=2;break;default:a=2;b=2;}
    for(int sx=-1;sx<=1;sx+=2)for(int sy=-1;sy<=1;sy+=2)for(int sw=0;sw<2;sw++){ int dx=sw?b:a, dy=sw?a:b; dx*=sx; dy*=sy; int dup=0; for(int k=0;k<nm;k++) if(mx[k]==dx&&my[k]==dy) dup=1; if(!dup){mx[nm]=dx;my[nm]=dy;nm++;} } }
  size_t nb=(((size_t)W*(size_t)W)>>3)+1; bits=mmap(NULL,nb,PROT_READ|PROT_WRITE,MAP_PRIVATE|MAP_ANONYMOUS|MAP_NORESERVE,-1,0);
  ll x=0,y=0,n=1; set(0,0); ll hist[65]; memset(hist,0,sizeof hist); int minfree=99; ll minfreeat=0; ll maxring=0;
  for(;n<N;){
    ll best=-1,bx=0,by=0;
    for(int k=0;k<nm;k++){ ll qx=x+mx[k],qy=y+my[k]; if(get(qx,qy)) continue; ll s=spiral(qx,qy); if(best<0||s<best){best=s;bx=qx;by=qy;} }
    if(best<0){ printf("%-5s moves %2d: TRAPPED at step %lld on square %lld\n",L,nm,n,spiral(x,y)); return 0; }
    x=bx;y=by;n++; set(x,y); ll r=llabs(x)>llabs(y)?llabs(x):llabs(y); if(r>maxring) maxring=r;
    if(r>H-6){ printf("%-5s moves %2d: board limit at step %lld (ring %lld), not trapped; lowest free count so far %d (first at step %lld)\n",L,nm,n,r,minfree,minfreeat); return 0; }
    int fc=0; for(int k=0;k<nm;k++) if(!get(x+mx[k],y+my[k])) fc++; hist[fc]++; if(fc<minfree && n>50){minfree=fc;minfreeat=n;}
  }
  printf("%-5s moves %2d: not trapped after %lld steps (ring %lld); lowest free count %d, first at step %lld, %lld times; free-count histogram low end:",L,nm,n,maxring,minfree,minfreeat,hist[minfree]);
  for(int i=0;i<=3&&i<=nm;i++) printf(" %d:%lld",i,hist[i]); printf("\n"); return 0; }
