/* Independent check #2 (C, odd-only sieve, different code path): compute a(n) per the upstream definition and report
   a(n) for n in a window around the first positive value after 250000. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(void){ const int B=4000000; char *c=calloc(B,1); /* c[i]=1 means composite, for odd i */
  for(long i=3;i*i<B;i+=2) if(!c[i]) for(long j=i*i;j<B;j+=2*i) c[j]=1;
  int *p=malloc(sizeof(int)*400000); int np=0; p[np++]=2; for(int i=3;i<B;i+=2) if(!c[i]) p[np++]=i;
  long a=0; long firstpos=-1;
  for(int k=2;k<=300000;k++){ int g1=p[k]-p[k-1], g0=(k-1>=1)?p[k-1]-p[k-2]:0; int d=g1-g0; a+= (d>0)-(d<0);
    if(k>250000 && a>0 && firstpos<0){ firstpos=k; printf("first n>250000 with a(n)>0: n=%d a=%ld p_n=%d p_(n-1)=%d p_(n-2)=%d\n",k,a,p[k],p[k-1],p[k-2]); }
    if(k==261150 || k==250000 || k==261149) printf("a(%d)=%ld\n",k,a); }
  printf("primes computed: %d, largest %d\n", np, p[np-1]); return 0; }
