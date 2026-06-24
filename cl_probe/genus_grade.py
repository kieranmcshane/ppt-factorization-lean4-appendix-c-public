import itertools
from fractions import Fraction as F
from collections import Counter
def cyc(p):
    n=len(p);seen=[False]*n;c=0
    for i in range(n):
        if not seen[i]:
            c+=1;j=i
            while not seen[j]:seen[j]=True;j=p[j]
    return c
def comp(a,b):return tuple(a[b[i]] for i in range(len(b)))
def inv(p):
    q=[0]*len(p)
    for i,pi in enumerate(p):q[pi]=i
    return tuple(q)
def gamma(k,r):
    g=list(range(k*r))
    for b in range(r):
        for j in range(k):g[b*k+j]=b*k+(j+1)%k
    return tuple(g)
def gk_set(k):
    g1=gamma(k,1);g1i=inv(g1);S=set()
    for p in itertools.permutations(range(k)):
        if 2*k+2-cyc(comp(g1,p))-cyc(comp(p,g1i))-2*cyc(p)==0:S.add(p)
    return S
def orbits(p,g,n):
    par=list(range(n))
    def f(x):
        while par[x]!=x:par[x]=par[par[x]];x=par[x]
        return x
    for i in range(n):
        a,b=f(i),f(p[i]); par[a]=b if a!=b else par[a]
        a,b=f(i),f(g[i]); par[a]=b if a!=b else par[a]
    return [ [i for i in range(n) if f(i)==r] for r in set(f(i) for i in range(n))]
def trivial(elems,p,k,G):
    if len(elems)!=k:return False
    base=min(elems)
    if base%k or set(elems)!=set(range(base,base+k)):return False
    if any(p[e]<base or p[e]>=base+k for e in elems):return False
    return tuple(p[base+j]-base for j in range(k)) in G

def grade(k,r):
    g=gamma(k,r);gi=inv(g);n=k*r;G=gk_set(k)
    tab=Counter()  # (j,h)-> count active ; also weighted by lambda via #pi
    wtab=Counter() # (j,h)-> Counter(#pi)
    for p in itertools.permutations(range(n)):
        comps=orbits(p,g,n)
        if any(trivial(c,p,k,G) for c in comps):continue   # skip non-active
        cpi=len(comps); E=2*k*r+2*r-cyc(comp(g,p))-cyc(comp(p,gi))-2*cyc(p)
        j=r-cpi; h=(E-4*j)//2
        tab[(j,h)]+=1; wtab[(j,h, cyc(p))]+=1
    return tab,wtab

print("=== k=2 active permutations graded by (j=r-c, h=g+g'), E=4j+2h ===")
for r in range(1,6):
    tab,_=grade(2,r)
    if not tab:
        print(f" r={r}: (no active permutations)"); continue
    js=sorted(set(j for j,h in tab)); hs=sorted(set(h for j,h in tab))
    print(f" r={r}: active total={sum(tab.values())}  Emin={min(4*j+2*h for j,h in tab)}")
    for (j,h),c in sorted(tab.items(),key=lambda kv:(4*kv[0][0]+2*kv[0][1],kv[0])):
        print(f"      j={j} h={h}  E={4*j+2*h}:  N={c}")
