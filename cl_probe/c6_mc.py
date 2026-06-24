import numpy as np,random
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
    for i,x in enumerate(p):q[x]=i
    return tuple(q)
def gamma(k,r):
    g=list(range(k*r))
    for b in range(r):
        for j in range(k):g[b*k+j]=b*k+(j+1)%k
    return tuple(g)
def gkset(k):
    g1=gamma(k,1);g1i=inv(g1);S=set()
    import itertools
    for p in itertools.permutations(range(k)):
        if 2*k+2-cyc(comp(g1,p))-cyc(comp(p,g1i))-2*cyc(p)==0:S.add(p)
    return S
def ncomp_and_active(p,g,k,r,G):
    n=k*r;par=list(range(n))
    def f(x):
        while par[x]!=x:par[x]=par[par[x]];x=par[x]
        return x
    for i in range(n):
        a,b=f(i),f(p[i])
        if a!=b:par[a]=b
        a,b=f(i),f(g[i])
        if a!=b:par[a]=b
    roots={}
    for i in range(n):roots.setdefault(f(i),[]).append(i)
    # active: no trivial block (single k-block orbit with restriction in G)
    for elems in roots.values():
        if len(elems)==k:
            base=min(elems)
            if base%k==0 and set(elems)==set(range(base,base+k)) and all(base<=p[e]<base+k for e in elems):
                if tuple(p[base+j]-base for j in range(k)) in G:
                    return len(roots),False
    return len(roots),True
import math
def c_r_mc(k,r,nsamp,seed=0):
    rng=random.Random(seed);g=gamma(k,r);gi=inv(g);n=k*r;G=gkset(k)
    base=list(range(n));target=2*r;hit=0
    for _ in range(nsamp):
        p=base[:];rng.shuffle(p);p=tuple(p)
        E=2*k*r+2*r-cyc(comp(g,p))-cyc(comp(p,gi))-2*cyc(p)
        if E!=target:continue
        nc,act=ncomp_and_active(p,g,k,r,G)
        if act:hit+=1
    frac=hit/nsamp
    return frac*math.factorial(n),hit,frac
# validate on r=4 (exact c_4=972) then r=6
for r,ns in [(4,300000),(6,1500000)]:
    est,hit,frac=c_r_mc(2,r,ns)
    print(f"k=2 r={r}: c_r MC-est = {est:.1f}  (hits={hit}, frac={frac:.4%}, of {math.factorial(2*r)})")
print("exact: c_2=18, c_4=972")
