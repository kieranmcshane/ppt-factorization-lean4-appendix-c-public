import numpy as np, itertools, math, time
def gamma(k,r):
    g=np.arange(k*r)
    for b in range(r):
        for j in range(k): g[b*k+j]=b*k+(j+1)%k
    return g
def ginv(g):
    q=np.zeros_like(g); q[g]=np.arange(len(g)); return q
def cyc_vec(P,n):
    idx=np.arange(n); mn=np.broadcast_to(idx,P.shape).copy(); cur=mn.copy()
    for _ in range(n):
        cur=np.take_along_axis(P,cur,axis=1); np.minimum(mn,cur,out=mn)
    return (mn==idx).sum(axis=1)
def cyc1(p):
    n=len(p);seen=[False]*n;c=0
    for i in range(n):
        if not seen[i]:
            c+=1;j=i
            while not seen[j]:seen[j]=True;j=p[j]
    return c
def gkset(k):
    g1=gamma(k,1).tolist();g1i=ginv(gamma(k,1)).tolist();S=set()
    def cp(a,b):return tuple(a[b[i]] for i in range(len(b)))
    for p in itertools.permutations(range(k)):
        if 2*k+2-cyc1(cp(g1,p))-cyc1(cp(list(p),g1i))-2*cyc1(p)==0:S.add(p)
    return S
def active(p,g,k,r,G):
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
    for e in roots.values():
        if len(e)==k:
            bs=min(e)
            if bs%k==0 and set(e)==set(range(bs,bs+k)) and all(bs<=p[x]<bs+k for x in e) and tuple(p[bs+j]-bs for j in range(k)) in G:
                return False
    return True
def est_cr(k,r,total,chunk,tlimit,seed=0):
    rng=np.random.default_rng(seed);g=gamma(k,r);gi=ginv(g);gl=g.tolist();n=k*r
    G=gkset(k);target=2*r;const=2*k*r+2*r;hits=0;seen=0;t0=time.time()
    while seen<total and time.time()-t0<tlimit:
        B=chunk
        P=np.argsort(rng.random((B,n)),axis=1).astype(np.int64)
        cP=cyc_vec(P,n); cGP=cyc_vec(g[P],n); cPG=cyc_vec(P[:,gi],n)
        E=const-cGP-cPG-2*cP
        cand=np.where(E==target)[0]
        for c in cand:
            if active(P[c].tolist(),gl,k,r,G):hits+=1
        seen+=B
    return hits/seen*math.factorial(n),hits,seen
print("k=2 planar active count c_r = #{active pi in S_2r with E=2r}:")
for r,tot,ch,tl in [(6,8_000_000,400_000,12),(8,40_000_000,400_000,28)]:
    est,h,s=est_cr(2,r,tot,ch,tl)
    print(f"  r={r}: c_r ~ {est:.0f}  (hits={h}, samples={s}, frac={h/s:.2e})  m={r//2}, c_r/m! = {est/math.factorial(r//2):.1f}")
