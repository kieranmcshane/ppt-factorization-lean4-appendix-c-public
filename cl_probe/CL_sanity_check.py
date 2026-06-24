import itertools
from math import comb, log
from fractions import Fraction as F

def cyc_count(p):
    n=len(p); seen=[False]*n; c=0
    for i in range(n):
        if not seen[i]:
            c+=1; j=i
            while not seen[j]:
                seen[j]=True; j=p[j]
    return c
def compose(a,b): return tuple(a[b[i]] for i in range(len(b)))
def inv(p):
    q=[0]*len(p)
    for i,pi in enumerate(p): q[pi]=i
    return tuple(q)
def gamma(k,r):
    g=list(range(k*r))
    for blk in range(r):
        base=blk*k
        for j in range(k): g[base+j]=base+(j+1)%k
    return tuple(g)

def hist_full(k,r,do_trans):
    g=gamma(k,r); gi=inv(g); n=k*r
    from collections import Counter
    Mh=Counter(); th=Counter(); ntrans=0; total=0
    for p in itertools.permutations(range(n)):
        total+=1
        cp=cyc_count(p); cgp=cyc_count(compose(g,p)); cpgi=cyc_count(compose(p,gi))
        E=2*k*r+2*r-cgp-cpgi-2*cp
        Mh[(E,cp)]+=1
        if do_trans:
            parent=list(range(n))
            def find(x):
                while parent[x]!=x: parent[x]=parent[parent[x]]; x=parent[x]
                return x
            for i in range(n):
                a=find(i);b=find(p[i])
                if a!=b: parent[a]=b
                a=find(i);b=find(g[i])
                if a!=b: parent[a]=b
            if len(set(find(i) for i in range(n)))==1:
                ntrans+=1; th[cp+(cgp+cpgi)//2-2]+=1
    return Mh,th,ntrans,total

def Mr_val(Mh,k,r,d,lam):  # exact Fraction
    tot=F(0)
    for (E,c),cnt in Mh.items():
        tot+= cnt*(lam**(c-k*r))*F(1,d**E)
    return tot
def b_d_exact(k,lam):
    g1=gamma(k,1); g1i=inv(g1); tot=F(0)
    for p in itertools.permutations(range(k)):
        E=2*k+2-cyc_count(compose(g1,p))-cyc_count(compose(p,g1i))-2*cyc_count(p)
        if E==0: tot+=lam**(cyc_count(p)-k)
    return tot
def Br_exact(k,r,d,lam):
    N=d*d; s=lam*N; rises=F(1)
    for i in range(k*r): rises*=(s+i)
    return F(1,N**r)*rises/(s**(k*r))

for lam in [F(1), F(2)]:
    k=2
    print(f"\n================ k=2, lambda={lam} ================")
    mk=1+F(1,1)/lam
    print(f"m_2={float(mk):.4f}   b_d={float(b_d_exact(k,lam)):.4f} (d-independent for k=2)")
    Mh={}; th={}
    for r in range(1,6):
        Mh[r],th[r],ntr,tot=hist_full(k,r, do_trans=(r<=4))
        if r<=4:
            meant=sum(t*c for t,c in th[r].items())/ntr
            print(f"  r={r} q={k*r}: transitive {100*ntr/tot:.1f}%  mean t={meant:.3f}  2ln(q)={2*log(k*r):.3f}")
    bd=b_d_exact(k,lam)
    print("  R_{r,d}/B_{r,d} (EXACT), watching r-growth and d->inf:")
    for d in [3,10,100,1000,10000]:
        M=[F(1)]+[Mr_val(Mh[r],k,r,d,lam) for r in range(1,6)]
        cells=[]
        for r in range(2,6):
            R=sum(comb(r,j)*((-bd)**(r-j))*M[j] for j in range(r+1))
            B=Br_exact(k,r,d,lam)
            rb=float(R/B)
            cells.append(f"c_{r}={rb:11.4f}")
        print(f"   d={d:>6}: "+"  ".join(cells))
    # growth of even-moment limiting constants
    d=10000; M=[F(1)]+[Mr_val(Mh[r],k,r,d,lam) for r in range(1,6)]
    print("  even-r limiting constants (d=1e4):")
    for r in [2,4]:
        R=sum(comb(r,j)*((-bd)**(r-j))*M[j] for j in range(r+1))
        c=float(R/Br_exact(k,r,d,lam))
        print(f"     c_{r}={c:.4f}  log c_{r}={log(c):.4f}  (log c_r)/r={log(c)/r:.4f}")
