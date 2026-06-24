import numpy as np,sys
from math import lgamma
rng=np.random.default_rng(3)
def cg(sh):return (rng.standard_normal(sh)+1j*rng.standard_normal(sh))/np.sqrt(2)
def Zof(Y,d,k):
    N=d*d;B=Y.shape[0]
    W=Y@np.conj(np.swapaxes(Y,1,2))
    WG=np.swapaxes(W.reshape(B,d,d,d,d),1,3).reshape(B,N,N)
    M2=WG@WG
    return (N**(k-1))*np.sum((M2.conj()*M2).real,axis=(1,2))
def betaIS(d,k,x,B,reps):
    N=d*d;s=N;Ns=N*s;tau=9.0+x
    theta=x**(1.0/k)*N**(-1+1.0/k); al=Ns*theta; be=Ns-1.0
    cst=lgamma(al)-lgamma(al+be)+lgamma(1+be)
    Ps=[];Ws=[]
    for _ in range(reps):
        R=rng.beta(al,be,size=B)
        G=cg((B,N,s));G[:,0,0]=0.0
        nr=np.sqrt(np.sum((G.conj()*G).real,axis=(1,2),keepdims=True))
        Y=G/nr*np.sqrt(1.0-R)[:,None,None];Y[:,0,0]=np.sqrt(R)
        Z=Zof(Y,d,k);w=np.exp((1-al)*np.log(R)+cst)
        Ps.append((Z>=tau)*w);Ws.append(w)
    P=np.concatenate(Ps);W=np.concatenate(Ws)
    return P.mean(),(W.sum()**2)/np.sum(W**2)/len(W)*100,al
def naiveP(d,k,tau,B):
    N=d*d;s=N;G=cg((B,N,s));nr=np.sqrt(np.sum((G.conj()*G).real,axis=(1,2),keepdims=True))
    return (Zof(G/nr,d,k)>=tau).mean()
k=4;d=6;N=d*d;a_d=N**(1+1/k);B=6000
print(f"d={d} N={N} a_d={a_d:.1f} k=4  B={B}",flush=True)
for x in [0.5,1.0]:
    pn=naiveP(d,k,9+x,3*B);pi,ess,al=betaIS(d,k,x,B,2)
    print(f" validate x={x}: naive={pn:.3e}  IS={pi:.3e}  ESS={ess:.0f}% al={al:.0f}",flush=True)
print(" x     P_IS       ESS%  rate   x^.25 ratio",flush=True)
for x in [1.0,2.0,4.0,8.0,16.0]:
    pi,ess,al=betaIS(d,k,x,B,2);rate=-np.log(pi)/a_d if pi>0 else float('nan')
    print(f"{x:5.1f} {pi:10.3e} {ess:5.0f} {rate:7.4f} {x**0.25:5.2f} {rate/x**0.25:5.2f}",flush=True)
