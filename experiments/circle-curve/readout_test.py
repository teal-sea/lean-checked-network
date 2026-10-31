import numpy as np, sys
def wrong(E1,E2,W2,p):
    a=np.repeat(np.arange(p),p); b=np.tile(np.arange(p),p)
    S=((E1[a]+E2[b])**2)@W2.T
    return int((S.argmax(1)!=(a+b)%p).sum())
def onewave(cols,p,H,which,extra=()):
    half=(p-1)//2; out=[c.copy() for c in cols]
    for h in range(H):
        Fs=[np.fft.fft(c[:,h]) for c in cols]
        tot=sum(np.abs(F)**2 for F in Fs); k=int(np.argmax(tot[1:half+1]))+1
        for i,(F,o) in enumerate(zip(Fs,out)):
            if i not in which: continue
            G=np.zeros_like(F); 
            for f in (k,p-k)+tuple(extra): G[f]=F[f]
            o[:,h]=np.round(np.fft.ifft(G).real).astype(np.int64)
    return out
for name in sys.argv[1:]:
    d=np.load(f"final_weights/{name}.npz"); p,H=int(d['p']),int(d['H'])
    cols=[d[k].astype(np.int64) for k in ["E1q","E2q","W2q"]]
    r={"net":wrong(*cols,p),
       "all 1-wave":wrong(*onewave(cols,p,H,{0,1,2}),p),
       "E1,E2 1-wave; W2 full":wrong(*onewave(cols,p,H,{0,1}),p),
       "W2 1-wave; E1,E2 full":wrong(*onewave(cols,p,H,{2}),p),
       "E1,E2 1-wave; W2 wave+DC":wrong(*onewave(cols,p,H,{0,1})[:2]+[onewave(cols,p,H,{2},extra=(0,))[2]],p),
       "E1 1-wave only":wrong(*onewave(cols,p,H,{0}),p),
       "E2 1-wave only":wrong(*onewave(cols,p,H,{1}),p),
    }
    print(name, " | ".join(f"{k}: {v}" for k,v in r.items()))
