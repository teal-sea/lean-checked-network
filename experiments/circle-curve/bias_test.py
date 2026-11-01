import numpy as np, sys
def logits(E1,E2,W2,p):
    a=np.repeat(np.arange(p),p); b=np.tile(np.arange(p),p)
    return ((E1[a]+E2[b])**2)@W2.T, (a+b)%p
def proj(cols,p,H,keep_fn):
    half=(p-1)//2; out=[np.zeros(c.shape,dtype=np.int64) for c in cols]; ks=[]
    for h in range(H):
        Fs=[np.fft.fft(c[:,h]) for c in cols]
        tot=sum(np.abs(F)**2 for F in Fs); k=int(np.argmax(tot[1:half+1]))+1; ks.append(k)
        for i,(F,o) in enumerate(zip(Fs,out)):
            G=np.zeros_like(F)
            for f in keep_fn(i,k,F): G[f]=F[f]
            o[:,h]=np.round(np.fft.ifft(G).real).astype(np.int64)
    return out, ks
for name in sys.argv[1:]:
    d=np.load(f"final_weights/{name}.npz"); p,H=int(d['p']),int(d['H'])
    cols=[d[k].astype(np.int64) for k in ["E1q","E2q","W2q"]]
    one,ks=proj(cols,p,H,lambda i,k,F:(k,p-k))
    S1,c=logits(*one,p); w1=int((S1.argmax(1)!=c).sum())
    # residual readout = full W2 minus its one-wave part
    W2res=cols[2]-one[2]
    # constant part of each neuron's squared activation under one-wave embeddings
    a=np.repeat(np.arange(p),p); b=np.tile(np.arange(p),p)
    act=(one[0][a]+one[1][b])**2
    actmean=act.mean(0)
    bias=W2res@actmean          # bias[c]
    Sb=S1+bias[None,:]; wb=int((Sb.argmax(1)!=c).sum())
    # exact contribution of residual readout, split into mean part and fluctuating part
    full_res=act@W2res.T
    Sf=S1+full_res; wf=int((Sf.argmax(1)!=c).sum())
    fluct=full_res-bias[None,:]
    print(f"{name}: 1-wave {w1} | +bias from residual readout x mean activation {wb} | +full residual readout {wf} | bias range {int(bias.min())}..{int(bias.max())} vs 1-wave logit gap med {int(np.median(np.sort(S1,1)[:,-1]-np.sort(S1,1)[:,-2]))} | fluct std {int(fluct.std())}")
    # how many W2 waves per neuron are needed if we instead keep top-m W2 frequencies
    for m in (2,3,5,8):
        def keep(i,k,F,m=m):
            if i<2: return (k,p-k)
            P=np.abs(F)**2; P2=P[:(p+1)//2].copy(); idx=np.argsort(-P2)[:m]
            return tuple(set(int(j) for j in idx)|set((p-int(j))%p for j in idx))
        o,_=proj(cols,p,H,keep); S,c2=logits(*o,p); print(f"   W2 top-{m} freqs (incl DC) per neuron: wrong {int((S.argmax(1)!=c2).sum())}")
    # is the residual W2 energy at frequencies that are OTHER neurons' dominant k?
    kset=set(ks); Fres=np.fft.fft(W2res,axis=0); P=np.abs(Fres)**2
    tot=P[1:(p+1)//2].sum(); inK=sum(P[k].sum() for k in kset); print(f"   residual W2 energy at the net's own {len(kset)} freqs: {inK/tot:.2f}  (chance {2*len(kset)/(p-1):.2f}); DC share {P[0].sum()/P.sum():.2f}")
