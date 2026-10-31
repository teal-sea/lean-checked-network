import numpy as np, sys
def wrong_mask(E1,E2,W2,p):
    a=np.repeat(np.arange(p),p); b=np.tile(np.arange(p),p)
    S=((E1[a]+E2[b])**2)@W2.T
    return (S.argmax(1)!=(a+b)%p), a, b, S
def project(cols,p,H):
    half=(p-1)//2; out=[np.zeros(c.shape,dtype=np.int64) for c in cols]; ks=[]
    for h in range(H):
        Fs=[np.fft.fft(c[:,h]) for c in cols]
        tot=sum(np.abs(F)**2 for F in Fs); k=int(np.argmax(tot[1:half+1]))+1; ks.append(k)
        for F,o in zip(Fs,out):
            G=np.zeros_like(F); G[k]=F[k]; G[p-k]=F[p-k]
            o[:,h]=np.round(np.fft.ifft(G).real).astype(np.int64)
    return out, ks
for name in sys.argv[1:]:
    d=np.load(f"final_weights/{name}.npz"); p,H=int(d['p']),int(d['H'])
    cols=[d[k].astype(np.int64) for k in ["E1q","E2q","W2q"]]
    proj,ks=project(cols,p,H)
    m,a,b,S=wrong_mask(*proj,p); mn,_,_,_=wrong_mask(*cols,p)
    c=(a+b)%p; pred=S.argmax(1)
    byres=np.bincount(c[m],minlength=p); bya=np.bincount(a[m],minlength=p); byb=np.bincount(b[m],minlength=p); byd=np.bincount(((a-b)%p)[m],minlength=p)
    off=np.bincount(((pred-c)%p)[m],minlength=p)
    print(f"\n== {name}: net wrong {mn.sum()}  proj wrong {m.sum()}  distinct freqs {len(set(ks))}  keys {list(d.keys())}")
    for lab,v in [("answer c",byres),("a",bya),("b",byb),("a-b",byd)]:
        o=np.argsort(-v); print(f" by {lab:8s} max {v.max():4d} med {int(np.median(v)):4d} min {v.min():4d}  top {o[:6].tolist()} {v[o[:6]].tolist()}")
    o=np.argsort(-off); print(f" pred-true offset top {o[:6].tolist()} {off[o[:6]].tolist()}  (of {m.sum()})")
    # margin of net on those pairs vs proj
    Sn=((cols[0][a]+cols[1][b])**2)@cols[2].T
    gapn=np.sort(Sn,1); gapn=gapn[:,-1]-gapn[:,-2]
    print(f" net margin on proj-missed pairs: med {int(np.median(gapn[m]))}  vs all pairs med {int(np.median(gapn))}")
    if 'train_mask' in d or 'train_idx' in d:
        print(" has train split info")
