"""Generate lean/NetExtra.lean: dependency slices of the forward cell and the keyword/type/constant
table structure, all read from the pinned weight file (optionally a mutated copy). Each slice is
linked to the full generated cell by `rfl`, so nothing is assumed."""
import argparse, pathlib, sys
ROOT=pathlib.Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT))
from exact import Model, WEIGHTS
ap=argparse.ArgumentParser(); ap.add_argument('--weights',default=str(WEIGHTS)); ap.add_argument('--out',default=str(ROOT/'lean/NetExtra.lean'))
a=ap.parse_args()
m=Model(a.weights)
def integer(n):
    assert int(n)==n
    return str(int(n)) if n>=0 else f'({int(n)})'
def lst(xs): return '['+', '.join(map(str,xs))+']'
def graph(cell, inputs, prefix):
    nodes={}; v=inputs
    for li,l in enumerate(cell):
        out=[]
        for ri,(row,b,hi) in enumerate(zip(l['W'],l['b'],l['hi'])):
            name=f'{prefix}{li}_{ri}'
            terms=[f'({integer(w)} * {v[i]})' for i,w in enumerate(row) if w]
            expr=f'max (0 : Int) ({" + ".join([integer(b)]+terms)})'
            if hi!=float('inf'): expr=f'min {integer(hi)} ({expr})'
            deps=[v[i] for i,w in enumerate(row) if w and v[i] in nodes]
            nodes[name]=(expr,deps); out.append(name)
        v=out+[v[i] for i in l['skip']]
    return nodes,v
ins=[f'(x.flags.getD {i} 0)' for i in range(13)]+['x.code']
hs=[f'(h.auto.getD {i} 0)' for i in range(13)]+['h.W','h.N','h.d','h.h1','h.h2']
nodes,v=graph(m.fwd,ins+hs,'f')
state=[v[i] for i in m.fs]; fout=[v[i] for i in m.fo]
L=['import lean.Pilot','import lean.Units','namespace Lexnet','open Units','set_option maxRecDepth 100000','set_option maxHeartbeats 0']
def slice_(name,sig,ret,needed,repl,body,stop=()):
    seen=set()
    def visit(n):
        if n in seen or n not in nodes or n in stop: return
        seen.add(n)
        for d in nodes[n][1]: visit(d)
    for n in needed: visit(n)
    L.append(f'def {name} {sig} : {ret} :=')
    for nm,(expr,_) in nodes.items():
        if nm in seen:
            for o,n in repl: expr=expr.replace(o,n)
            L.append(f'  let {nm} := {expr}')
    L.append('  '+body)
# hash slice: (d', h1', h2')
repl=[('(x.flags.getD 2 0)','wc'),('x.code','code'),('h.W','W'),('h.d','d'),('h.h1','h1'),('h.h2','h2')]
slice_('hashStep','(wc code W d h1 h2 : Int)','Int × Int × Int',[state[15],state[16],state[17]],repl,f'({state[15]}, {state[16]}, {state[17]})')
assert state[15]=='f0_12' and state[16]=='f2_0' and state[17]=='f2_1', state[15:]
L.append('theorem hash_link (x : Features) (h : FState) :')
L.append('    ((forward x h).1.d, (forward x h).1.h1, (forward x h).1.h2) = hashStep (x.flags.getD 2 0) x.code h.W h.d h.h1 h.h2 := by rfl')
# W,N slice
repl=[('x.flags','x'),('h.auto','h'),('h.W','hW'),('h.N','hN')]
slice_('wnStep','(x : List Int) (h : AState) (hW hN : Int)','Int × Int',[state[13],state[14]],repl,f'({state[13]}, {state[14]})')
L.append('theorem wn_link (x : Features) (h : FState) :')
L.append('    ((forward x h).1.W, (forward x h).1.N) = wnStep x.flags h.auto h.W h.N := by rfl')
# opener
slice_('openStep','(x : List Int) (h : AState)','Int',[fout[10]],[('x.flags','x'),('h.auto','h')],fout[10])
L.append('theorem open_link (x : Features) (h : FState) :')
L.append('    (forward x h).2.getD 10 0 = openStep x.flags h.auto := by rfl')
# flags: unrolled slice from f2_0,f2_1
fnodes={k:v for k,v in nodes.items()}
slice_('flagsOf','(f2_0 f2_1 : Int)','Int × Int × Int',[fout[7],fout[8],fout[9]],[],f'({fout[7]}, {fout[8]}, {fout[9]})',stop=('f2_0','f2_1'))
assert fout[7:10]==['f5_0','f5_1','f5_2']
# structure of layers 3 and 4
l3=m.fwd[3]; l4=m.fwd[4]; l5=m.fwd[5]
unit={}
for r in range(162):
    nz=[(i,w) for i,w in enumerate(l3['W'][r]) if w]; assert len(nz)==1 and l3['hi'][r]==1
    col,w=nz[0]; assert col in (0,1) and abs(w)==1
    unit[r]=(col,w,int(l3['b'][r]))
def pairc(k):
    c0,w0,p=unit[2*k]; c1,w1,q=unit[2*k+1]
    assert c0==c1 and w0==1 and w1==-1 and q==2-p
    return c0,1-p
rowsA={};rowsP={}
for r,(row,b,hi) in enumerate(zip(l4['W'],l4['b'],l4['hi'])):
    nz=[(i,w) for i,w in enumerate(row) if w]; assert hi==1
    idx=[i for i,w in nz if i<162]; assert all(w==1 for i,w in nz if i<162)
    ks=[]
    for i in idx:
        if i%2==0:
            assert (i+1) in idx; ks.append(i//2)
    assert len(idx)==2*len(ks)
    pcs=[pairc(k) for k in ks]
    extra=[(i,w) for i,w in nz if i>=162]
    if extra:
        assert extra==[(163,-1)] and all(c==0 for c,_ in pcs) and b==-len(pcs)
        rowsA[r]=[c for _,c in pcs]
    else:
        assert b==-3 and len(pcs)==2 and sorted(c for c,_ in pcs)==[0,1]
        ca=[c for cc,c in pcs if cc==0][0]; cb=[c for cc,c in pcs if cc==1][0]
        order='AB' if pcs[0][0]==0 else 'BA'
        rowsP[r]=(order,ca,cb)
assert sorted(rowsA)==[0,7,10] and sorted(rowsP)==[1,2,3,4,5,6,8,9]
for r in (0,7,10): L.append(f'def tab{r} : List Int := {lst(map(integer,rowsA[r]))}')
def rowexpr(r):
    if r in rowsA: return f'rowA tab{r} f2_0 f2_1'
    o,ca,cb=rowsP[r]
    return f'rowAB {integer(ca)} {integer(cb)} f2_0 f2_1' if o=='AB' else f'rowBA {integer(cb)} {integer(ca)} f2_1 f2_0'
for r,row in enumerate(l5['W']):
    assert l5['b'][r]==0 and l5['hi'][r]==1
groups=[[i for i,w in enumerate(row) if w] for row in l5['W']]
assert groups==[[0,1,2,3,4,5,6],[7,8,9],[10]]
for gi,g_ in enumerate(groups):
    L.append(f'def grp{gi}Rows (A B : Int) : List Int := [{", ".join(rowexpr(r).replace("f2_0","A").replace("f2_1","B") for r in g_)}]')
L.append('def flagsS (f2_0 f2_1 : Int) : Int × Int × Int :=')
for gi,g_ in enumerate(groups):
    L.append(f'  let g{gi} := clip1 (lin 0 ((grp{gi}Rows f2_0 f2_1).map fun r => (1, r)))')
L.append('  (g0, g1, g2)')
L.append('theorem flags_link (A B : Int) : flagsOf A B = flagsS A B := by rfl')
# semantic characterisation
def P(rs): return '['+', '.join(f'({integer(ca)}, {integer(cb)})' for (_,ca,cb) in rs)+']'
L.append('def kwP : List (Int × Int) := '+P([rowsP[r] for r in (1,2,3,4,5,6)]))
L.append('def tyP : List (Int × Int) := '+P([rowsP[r] for r in (8,9)]))
def char(name,gi,rowsAr,pairs):
    rows=groups[gi]
    L.append(f'theorem {name} (A B : Int) (hB : 0 ≤ B) : (flagsOf A B).{["1","2.1","2.2"][gi]} = 1 ↔ ' + (f'((A ∈ tab{rowsAr} ∧ B = 0) ∨ (A, B) ∈ {pairs})' if pairs else f'(A ∈ tab{rowsAr} ∧ B = 0)') + ' := by')
    L.append('  rw [flags_link]')
    L.append(f'  show clip1 (lin 0 ((grp{gi}Rows A B).map fun r => (1, r))) = 1 ↔ _')
    L.append(f'  have e0 := rowA_iff tab{rowsAr} (by decide) A B hB')
    L.append(f'  have z0 := rowA_01 tab{rowsAr} A B')
    for r in rows:
        if r in rowsP:
            o,ca,cb=rowsP[r]
            if o=='AB':
                L.append(f'  have e{r} := rowAB_iff {integer(ca)} {integer(cb)} A B'); L.append(f'  have z{r} := rowAB_01 {integer(ca)} {integer(cb)} A B')
            else:
                L.append(f'  have e{r} := rowBA_iff {integer(cb)} {integer(ca)} B A'); L.append(f'  have z{r} := rowBA_01 {integer(cb)} {integer(ca)} B A')
    L.append(f'  rw [grp_iff _ (by simp only [grp{gi}Rows, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact {("z0" if len(rows)==1 else "⟨"+", ".join(("z0" if r in rowsA else f"z{r}") for r in rows)+"⟩")})]')
    args=['grp%dRows'%gi,'List.mem_cons','List.not_mem_nil','or_false','exists_eq_or_imp','exists_eq_left','e0']+[f'e{r}' for r in rows if r in rowsP]+(['kwP' if pairs=='kwP' else 'tyP','Prod.mk.injEq'] if pairs else [])
    L.append('  simp only ['+', '.join(args)+']')
char('kw_char',0,0,'kwP'); char('ty_char',1,7,'tyP'); char('const_char',2,10,None)
L.append('end Lexnet')
pathlib.Path(a.out).write_text('\n'.join(L)+'\n')
print('rowsA sizes',{r:len(c) for r,c in rowsA.items()},'rowsP',rowsP)
