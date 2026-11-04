"""Create two single-purpose mutants of the pinned weight file and generate their Lean.
head: head[8][5] 9 -> 7.5 (the comment logit 18 -> 15 after doubling): comment now loses to preprocessor.
kw  : the two biases of the threshold pair for the keyword `do` shift by one (hash constant 271 -> 270)."""
import json, pathlib, struct, sys, subprocess
ROOT=pathlib.Path(__file__).resolve().parent
OUT=pathlib.Path(sys.argv[1]).resolve()   # output directory for the mutant trees
ONLY=sys.argv[2] if len(sys.argv)>2 else None
sys.path.insert(0,str(ROOT))
from exact import WEIGHTS
raw=WEIGHTS.read_bytes(); pos=8
def ints(n):
    global pos
    v=struct.unpack_from('<'+'q'*n,raw,pos); pos+=8*n; return v
nf,nfs,nfo,nbs,nc,hc=ints(6)
pos+=128*nf*8
offs={}
def cell(name):
    global pos
    (nl,)=ints(1)
    for li in range(nl):
        r,c,s=ints(3)
        offs[(name,li,'W')]=pos; pos+=r*c*8
        offs[(name,li,'b')]=pos; pos+=r*8
        pos+=r*8; pos+=s*8
cell('fwd'); cell('bwd')
pos+=(nfs+nfo+nbs)*8+nfs*8
head=pos
def dbl(off): return struct.unpack_from('<d',raw,off)[0]
muts={}
# head mutant
o=head+(8*hc+5)*8; assert dbl(o)==9.0
b=bytearray(raw); struct.pack_into('<d',b,o,7.5); muts['head']=(b,dict(kind='head coefficient',where=f'head[8][5]',before=9.0,after=7.5,byte_offset=o))
# keyword threshold mutant: layer 3 rows 12 and 13 biases (-270, 272) -> (-271, 273)
o12=offs[('fwd',3,'b')]+12*8; o13=offs[('fwd',3,'b')]+13*8
assert (dbl(o12),dbl(o13))==(-270.0,272.0)
b=bytearray(raw); struct.pack_into('<d',b,o12,-271.0); struct.pack_into('<d',b,o13,273.0)
muts['kw']=(b,dict(kind='keyword threshold pair (hash constant 271 = "do" -> 270)',where='fwd layer 3 rows 12,13 biases',before=[-270.0,272.0],after=[-271.0,273.0],byte_offsets=[o12,o13]))
for k,(b,info) in muts.items():
    if ONLY and k!=ONLY: continue
    d=OUT/f'mutant-{k}'; (d/'lean').mkdir(parents=True,exist_ok=True)
    (d/'weights.bin').write_bytes(b)
    subprocess.check_call(['python3','-I','-B','gen_lean.py','--weights',str(d/'weights.bin'),'--out',str(d/'lean/Pilot.lean')],cwd=ROOT,stdout=subprocess.DEVNULL)
    subprocess.check_call(['python3','-I','-B','gen_extra.py','--weights',str(d/'weights.bin'),'--out',str(d/'lean/NetExtra.lean')],cwd=ROOT,stdout=subprocess.DEVNULL)
    (d/'info.json').write_text(json.dumps(info,indent=1))
    print(k,info)
