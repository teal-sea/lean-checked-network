"""Prepare a binary32 enclosure for producer search. The theorem keeps exact decimals."""
from pathlib import Path
from fractions import Fraction
from decimal import Decimal
import struct,re
p=Path(__file__).resolve().parents[1]/'inputs/prop_1.vnnlib'
def bound(m):
 op,i,s=m.groups();v=struct.unpack('<f',struct.pack('<f',float(s)))[0]
 if (Fraction(v)<Fraction(s)) if op=='<=' else (Fraction(v)>Fraction(s)):
  bits=struct.unpack('<I',struct.pack('<f',v))[0]
  bits+= (1 if v>=0 else -1)*(1 if op=='<=' else -1)
  v=struct.unpack('<f',struct.pack('<I',bits))[0]
 return f'(assert ({op} X_{i} {Decimal(v)}))'
s=re.sub(r'\(assert \((<=|>=) X_(\d) ([-\d.]+)\)\)',bound,p.read_text())
p.with_name('prop-1-outward.vnnlib').write_text(s)
