"""Small independent decoder audit and rejection controls; stdlib only."""
import unittest, struct, json
from pathlib import Path
from fractions import Fraction
import importer as I

RAW=Path('ACASXU_run2a_1_1_batch_2000.onnx').read_bytes()
PROP=Path('prop_1.vnnlib').read_bytes()

def varint(n):
    r=bytearray()
    while n>127: r.append((n&127)|128); n>>=7
    return bytes(r)+bytes([n])
def tensor(bits, dims=(1,)):
    raw=b''.join(struct.pack('<I',v) for v in bits)
    return b''.join(b'\x08'+varint(d) for d in dims)+b'\x10\x01'+b'\x42\x01t'+b'\x4a'+varint(len(raw))+raw

class ImportTests(unittest.TestCase):
    def test_all_original_float32_bits(self):
        _,_,ts=I.decode(RAW)
        for t in ts.values():
            for bit,q in zip(t['bits'],t['values']):
                f=struct.unpack('<f',struct.pack('<I',int(bit,16)))[0]
                self.assertEqual(q,Fraction.from_float(f))
    def test_float_edge_encodings(self):
        bits=[0,0x80000000,1,0x80000001,0x007fffff,0x00800000,0x7f7fffff]
        _,t=I.tensor(tensor(bits,(len(bits),)))
        for b,q in zip(bits,t['values']):
            self.assertEqual(q,Fraction.from_float(struct.unpack('<f',struct.pack('<I',b))[0]))
    def test_nonfinite_rejected(self):
        for b in [0x7f800000,0xff800000,0x7fc00000]:
            with self.assertRaises(ValueError): I.tensor(tensor([b]))
    def test_bad_tensor_length(self):
        with self.assertRaises(ValueError): I.tensor(tensor([0],(2,)))
    def test_unsupported_operator(self):
        with self.assertRaises(ValueError): I.decode(RAW.replace(b'Relu',b'Tanh',1))
    def test_broken_wiring(self):
        with self.assertRaises(ValueError): I.decode(RAW.replace(b'relu_1',b'relu_9',1))
    def test_property_changed_decimal(self):
        with self.assertRaises(ValueError): I.property_data(PROP.replace(b'3.991125645861615',b'3.991125645861616'))
    def test_property_extra_assertion(self):
        with self.assertRaises(ValueError): I.property_data(PROP+b'\n(assert (>= Y_1 0))')
    def test_property_exact_tokens(self):
        lo,hi,t=I.property_data(PROP)
        self.assertEqual((lo[0],hi[0],t),('0.6','0.679857769','3.991125645861615'))
    def test_wrong_source_hash(self):
        with self.assertRaises(ValueError): I.validate_sources(RAW[:-1]+bytes([RAW[-1]^1]),PROP)
        with self.assertRaises(ValueError): I.validate_sources(RAW,PROP+b' ')
    def test_input_vectors_unique(self):
        a=json.loads(Path('agreement.json').read_text())
        self.assertEqual(len({tuple(x) for x in a['inputs']}),20)

if __name__=='__main__': unittest.main(verbosity=2)
