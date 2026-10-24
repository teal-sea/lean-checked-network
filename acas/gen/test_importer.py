"""Small independent decoder audit and rejection controls; stdlib only."""
import unittest, struct, json
from pathlib import Path
from fractions import Fraction
import importer as I

ROOT=Path(__file__).resolve().parent
RAW=(ROOT.parent/'inputs/ACASXU_run2a_1_1_batch_2000.onnx').read_bytes()
PROP=(ROOT.parent/'inputs/prop_1.vnnlib').read_bytes()

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
        a=json.loads((ROOT/'agreement.json').read_text())
        self.assertEqual(len({tuple(x) for x in a['inputs']}),20)

if __name__=='__main__': unittest.main(verbosity=2)

class ReleaseBindingTests(unittest.TestCase):
    def test_frozen_statement_bytes(self):
        original=(ROOT.parent/'lean/ACASChecked/Spec.lean').read_bytes().replace(b'import ACASChecked.Net',b'import Net')
        self.assertEqual(I.sha(original),'fc9a750a19646c2e66ced81bb8138620861b4c01e1fd0cd9b85baf1030e1a9b0')
    def test_actual_unsafe_weight_counterexample(self):
        c=json.loads((ROOT.parent/'producer/crownint-weight-mutation.json').read_text())
        import copy
        base=json.loads((ROOT.parent/'producer/certificate.json').read_text())
        changed=copy.deepcopy(base['layers']);changed[6]['w'][0][25]=1000000
        self.assertEqual(c['layers'],changed)
        x=list(map(Fraction,['10736225/16777216','-3/8','-1/4','15938355/33554432','-15938355/33554432']))
        lo,hi,th=I.property_data(PROP)
        box=c['nodes'][13]['box']
        self.assertTrue(all(Fraction(l)<=v<=Fraction(u) for l,v,u in zip(box[0],x,box[1])))
        self.assertTrue(all(Fraction(l)<=v<=Fraction(u) for l,v,u in zip(lo,x,hi)))
        for k,layer in enumerate(c['layers']):
            x=[sum((Fraction(w)*v for w,v in zip(row,x)),Fraction(b)) for row,b in zip(layer['w'],layer['b'])]
            if k<6:x=[max(Fraction(0),v) for v in x]
        self.assertGreaterEqual(x[0],Fraction(th))
        self.assertEqual(str(x[0]),'617395803471793988437503247185622853024376841368134534849805963880125184371/3450873173395281893717377931138512726225554486085193277581262111899648')
