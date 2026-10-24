#!/usr/bin/env python3
"""Fetch the original benchmark files and reject unexpected decompressed bytes."""
import gzip,hashlib,urllib.request
from pathlib import Path
REV='d9e7b2feeaf534dcc557729ee7c920bd5b97099c'
BASE=f'https://raw.githubusercontent.com/VNN-COMP/vnncomp2023_benchmarks/{REV}/benchmarks/acasxu/'
FILES={
 'ACASXU_run2a_1_1_batch_2000.onnx':('onnx/ACASXU_run2a_1_1_batch_2000.onnx.gz','843f7110bf5a8b7f0eeb9b1c548d9d558db9099328b392423d5a7444a0656dd4'),
 'prop_1.vnnlib':('vnnlib/prop_1.vnnlib.gz','7a9a9930711817c6cc39940f5c1d0f8c51f2ed82f38e203c4b5de03c19bd4ced')}
def main():
 out=Path(__file__).resolve().parents[1]/'inputs';out.mkdir(exist_ok=True)
 for name,(url,digest) in FILES.items():
  dest=out/name
  raw=dest.read_bytes() if dest.exists() else gzip.decompress(urllib.request.urlopen(BASE+url,timeout=60).read())
  if hashlib.sha256(raw).hexdigest()!=digest:raise ValueError('wrong input hash: '+name)
  dest.write_bytes(raw);print(digest+'  '+name)
if __name__=='__main__':main()
