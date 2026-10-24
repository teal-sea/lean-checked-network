from pathlib import Path
for p in Path('.').glob('N*/NodeDataNC.lean'):
 s=p.read_text();s=s.replace('open RouteA','open RouteA RouteNC SharedWeights');p.write_text(s)
