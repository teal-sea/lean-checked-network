"""Draw the circle from the real weights (no plotting library needed; writes SVG).

Left: one neuron's 113 input weights E1[a, h] against a, with its best-fitting wave.
Right: the 4 neurons that share frequency 11, embedding of every number a in their 4 weights,
projected onto the two directions of largest variation (computed from the data, no circle
assumed). The 113 numbers land on a circle, and a -> a+1 always turns by the same angle.

Usage: python3 figure.py network/trained.npz figures/circle.svg
"""
import sys
import numpy as np

t = np.load(sys.argv[1]); p = int(t["p"])
E1 = t["E1q"].astype(float)
cols = [t[k].astype(float) for k in ["E1q", "E2q", "W2q"]]
half = (p - 1) // 2
freq = {}
for h in range(E1.shape[1]):
    if not np.any(cols[0][:, h]) and not np.any(cols[2][:, h]):
        continue
    tot = sum((np.abs(np.fft.fft(c[:, h])) ** 2)[1:half + 1] + (np.abs(np.fft.fft(c[:, h])) ** 2)[p - 1:p - half - 1:-1] for c in cols)
    freq[h] = int(np.argmax(tot)) + 1
k = 11
group = [h for h, f in freq.items() if f == k]
h0 = group[0]

W, Hh, pad = 920, 390, 50
out = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {Hh}" font-family="sans-serif" font-size="13">',
       f'<rect width="{W}" height="{Hh}" fill="white"/>']
# left panel
x0, y0, w, hgt = pad, 40, 400, 320
y = E1[:, h0]
F = np.fft.fft(y); fitw = (2 * F[k] / p * np.exp(2j * np.pi * k * np.arange(p) / p)).real
lim = max(np.abs(y).max(), np.abs(fitw).max()) * 1.1
X = lambda a: x0 + w * a / (p - 1)
Y = lambda v: y0 + hgt / 2 - (hgt / 2) * v / lim
out.append(f'<line x1="{x0}" y1="{Y(0)}" x2="{x0 + w}" y2="{Y(0)}" stroke="#bbb"/>')
xs = np.linspace(0, p - 1, 800)
fw = (2 * F[k] / p * np.exp(2j * np.pi * k * xs / p)).real
out.append('<polyline fill="none" stroke="#e07a5f" stroke-width="1.5" points="' + " ".join(f"{X(a):.1f},{Y(v):.1f}" for a, v in zip(xs, fw)) + '"/>')
for a in range(p):
    out.append(f'<circle cx="{X(a):.1f}" cy="{Y(y[a]):.1f}" r="2.6" fill="#3d5a80"/>')
out.append(f'<text x="{x0}" y="24" font-weight="bold">One neuron: its weight for each input a = 0..{p - 1}</text>')
out.append(f'<text x="{x0}" y="{y0 + hgt + 24}" fill="#555">dots: the trained weights. line: a wave of frequency {k}</text>')
# right panel: PCA of the frequency-11 group's embedding
G = E1[:, group] - E1[:, group].mean(0)
U_, S_, Vt = np.linalg.svd(G, full_matrices=False)
P2 = U_[:, :2] * S_[:2]
cx, cy, r = 470 + 220, 40 + 160, 150
sc = r / np.abs(P2).max()
for a in range(p):
    out.append(f'<circle cx="{cx + sc * P2[a, 0]:.1f}" cy="{cy - sc * P2[a, 1]:.1f}" r="2.6" fill="#3d5a80"/>')
for a in [0, 1, 2, 3]:
    out.append(f'<text x="{cx + sc * P2[a, 0] * 1.13:.1f}" y="{cy - sc * P2[a, 1] * 1.13 + 4:.1f}" text-anchor="middle" fill="#e07a5f" font-weight="bold">{a}</text>')
out.append(f'<text x="{470}" y="24" font-weight="bold">{len(group)} neurons of frequency {k}: all {p} numbers sit on a circle</text>')
out.append(f'<text x="{470}" y="{y0 + hgt + 24}" fill="#555">each step a → a+1 turns by the same angle, {k}/{p} of a full turn</text>')
out.append("</svg>")
open(sys.argv[2], "w").write("\n".join(out))
var2 = (S_[:2] ** 2).sum() / (S_ ** 2).sum()
print(f"wrote {sys.argv[2]}; neuron {h0}; group {group}; top-2 directions hold {var2:.3f} of the group's variation")
