"""Train the repo's one-layer transformer (transformer/train.py, Nanda et al. 2023's model) on
(a + b) mod 113 with dense checkpoints and none of train.py's stop rule, margin phase or fallback.

Usage: python3 train_curve.py OUT_DIR --wd 0 --seed 0 [--frac 0.3] [--epochs 20000]
       [--shuffle-labels] [--threads 2] [--eval-every 50]

Same model class (imported unchanged), initialisation (torch.manual_seed(seed), then
Transformer()), optimiser (AdamW, lr 1e-3, betas 0.9 / 0.98, full batch) and split rule
(np.random.default_rng(seed).permutation) as transformer/train.py. Deliberate differences:
no stop rule, no margin phase, no fallback (train.py merges the held-out pairs into training after
2 hours, which would corrupt a memorizing run), checkpoints on the fixed schedule SCHEDULE from
epoch 0, all-pairs evaluation only every --eval-every epochs. --shuffle-labels permutes the
training labels among the training pairs (the control of experiments/circle-curve/train_ckpt2.py).

Output: OUT_DIR/ckpt_EEEEEE.npz in train.py's format (the 11 float64 weights tok, pos, WQ, WK, WV,
WO, Win, bin, Wout, bout, U, plus epoch and train_idx; transformer/int_transformer.py reads it),
with labels (the training targets used), seed, wd, frac, shuffled; OUT_DIR/curve.tsv: epoch, train
loss, train accuracy (against the labels trained on), held-out accuracy (against (a + b) mod 113),
wrong pairs of 12,769, seconds; OUT_DIR/DONE when finished."""
import argparse
import sys
import time
from pathlib import Path

import numpy as np

REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO / "transformer"))
import torch  # noqa: E402
import torch.nn.functional as F  # noqa: E402
from train import Transformer, P  # noqa: E402  (the released model class, unchanged)

SCHEDULE = [0, 5, 10, 20, 30, 50, 75, 100, 150, 200, 300, 500, 750, 1000, 1500, 2000, 3000, 5000,
            7500, 10000, 15000, 20000, 25000, 30000, 40000, 50000]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("out")
    ap.add_argument("--wd", type=float, required=True)
    ap.add_argument("--seed", type=int, required=True)
    ap.add_argument("--frac", type=float, default=0.3)
    ap.add_argument("--lr", type=float, default=1e-3)
    ap.add_argument("--epochs", type=int, default=20000)
    ap.add_argument("--shuffle-labels", action="store_true")
    ap.add_argument("--threads", type=int, default=2)
    ap.add_argument("--eval-every", type=int, default=50)
    args = ap.parse_args()
    torch.set_num_threads(args.threads)
    out = Path(args.out); out.mkdir(parents=True, exist_ok=True)

    torch.manual_seed(args.seed)
    rng = np.random.default_rng(args.seed)
    pairs = np.array([(a, b) for a in range(P) for b in range(P)])
    truth = (pairs[:, 0] + pairs[:, 1]) % P
    perm = rng.permutation(len(pairs))
    n_train = int(round(args.frac * len(pairs)))
    tr_idx, te_idx = np.sort(perm[:n_train]), np.sort(perm[n_train:])
    labels = truth.copy()
    if args.shuffle_labels:
        labels[tr_idx] = labels[tr_idx][rng.permutation(n_train)]
    A = torch.tensor(pairs[:, 0]); B = torch.tensor(pairs[:, 1])
    tr = torch.tensor(tr_idx); te = torch.tensor(te_idx)
    y_train = torch.tensor(labels[tr_idx]); y_truth = torch.tensor(truth)

    model = Transformer()
    opt = torch.optim.AdamW(model.parameters(), lr=args.lr, weight_decay=args.wd, betas=(0.9, 0.98))
    sched = sorted({e for e in SCHEDULE if e <= args.epochs} | {args.epochs})

    def evaluate():
        with torch.no_grad():
            logits = model(A, B)
            pred = logits.argmax(1)
            loss = F.cross_entropy(logits[tr], y_train).item()
            train_acc = (pred[tr] == y_train).float().mean().item()
            test_acc = (pred[te] == y_truth[te]).float().mean().item()
            wrong = int((pred != y_truth).sum().item())
        return loss, train_acc, test_acc, wrong

    def save(epoch):  # written under another name, then renamed, so a reader never sees half a file
        part = out / f"part_{epoch:06d}.npz"
        with open(part, "wb") as fh:
            np.savez(fh,
                 **{k: v.detach().cpu().numpy().astype(np.float64) for k, v in model.state_dict().items()},
                 epoch=epoch, train_idx=tr_idx, labels=labels, seed=args.seed, wd=args.wd,
                 frac=args.frac, shuffled=int(args.shuffle_labels))
        part.replace(out / f"ckpt_{epoch:06d}.npz")

    log = open(out / "curve.tsv", "a")
    print(f"# p {P} frac {args.frac} train {n_train} wd {args.wd} seed {args.seed} lr {args.lr} "
          f"shuffled {int(args.shuffle_labels)} epochs {args.epochs} threads {args.threads} torch {torch.__version__}",
          file=log, flush=True)
    print("epoch\ttrain_loss\ttrain_acc\theldout_acc\twrong_of_12769\tseconds", file=log, flush=True)
    t0 = time.time()
    for epoch in range(args.epochs + 1):
        if epoch > 0:
            loss = F.cross_entropy(model(A[tr], B[tr]), y_train)
            opt.zero_grad(set_to_none=True)
            loss.backward()
            opt.step()
        if epoch in sched or epoch % args.eval_every == 0:
            l, tra, tea, w = evaluate()
            print(f"{epoch}\t{l:.6f}\t{tra:.4f}\t{tea:.4f}\t{w}\t{time.time() - t0:.0f}", file=log, flush=True)
        if epoch in sched:
            save(epoch)
    (out / "DONE").write_text(f"{time.time() - t0:.0f} s\n")


if __name__ == "__main__":
    main()
