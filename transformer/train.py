"""Train a one-layer transformer to add modulo 113 (Nanda et al. 2023's model), then hand it on.

Model: vocabulary 114 (tokens 0..112 and '=' = 113), input [a, b, =], learned token and
position embeddings (d_model 128), one attention layer (4 heads of 32, no biases, no LayerNorm,
causal mask), one MLP (512, ReLU, biases), residual connections, unembedding of the last
position to 113 logits (no bias). The attention score divides q . k by sqrt(32) as in the
original; the integer evaluator folds that factor into W_Q when it quantises.

Training: AdamW, lr 1e-3, weight decay 1.0, betas (0.9, 0.98), full batch on a seeded random
split of the 12,769 pairs. Every epoch the train and held-out accuracy are measured; every 100
epochs one line goes to runs/train.log; every 500 epochs a checkpoint goes to runs/.

Stop rule: once train and held-out accuracy are both 1.0 for 300 consecutive epochs, a margin
phase of 2000 epochs begins: cross-entropy plus a hinge term on the TRAIN pairs that pushes the
gap between the right logit and the best wrong logit above a target (the median train gap at the
moment the phase starts, written to the log), with the same weight decay. Then stop.
Fallback: if the stop rule has not fired after FALLBACK_HOURS, training continues on all pairs
(said in the log). Hard budget: BUDGET_HOURS wall; at the budget the best checkpoint by smallest
gap over all pairs is written to runs/best.pt and training stops.

Usage: python3 transformer/train.py [--frac 0.5] [--seed 0] [--budget-hours 3] [--fallback-hours 2]
       [--max-epochs N] [--eval-every 100] [--ckpt-every 500] [--runs transformer/runs]
"""
import argparse
import os
import sys
import time

import numpy as np
import torch
import torch.nn.functional as F

torch.set_num_threads(2)

P = 113
VOCAB = P + 1          # 0..112 and '='
EQ = P
D_MODEL, N_HEADS, D_HEAD, D_MLP = 128, 4, 32, 512


class Transformer(torch.nn.Module):
    def __init__(self):
        super().__init__()
        s = 1.0 / np.sqrt(D_MODEL)
        self.tok = torch.nn.Parameter(torch.randn(VOCAB, D_MODEL) * s)
        self.pos = torch.nn.Parameter(torch.randn(3, D_MODEL) * s)
        self.WQ = torch.nn.Parameter(torch.randn(N_HEADS, D_MODEL, D_HEAD) * s)
        self.WK = torch.nn.Parameter(torch.randn(N_HEADS, D_MODEL, D_HEAD) * s)
        self.WV = torch.nn.Parameter(torch.randn(N_HEADS, D_MODEL, D_HEAD) * s)
        self.WO = torch.nn.Parameter(torch.randn(N_HEADS, D_HEAD, D_MODEL) * (1.0 / np.sqrt(D_HEAD)))
        self.Win = torch.nn.Parameter(torch.randn(D_MODEL, D_MLP) * s)
        self.bin = torch.nn.Parameter(torch.zeros(D_MLP))
        self.Wout = torch.nn.Parameter(torch.randn(D_MLP, D_MODEL) * (1.0 / np.sqrt(D_MLP)))
        self.bout = torch.nn.Parameter(torch.zeros(D_MODEL))
        self.U = torch.nn.Parameter(torch.randn(D_MODEL, P) * s)

    def forward(self, a, b):
        """Logits at the last position for the batch of pairs (a, b); shape (N, 113).

        Only the last position's query is needed: with a causal mask, the output at position 2
        attends over positions 0, 1, 2 and nothing downstream reads positions 0 and 1.
        """
        n = a.shape[0]
        x0 = self.tok[a] + self.pos[0]            # (N, D)
        x1 = self.tok[b] + self.pos[1]
        x2 = (self.tok[EQ] + self.pos[2]).expand(n, D_MODEL)
        X = torch.stack([x0, x1, x2], 1)          # (N, 3, D)
        q = torch.einsum("nd,hde->nhe", x2, self.WQ)            # (N, H, E)
        k = torch.einsum("njd,hde->nhje", X, self.WK)           # (N, H, 3, E)
        v = torch.einsum("njd,hde->nhje", X, self.WV)
        s = torch.einsum("nhe,nhje->nhj", q, k) / np.sqrt(D_HEAD)
        att = torch.softmax(s, -1)                              # (N, H, 3)
        z = torch.einsum("nhj,nhje->nhe", att, v)               # (N, H, E)
        attn_out = torch.einsum("nhe,hed->nd", z, self.WO)
        r = x2 + attn_out
        m = torch.relu(r @ self.Win + self.bin)
        out = m @ self.Wout + self.bout
        return (r + out) @ self.U


def margins(logits, labels):
    """right logit minus the best wrong logit, per row."""
    right = logits.gather(1, labels[:, None])[:, 0]
    wrong = logits.clone()
    wrong.scatter_(1, labels[:, None], float("-inf"))
    return right - wrong.max(1).values


def save_ckpt(model, path, extra):
    torch.save({"state": {k: v.detach().clone() for k, v in model.state_dict().items()}, **extra}, path)
    np.savez(path.replace(".pt", ".npz"),
             **{k: v.detach().cpu().numpy().astype(np.float64) for k, v in model.state_dict().items()},
             **{k: np.asarray(v) for k, v in extra.items() if not isinstance(v, (dict, list))})


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--frac", type=float, default=0.5)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--lr", type=float, default=1e-3)
    ap.add_argument("--wd", type=float, default=1.0)
    ap.add_argument("--budget-hours", type=float, default=3.0)
    ap.add_argument("--fallback-hours", type=float, default=2.0)
    ap.add_argument("--max-epochs", type=int, default=10**9)
    ap.add_argument("--eval-every", type=int, default=100)
    ap.add_argument("--ckpt-every", type=int, default=500)
    ap.add_argument("--stable-epochs", type=int, default=300)
    ap.add_argument("--margin-epochs", type=int, default=2000)
    ap.add_argument("--hinge-weight", type=float, default=1.0)
    ap.add_argument("--runs", default="transformer/runs")
    args = ap.parse_args()

    os.makedirs(args.runs, exist_ok=True)
    log = open(os.path.join(args.runs, "train.log"), "a")

    def say(line):
        print(line, file=log, flush=True)
        print(line, file=sys.stderr, flush=True)

    torch.manual_seed(args.seed)
    rng = np.random.default_rng(args.seed)
    pairs = np.array([(a, b) for a in range(P) for b in range(P)])
    labels_np = (pairs[:, 0] + pairs[:, 1]) % P
    perm = rng.permutation(len(pairs))
    n_train = int(round(args.frac * len(pairs)))
    tr_idx, te_idx = np.sort(perm[:n_train]), np.sort(perm[n_train:])
    A = torch.tensor(pairs[:, 0]); B = torch.tensor(pairs[:, 1]); Y = torch.tensor(labels_np)
    tr = torch.tensor(tr_idx); te = torch.tensor(te_idx)

    model = Transformer()
    opt = torch.optim.AdamW(model.parameters(), lr=args.lr, weight_decay=args.wd, betas=(0.9, 0.98))

    say(f"# start {time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())} pid {os.getpid()} seed {args.seed} "
        f"frac {args.frac} train {len(tr_idx)} held-out {len(te_idx)} lr {args.lr} wd {args.wd} "
        f"budget {args.budget_hours} h fallback {args.fallback_hours} h torch {torch.__version__}")
    say("# epoch train_loss train_acc test_acc min_margin_all phase")

    t0 = time.time()
    stable = 0
    phase = "fit"
    margin_target = None
    margin_left = 0
    fell_back = False
    best = (-float("inf"), None)
    epoch = 0
    while epoch < args.max_epochs:
        epoch += 1
        model.train()
        logits = model(A[tr], B[tr])
        loss = F.cross_entropy(logits, Y[tr])
        if phase == "margin":
            loss = loss + args.hinge_weight * torch.relu(margin_target - margins(logits, Y[tr])).mean()
        opt.zero_grad(set_to_none=True)
        loss.backward()
        opt.step()

        with torch.no_grad():
            model.eval()
            all_logits = model(A, B)
            all_margin = margins(all_logits, Y)
            pred_ok = all_logits.argmax(1) == Y
            train_acc = pred_ok[tr].float().mean().item()
            test_acc = pred_ok[te].float().mean().item() if len(te_idx) else 1.0
            min_margin = all_margin.min().item()
        elapsed = time.time() - t0

        if phase == "fit":
            stable = stable + 1 if (train_acc == 1.0 and test_acc == 1.0) else 0
            if stable >= args.stable_epochs:
                phase = "margin"
                margin_left = args.margin_epochs
                with torch.no_grad():
                    margin_target = float(all_margin[tr].median().item())
                say(f"# epoch {epoch}: train and held-out accuracy 1.0 for {stable} epochs; margin phase "
                    f"for {args.margin_epochs} epochs, hinge target {margin_target:.4f} (median train gap), "
                    f"hinge weight {args.hinge_weight}")
            elif not fell_back and elapsed > args.fallback_hours * 3600:
                fell_back = True
                say(f"# epoch {epoch}: no generalisation after {args.fallback_hours} h (train {train_acc:.4f}, "
                    f"held-out {test_acc:.4f}); FALLBACK: continuing on all {len(pairs)} pairs, no held-out set")
                tr_idx = np.arange(len(pairs)); te_idx = np.array([], dtype=int)
                tr = torch.tensor(tr_idx); te = torch.tensor(te_idx)
        elif phase == "margin":
            margin_left -= 1

        if min_margin > best[0]:
            best = (min_margin, epoch)
            if train_acc == 1.0 and test_acc == 1.0:
                save_ckpt(model, os.path.join(args.runs, "best.pt"),
                          {"epoch": epoch, "min_margin": min_margin, "train_idx": tr_idx, "phase": phase,
                           "fell_back": fell_back})

        if epoch % args.eval_every == 0 or epoch == 1:
            say(f"{epoch} {loss.item():.6f} {train_acc:.4f} {test_acc:.4f} {min_margin:.4f} {phase}")
        if epoch % args.ckpt_every == 0:
            save_ckpt(model, os.path.join(args.runs, f"ckpt_{epoch:06d}.pt"),
                      {"epoch": epoch, "min_margin": min_margin, "train_idx": tr_idx, "phase": phase,
                       "fell_back": fell_back})

        done_margin = phase == "margin" and margin_left <= 0
        over_budget = elapsed > args.budget_hours * 3600
        if done_margin or over_budget:
            why = "margin phase complete" if done_margin else f"budget of {args.budget_hours} h reached"
            say(f"{epoch} {loss.item():.6f} {train_acc:.4f} {test_acc:.4f} {min_margin:.4f} {phase}")
            save_ckpt(model, os.path.join(args.runs, "final.pt"),
                      {"epoch": epoch, "min_margin": min_margin, "train_idx": tr_idx, "phase": phase,
                       "fell_back": fell_back})
            say(f"# stop at epoch {epoch}: {why}; {elapsed:.0f} s; best min margin over all pairs "
                f"{best[0]:.4f} at epoch {best[1]} (runs/best.pt holds the best checkpoint that was right on "
                f"every pair); fell_back {fell_back}")
            break
    log.close()


if __name__ == "__main__":
    main()
