# Prior art for generalization to unseen tokens and sums (search 2026-11-01, night)

Claim searched: after training on pairs from which whole tokens (30 to 70 of 97) or whole sums (30 to 80)
are absent, the one-wave projection is exact on all 9,409 pairs. Two searchers (held-out operands and
classes in algorithmic tasks; structural explanations and zero-shot classes) and one adversarial
refuter, papers opened. The refuter's report, as returned:

**Verdict: NOT FOUND.** No paper I opened reports a network or read-out that is exact, or near exact, on whole tokens or whole labels left out of training in a group table. The network-side statements are KNOWN. This pass adds three sources:
- **Ootani 2609.20166** (2026) calls held-out operand rows of modular addition unrecoverable. No transformer beats its ceiling in 144 runs.
- **Zucchet et al. 2608.15448** argues from the coupon collector problem that a learner must see every output token at least once.
- **Huo & Geng (IJCAI 2017)** predict classes never used as labels from the order of the labels. This is the classical precedent for the never-labeled sums.

Both new contrasts assume the learner has no structure across tokens. So the claim holds as "exact given the cyclic-order prior that the DFT supplies", and the paper should say that in one sentence.

**How to read the tags.** "Opened" means I opened it this pass. "Searchers' record" means a searcher opened it and I did not reopen it, so treat it as opened=false for this pass. An earlier refuter pass in this session found Kvinge 2601.21150 and BRo-JEPA 2606.01372 (its notes are in /private/tmp/claude-501/-Users-thomas-lean-checked-network--claude-worktrees-project-direction-next-steps-a594e6/30a71daa-2e6f-4432-b4bf-d84f1dfcda46/scratchpad/refute_unseen/refuter_output.txt). I reread both papers in full and confirm the details below.

**1. Unseen tokens (30 to 70 of the 97 tokens absent from both slots)**
- **The network fails on them: KNOWN.**
  - Boix-Adsera 2310.09753, Lemma I.7 (searchers' record).
  - Kvinge et al., Can Neural Networks Learn Small Algebraic Worlds?, arXiv 2601.21150 (opened, full text). This is our holdout design (one-hot inputs, a cyclic group, an element absent from both slots), on networks only, with no projection.
    - Sec 3.2: in C100 they drop every pair with g' in either slot. Out-of-distribution symmetric consistency falls early and never recovers (Fig 1). Transformers, Adam, wd 0.001, 80% of the 10,000 pairs (App A).
    - Sec 3.3: elements held out of training entirely. No model reliably gets g*e = g for an unseen g.
  - Correction to the second searcher: their NOT FOUND item ("a group-table training set with a token absent from both operand slots") is wrong for networks, because of Kvinge. It still holds for projections and read-outs.
- **New contrast: Ootani, Small Enough to Know Everything, arXiv 2609.20166 (opened, full PDF).**
  - Setup: the task family addpotcK is addition mod 10 (a 100-cell table) with K = 0 to 3 operand rows held out. Llama-style transformers at 12K, 1M and 50M parameters, AdamW, wd 0.1, word-level digit tokens.
  - Sec 2(a): the ceiling is the best accuracy any predictor can reach under a declared hypothesis class.
  - Sec 3.3: the held-out rows' 10K test cells are proved unrecoverable, giving ceilings 1.00, 0.71, 0.43 and 0.14. The paper treats these as properties of the data split, whatever the model.
  - Sec 4.1 and Figs 1-2: 0 of 144 runs beat the ceiling.
  - I infer from the cell count (10K cells for K rows) that only the first slot is held out, so the token still trains through the second slot. The paper does not say which slot.
  - The paper credits the law to its predecessor 2607.05104. That paper's only version, v1 (opened), has no held-out rows or ceilings.
  - Our holdout is stronger: both slots, 30 to 70 tokens. The projection recovers cells this paper calls unrecoverable.
  - The paper does not name its hypothesis class in what I read. A Latin-square class would pin down a held-out row whenever its columns are otherwise observed. So scoring whole rows as unrecoverable implies a weaker class, and the unrecoverability comes from that class, not from the data.
  - Our derivation: swapping two absent tokens leaves the training set unchanged and gives another Latin square that fits it. So at least k! completions exist, and the data alone fix nothing on the 4,920 pairs. The projection's class (one wave per neuron, in Z_p index order) rules out those relabelings.
- **A structured model reaching group elements never trained: PARTLY KNOWN.** In both papers the structure is built in before training.
  - BRo-JEPA, arXiv 2606.01372 (opened, full text).
    - Sec 3: trained only on operations k = +1 and -1, tested on ±2 to ±9.
    - Sec 2.3: the predictor applies block rotations R(k theta).
    - Sec 5.2 and Fig 9: the learnable angles converge to pi/5 and its harmonics.
    - Table 1: accuracy on the unseen operations is 0.9944 with a ResNet-18 and 0.9724 with an MLP. Baselines with additive operation embeddings fail.
    - Limits: mod 10, the operation enters as an integer exponent, every state and target is trained, and the result is near exact, not exact.
  - Kam et al., arXiv 2607.13749 (opened, full PDF).
    - Sec 1 and Thm 1: a z^k net on a fixed roots-of-unity encoding (omega^a, omega^b) can only output k + 1 characters, at any width.
    - Sec 4.1: trained on a random 40% of pairs, with no token holdout. Representable linear tasks pass 99% on train and test.
    - Inference: such a net would cover unseen tokens by construction, since the encoding supplies the order. It is the built-in version of the prior that the projection imposes after training.
  - Kadlcik 2506.08966 and Kantamneni 2502.00873 (searchers' record): fits made after training, but the language model had trained every token.
- **The claim itself: NOT FOUND.**

**2. Unseen sums as labels (30 to 80 sums never used as a label)**
- **The network never outputs them: KNOWN.**
  - Lazic 2604.21632 Sec 4, Land & Bartolo 2405.05417 Sec 2.2, and Gandhi & Lake 1906.10197 Sec 3.2 (searchers' record; this pass I opened only Lazic Sec 1-2).
  - New: Zucchet, Lee & Linderman, Language models suffer from a curse of ambiguity, arXiv 2608.15448 (opened, App E.1). A token never seen in the data cannot be told apart from other off-support tokens, so the k log k coupon-collector floor holds "regardless of the model, the optimizer, or the loss".
  - Their setting is next-token distributions with interchangeable tokens. The projection does not break that floor. It sits outside its assumption, because it brings in the order of the output index.
- **A read-out that produces never-labeled classes from the label order: PARTLY KNOWN, outside group tasks.**
  - Huo & Geng, Ordinal Zero-Shot Learning, IJCAI 2017, pp. 1916-1922 (opened, full PDF).
  - Sec 3.2: two thirds of the ordinal labels are seen in training, and testing uses items with the other third. Tasks are head pose (Pointing'04, BJUT-3D) and age (MORPH).
  - Sec 2.2: an unseen label gets its supervision from neighbouring seen labels along the order. Results are mean absolute error in Tables 1-2, with four patterns of unseen labels in Figs 5-6.
  - Limits: the labels are ordered, not cyclic, it is not a group task, and nothing is exact.
- **In a group or modular task: NOT FOUND.**
  - Kvinge Sec 3.3 does not say whether held-out elements were also removed as labels. Ootani holds out operand rows, not labels.
  - Our derivation: permuting the never-used labels among themselves gives another Latin square that fits the training data. So recovering them needs the order prior, as with tokens.

**3. After one step: NOT FOUND, with or without holdouts.**
- No opened paper scores a network or read-out at step 1 under a token or label holdout:
  - Kvinge tracks out-of-distribution consistency over epochs.
  - BRo-JEPA's angles converge over epochs.
  - Ootani reports accuracy after training ends and the epoch where generalization starts.
- Without holdouts, the one-step prior art stands as in prior_art_batch45 section T1: the mechanism is partly known, the result is not found.

**4. Exact: NOT FOUND with tokens or labels absent.**
- The nearest result is BRo-JEPA at 0.9944, with rotations built in, unseen operations, and every target trained.
- Exact with every symbol present is routine (earlier files). Kam passes 99% with every token present.
- The data do not determine the held-out cells (Ootani's ceilings and the permutation argument). So "exact" means exact relative to the cyclic-order prior.
- What was measured: each neuron's frequency and phases are estimated from columns full of untouched initial rows, or rows that were only ever pushed down. They still land inside that prior after 1 to 15 steps.

**Referee points from this pass**
- Expect Ootani's unrecoverability and model-independence statements to be quoted against the claim. The answer is the declared hypothesis class: name the prior (Z_p index order, one wave per neuron) and say the network does not have it.
- Suggested control (our inference, not run): train with the tokens relabeled by a random permutation sigma, then project with the DFT in the original index order. The waves are scrambled in that order, so exactness should fail on every pair, not just the held-out ones. That would show the order does the work.
- Split check: I recomputed the 5%-of-table splits using train_gen.py's split logic and they confirm the accidents FINDINGS reports. Seed 0 also never has token 68 as first operand, which FINDINGS leaves out (it does report seed 2's missing first token 32).
- With uniform draws, a token missing from both slots of 470 pairs happens in about 0.4% of seeds (0.0044 expected tokens per seed). Missing sums are common: about 0.66 per seed.

**Searches run.** The full log is in /private/tmp/claude-501/-Users-thomas-lean-checked-network--claude-worktrees-project-direction-next-steps-a594e6/30a71daa-2e6f-4432-b4bf-d84f1dfcda46/scratchpad/refuter_unseen/searches.log.
- **Web (12):**
  - tied embeddings with a held-out output class or unseen residue
  - group convolution on cyclic one-hot inputs for modular addition, with elements absent
  - Marcus 1998, training independence
  - rebuilding the embeddings of never-seen tokens from learned Fourier structure
  - a quasigroup or Latin square with a whole row or column withheld, leave-one-operand-out
  - arithmetic transformers with excluded operands, 2025-2026
  - classifiers that predict never-labeled classes from ordered or cyclic labels
  - shift-equivariant circulant nets for modular addition
  - the coupon collector problem: every residue must appear
  - interpolating an untrained token's embedding on the learned circle
  - training on a subgroup or coset of Z_n
  - novel or unseen symbols in group tables
- **OpenAlex phrase queries (8):**
  - modular addition + unseen tokens
  - modular arithmetic + held-out tokens
  - modular addition + never appear + training (this one found Ootani)
  - cyclic group + held out + elements
  - Cayley table + missing rows
  - zero-shot + modular addition
  - modular arithmetic + unseen residues
  - group operation + unseen elements
- **arXiv API (6):**
  - unrecoverable AND modular
  - recoverability AND grokking
  - held-out rows
  - operand rows
  - modular addition AND never
  - Latin square AND held out
- **Backward citations:** the related work in Lazic 2604.21632 Sec 2 (Boix-Adsera; Anand et al. 2025 on in-context learning with novel tokens and resetting embeddings; copying architectures). Nothing on group holdouts.

**Scope**
- **Opened, relevant sections read:**
  - 2601.21150, 2606.01372, 2609.20166, 2607.05104 v1 and 2607.13749
  - 2608.15448 App E
  - Huo & Geng, IJCAI 2017
  - 2604.21632 Sec 1-2
  - 2610.13750, keyword check only (its holdouts are tasks, not tokens)
- **Abstracts only, judged off-target:** 2605.08119, 2608.14803, 2610.00647, 2603.24746, 2407.17963 (length generalization), 2603.08322, 2602.18649, 2605.27078, 2604.21935 and 2512.25060.
- **Not opened and not cited:**
  - Marcus 1998, Cognitive Psychology 37: ScienceDirect returned 403, and the eScholarship copy was not a PDF.
  - The PégaseNet record on Zenodo (18324563): deleted (HTTP 410).

Safety copy of this output: /private/tmp/claude-501/-Users-thomas-lean-checked-network--claude-worktrees-project-direction-next-steps-a594e6/30a71daa-2e6f-4432-b4bf-d84f1dfcda46/scratchpad/refuter_unseen/refuter_output.txt
