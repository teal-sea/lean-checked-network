# Prior art for the fourth and fifth batches (search 2026-11-01, evening)

Claim groups searched: T1 (one step, little data, wrong labels) and T2 (the even part of the
activation). Method: two searchers per group with different angles (one-step feature-learning theory;
modular-arithmetic papers on the early phase, data and label corruption; activation analyses;
activation comparisons in modular arithmetic), then one adversarial refuter per group told to find
each statement already published and to cite only papers it opened, then a synthesis. About 90 web
searches, forward citations of fourteen anchor papers, about 85 papers opened. Not searched: the
unseen-token result and the arrival law of the sixth batch.

What follows is the synthesis as returned (lightly formatted); the per-paper records are in the
workflow journal of this session.

T1 verdict: PARTLY KNOWN. The mechanism is published, and so is one-step feature learning on other tasks. Not published: an exact, data-free projection after one step from iid init while the net is at chance; that projection surviving 10% data or 25 to 50% wrong labels; and the t* x lr x H law.
T2 verdict: PARTLY KNOWN. Each half of the even-part reading is published separately (the even part writes the adder: Wang 2610.11833; the even part reads it: He 2602.16849). The odd part reading at chance follows by derivation. Not published: an even read-out turning a failing GELU or SiLU projection exact in wd-0 memorizers; the f(sz)/s ratio law; and projections of nets trained with |x| or tanh.

Grading (the refuter's rule, used throughout):
- Known: an opened paper reports the statement, or it follows by direct derivation.
- Partly known: an opened paper reports a weaker version. That means another task (such as a sum mod 2), the init erased or the readout trained, end of training rather than early, or near-perfect rather than exact.
- Not found: only mechanism-level or Gaussian-only background exists.
- Inference: the searchers' own reasoning, not stated in any paper.

T1. ONE STEP, LITTLE DATA, WRONG LABELS

1. Known
- Mechanism. Wang et al., Probability-Signature Dynamics: Unpacking Modular Addition Learning Within Two-Layer Networks, arXiv 2610.11833, Sec 4.1 Thm 1. In small-parameter gradient flow on the same untied network, each Fourier mode's update is the product of the other two, with coupling c2 = sigma''(0).
- He et al., On the Mechanism and Dynamics of Modular Addition, arXiv 2602.16849, Sec 3.2: the initial spectrum picks each neuron's frequency. Sec 6.2 Prop 6.3 defines how much energy one gradient step pushes into frequency k. That is a theory quantity with no step-1 experiment.
- The target is Gromov's random-phase family (Grokking modular arithmetic, arXiv 2301.02679, Eqs 6-7).
- Width. Hand-built phase-sum nets average 0.9999 to 1.0000 accuracy at N 512 over 40 seeds (Swaroop, Latent Algorithmic Structure Precedes Grokking, arXiv 2603.23784, Sec 4 Table 1). So H >= 512 is the expected width for exactness, not a finding.
- Net at chance after one step on little data. Mohamadi et al., Why Do You Grok?, arXiv 2407.12332, Thm 3.4 and Thm 4.3: in the kernel regime, a permutation-equivariant model needs a constant fraction of the table. The projection is not permutation-equivariant, so the bound does not apply to it (inference).
- Noisy labels are fitted first on modular addition. Liu & Lu, Unveiling Memorization-Generalization Coexistence, arXiv 2605.18022, Sec 3.2 Result 3.2; Wang Sec 6.1 Thm 3.
- One large step learns features on other tasks, but these papers erase the init:
  - Barak et al., Hidden Progress in Deep Learning, arXiv 2207.08799: Sec 4.1 footnote 9 (the parity indices emerge in a single SGD step); Thm 4 in App B.1; Prop 9 in App B.2 (the exact support comes from the top-k coordinates of one batch gradient).
  - Daniely & Malach, Learning Parities with Neural Networks, arXiv 2002.07400, Thm 2 and Sec 5.
  - Shi, Wei & Liang, Provable Guarantees for Neural Networks via Gradient Feature Learning, arXiv 2310.12408, Thm 3.4 and Prop 5.1.
  - Kim & Suzuki, Transformers Provably Solve Parity Efficiently with Chain of Thought, arXiv 2410.08633, Thm 5.
  - All four erase the init, either through the first step's weight decay or by starting from zero. The update alone carries the feature, and the readout is trained afterwards or read off the gradient.
- Second-order and giant-step theory:
  - Damian, Lee & Soltanolkotabi, Neural Networks can Learn Representations with Gradient Descent, arXiv 2206.15144, Sec 5.1 Lemma 1. The first gradient is the target's Hessian applied to each neuron's random init, and it needs n of order d^2.
  - Dandi et al., How Two-Layer Neural Networks Learn, One (Giant) Step at a Time, arXiv 2305.18270, Sec 3.3 Thm 5. A step proportional to width weakly recovers a leap-l subspace with n of order d^l.
- Standard one-step theory predicts no gain where T1 sits, because x^2 has no linear Hermite part and addition has no linear part:
  - Ba et al., High-dimensional Asymptotics of Feature Learning, arXiv 2205.01445, Sec 4.2 Thm 7.
  - Moniri et al., A Theory of Non-Linear Feature Learning with One Gradient Step in Two-Layer Neural Networks, arXiv 2310.07891, Condition 2.3 and Sec 4.
  - Dandi Thm 4.

2. Partly known, and how ours differs
- One Adam step, exact while the net is at chance.
  - Closest statement: Kumar & Sankaranarayanan, Flat Loss, Evolving Features: Grokking in Modular Addition, arXiv 2610.22593, Sec 4.2 Thm 4.2(iii) and Eq 12. On modular addition, a refit readout is at least 1 - eps accurate on held-out pairs from the first update, while the net's own held-out accuracy stays below a small eps_lag.
  - Their setting: the init is built from the training data (the theorem says nothing about iid starts), width p^2(p-1)^2, train fraction 4/5, supported-Polar steps with weight decay, a ridge refit on the training pairs, and accuracy that is not exact. From iid init, their refit first reaches 90% at update 6,500 (Sec 5.1).
  - Ours: iid N(0, 1/H) init, one Adam step, wd 0, a data-free projection, exact on all p^2 pairs in 20 of 20 seeds, Lean-checked for several cells. The update alone is at chance.
  - The only precedent where init and update are both needed is on parity: Edelman et al., Pareto Frontiers in Neural Feature Learning, arXiv 2309.03800, Sec 3.2 Thm 5 (formal version Thm 21, App B.3). A neuron's under-sparse init supplies part of the support and one step supplies the rest. The init is designed, the result is that a subnetwork exists rather than a fixed projection, and there is no step-1 accuracy.
  - Kou et al., Matching the Statistical Query Lower Bound for k-Sparse Parity Problems with Sign Stochastic Gradient Descent, arXiv 2404.12376, Remark 3.2, Sec 5.1, Lemmas 5.1-5.2. It uses a z^k activation and Adam-like sign steps. Good neurons satisfy a_r = prod sign(w_rj(0)), which reads as the mod-2 form of the phase-sum rule (inference). Half the neurons satisfy it at init, training takes many steps, and there is no projection.
  - Neural Networks as Kernel Learners: The Silent Alignment Effect, arXiv 2111.00034 (abstract only), shows alignment before the loss drops, but with small init and linear nets.
- One plain GD step at lr about H.
  - Width-proportional single steps are known on Gaussian targets: Dandi Thm 5 (Eq 16), and Ba Sec 3. In Ba's scaling, eta of order sqrt N gives an update proportional to width and comparable to the init; larger exponents let the gradient swamp the init.
  - Tensor Programs V (Yang et al.), arXiv 2203.03466, Sec 5 Eq 5 and Fig 5: in standard parametrization one step moves the outputs by order width, because update times init adds coherently across neurons.
  - Ours adds: a mod-p table, an exact projection, a learning-rate window with an upper edge near 10H, and the update-only control.
  - Inference: Ba's swamping regime is the candidate for the upper edge, and the TP5 argument is the candidate origin of lr x H.
- 10% of the table.
  - Theory: Tian, Provable Scaling Laws of Feature Emergence from Learning Dynamics of Grokking, arXiv 2509.21519, Sec 4.5 Thm 4 (O(M log M) samples keep the Fourier maxima). Wang Sec 4.2 Thm 2: a training ratio rho leaves the drift unchanged and adds a zero-mean sampling error with variance proportional to [(1 - rho) + alpha]/rho. It is untested.
  - Experiment, end of training only: Liu & Lu App D.2 Fig 25 apply per-neuron filtration to clean-label ReLU nets at training ratios 0.15 to 0.5, after 200,000 epochs at wd 0.1. The refuter checked the ratio list in the caption.
  - The accuracies come from the earlier file's read of the rendered figure (line 135) and were not re-verified this round. At ratio 0.15 the raw net is near 0%, and filtration gives about 75% at width 513 and about 93% at width 8,193. At 0.2 it is near 100% from width 2,049. Never exact.
  - Edelman Sec 4.1 Fig 2 reports, on parity, that width buys data and steps.
  - Ours: step 1, 10% of the table, exact, wd 0.
  - Inference: with one-hot inputs d = 2p, so 10% of the table is n of about 0.025 d^2. That is the regime Damian and Dandi need for a target with no linear part.
- 25% to 50% wrong labels at step 1.
  - Liu & Lu Sec 4 Fig 5: filtration is near-perfect at 80% noise (200,000 epochs, wd 0.1, one seed).
  - Swaroop Sec 4.1 Table 2: a model rebuilt from the extracted frequencies and phases scores 95.5%, where the net itself (noise 0.30, wd 1.0) scores 0.23%. Final checkpoint only.
  - Wang Thm 2: noise enters the drift only through the factor (1 - alpha). Untested.
  - Doshi et al., To grok or not to grok, arXiv 2310.13061, Fig 1a and Fig 4. In the same family (x^2, p 97, AdamW lr 0.01), the net generalizes at wd 0 with 35% corruption at data fraction 0.5, at the end of training. Their wd-0 phase diagram (Fig 3a) shows memorization at every corruption level below a data fraction of about 0.34. That region covers our 10% runs and the 0.3 fraction searcher 2 reports for the wrong-label runs.
  - Ours: step 1, exact, wd 0, inside the region where Doshi's net only memorizes.
  - Inference: Wang's (1 - alpha) factor matches RULES.md's prediction that t* x lr x H x (1 - noise) is about 10.
- 75% wrong labels, exact within 9 to 20 steps while the net fits them.
  - Liu & Lu: near-perfect at 80% noise, but at the end of training. Wang Thm 3: the loss on noisy labels falls faster early.
  - In standard classification the early-learning picture is that clean labels are fitted first (Early-Learning Regularization Prevents Memorization of Noisy Labels, arXiv 2007.00151; Li et al., arXiv 1903.11680; abstracts only). On modular addition the order is reversed.
  - Ours: exact within 20 steps while the net memorizes the wrong labels.
- Lean check. Proofs of performance exist only as accuracy bounds on trained nets:
  - Wu et al., Towards a Unified and Verified Understanding of Group-Operation Networks, arXiv 2410.07476: compact proofs checked against a brute-force verifier. No proof-assistant kernel appears in the text.
  - Yip et al., Modular addition without black-boxes, arXiv 2412.03773: accuracy bounds for trained pizza transformers.
- Contrasts a referee will raise:
  - Xu et al., Benign Overfitting and Grokking in ReLU Networks for XOR Cluster Data, arXiv 2310.02541, Thm 3.1, Sec 4.2.1 and Fig 3. One step fits the noisy labels, test accuracy is at chance, and the neurons are not yet aligned with the cluster directions. That is the opposite picture.
  - Ba Sec 4.2 Prop 9: the one-step gain vanishes as width grows, while ours improves with width.
  - Minegishi et al., Bridging Lottery Ticket and Grokking, arXiv 2310.19470, Sec 3.2 Fig 4a: pruning at init fails on modular addition.
  - Gromov Sec 4.1: no periodic structure exists at the first overfit.
  - Nanda et al., Progress measures for grokking via mechanistic interpretability, arXiv 2301.05217, App C.2.2: with 10% to 20% of the data the model never groks.

3. Not found in any opened paper
- A data-free per-neuron projection that is exact on all p^2 pairs after one discrete step (Adam or plain GD) from iid standard init, while the net is at chance and the update alone is at chance.
- The same after one step on 10% of the table, or with 25% to 50% wrong labels.
- Exactness within 9 to 20 steps at 75% wrong labels.
- A one-step plain-GD learning-rate window with an upper edge.
- Any law for the time to features or to exactness in lr x width, so t* x lr x H of about 10 is new. The existing timing laws all concern the net's own grokking, and none has this width dependence:
  - Khanh et al., The Norm-Separation Delay Law of Grokking, arXiv 2603.13331, abstract only: set by eta x lambda, with no width.
  - Kataria, Quantifying the Memorization-to-Generalization Transition, arXiv 2609.10657, abstract only: onset about H^-0.27 eta^-0.5.
  - Liu et al., Towards Understanding Grokking: An Effective Theory of Representation Learning, arXiv 2205.10343, Sec 3.2 and App E: about 3/(lambda_3 eta) in a toy model, with no width.
  - Wang's drift, eta c2 (1 - alpha)/P, has no width term.
- A proof-assistant kernel check of any modular-addition network.

4. Most expected citations
- Kumar & Sankaranarayanan 2610.22593: the closest statement.
- Wang 2610.11833: the closest theory, covering both data ratio and label noise.
- Barak 2207.08799: hidden progress, and one step on a sum mod 2.
- An empirical referee adds Doshi 2310.13061, the same x^2 family with corrupted labels.

Scope:
- Two searchers and a refuter.
- About 40 web searches and 40 arXiv-API queries.
- Forward citations of six anchor papers, 56 citing papers screened by title.
- About 45 papers opened, with full text or HTML for every paper graded partial.
- Abstracts only: Khanh, Kataria, 2111.00034, 2007.00151 and 1903.11680.

T2. EVEN PART OF THE ACTIVATION

1. Known
- The even part writes the adder.
  - Wang 2610.11833, Sec 3.2 Prop 1, Thm 1, and App B Fig 10. First-order terms vanish under uniform marginals, and the Fourier coupling runs on sigma''(0). A linear net cannot fit the training set, and tanh, which has no second-order term, generalizes very poorly.
  - Wang App C.2 Fig 12, at P 7 on the full table: keeping only the sigma''(0) term predicts the real GELU net's dominant frequency for 93% of the neurons that develop one.
  - Tian 2509.21519, Sec 4.3, remark after Thm 2: for ax + bx^2 the linear part cancels.
  - Lin, Tegmark & Rolnick, Why does deep and cheap learning work so well?, arXiv 1608.08225, Sec II Eq 11: a product gate uses only the activation's even part and needs sigma''(0) != 0.
  - Damian Lemma 1: once the target's linear part is removed, the first step runs on the activation's second Hermite coefficient.
- For trained ReLU nets, even read-outs keep the adder and odd read-outs are at chance.
  - He 2602.16849, Sec 3.1 Obs 4, Table 1 and footnote 2. A ReLU net trained on all pairs (p 23, M 512) and read at test time with |x|, x^2, x^4, x^8, log(1 + e^{2x}) or e^x keeps accuracy 1.000. Read with x it gives 0.041, and with x^3 0.036, against chance 0.043. Footnote 2 writes ReLU as (x + |x|)/2 and has the linear half cancel under phase symmetry.
  - The same |x| swap: Wu 2410.07476 App F Table 1 (Z/53Z, 99.55% to 99.88%); Stander et al., Grokking Group Multiplication with Cosets, arXiv 2312.06581, Sec 6.3 Table 1 (S5, 100%).
  - Yip 2412.03773, Sec 5.1, Sec 6.1 and App I: the |x|/2 half alone fits the pizza logits with R^2 0.99.
- The odd part alone reads at chance. This is known and forced, so present it as a check, not a finding.
  - For GELU and SiLU the odd part is exactly z/2 at every s, since GELU(-z) = -z(1 - Phi(z)) and SiLU(-z) = -z(1 - sigma(z)).
  - So that read-out is linear, with logits A[c,a] + B[c,b], and cannot single out a + b. Yip Sec 5.1 writes ReLU's x/2 half in this form, and He Table 1 measures it.
  - Decomposition references: Zhang, Saxe & Latham, When Are Bias-Free ReLU Networks Effectively Linear Networks?, arXiv 2406.12615, Sec 3.1 Thm 1; Holzmuller & Scholpple, Beyond ReLU: How Activations Affect Neural Kernels and Random Wide Networks, arXiv 2506.22429, Sec 3.
- An odd component slows learning, and odd activations fail. Salah & Yevick, Controlling Grokking with Nonlinearity and Data Symmetry, arXiv 2411.05353, Sec 3.2 Figs 5-7. With x + a x^2, grokking comes earlier as a grows. x^3 and x^2 sign(x) never grok, while |x^3| does.

2. Partly known, and how ours differs
- |x| projection exact at every checkpoint.
  - Only the read half is known. Gromov App B Fig 6 reads his constructed one-wave weights with |x| at about 100% by width about 150. He, Wu and Stander read trained ReLU nets with |x|.
  - Ours: a net trained with |x| at wd 0, whose memorizer projects exactly at all 45 checkpoints (H 512 and 1024).
  - Exactness from H 512 is the expected width for random-phase nets (Swaroop Table 1), not a finding. No opened paper speaks to the H 256 failure.
- tanh projection at chance under every read-out.
  - Known: tanh nets generalize poorly (Wang App B), and odd activations do not grok (Salah & Yevick).
  - Ours: the projection stays at chance even when read with x^2, |x| or the even part, at s 1, 10 and 100. So tanh wrote nothing.
  - Inference, with no citable source: for cosine-wave neurons, an odd activation produces only Fourier modes (r, s) with r + s odd, so the adder mode (1, 1) is absent.
  - The nearest published result is a degree selection rule in a complex-valued model: Kam et al., Algebraic Representability as the Limiting Regime of Grokking, arXiv 2607.13749, Thm 1. It states nothing about T2.
- GELU and SiLU projections wrong under their own activation.
  - Gromov App B Fig 6: his constructed one-wave weights read with GELU stay near chance up to width about 460 (read off the figure; the caption does not give p). With x^2, x^4, |x| and ReLU they reach about 100%. He offers no proof or explanation.
  - Net-level results only: Liu & Lu Sec 3.1 Fig 1b (GELU and quadratic nets hit test-accuracy ceilings under label noise), and Wang Fig 1 (a GELU net at lambda 0 with 10% label noise scores 100% train and 0 test, and is never analyzed).
  - Ours: projections of trained GELU and SiLU memorizers, wrong on thousands of pairs at 2k and 20k steps.
  - Inference, untested: this explains Gromov's result. His 1/sqrt(D) scaling keeps |h| at most sqrt(2/p), about 0.14 at p 97. There GELU's even/odd ratio is about 0.1, below the 0.27 threshold.
- Even read-outs rescue the projection.
  - Prior swaps: He Table 1, Wu App F, Stander Sec 6.3, and Liu & Lu Sec 4 Fig 5 (right). In Liu & Lu, x^2 or reverse ReLU (same even part, odd part flipped) on noisy-label ReLU nets at wd 0.1 keeps or raises test accuracy and lowers accuracy on the noisy labels.
  - In every one of these the net's own read-out already works or nearly works. They are ReLU only and not exact.
  - Ours: GELU and SiLU weights read with x^2, |x| or their own even part go from 3,575 to 6,502 wrong pairs (GELU, s 1) to zero, from step 20 to 50, in wd-0 memorizers.
- The f(sz)/s knob.
  - The direction is known. Salah & Yevick: more even part, earlier grokking; measured as grokking time, with weight decay, at P 27.
  - Kumar, Bordelon, Gershman & Pehlevan, Grokking as the Transition from Lazy to Rich Training Dynamics, arXiv 2310.06110, Sec 4 Eq 3, Sec 5.2 Fig 3b and Sec 5.3. With phi = h + (eps/2) h^2 in Gaussian quadratic regression, smaller eps lengthens the delay, and the linear component hurts test loss.
  - Ours: GELU and SiLU on modular addition, a threshold near r 0.27, one monotone curve across two activations (Spearman -0.886 over 15 runs), and projection exactness as the measure.
  - Derivation: f(sz)/s keeps the odd part at z/2 and grows only the even part, (z/2) erf(sz/sqrt 2) for GELU and (z/2) tanh(sz/2) for SiLU. So s is a pure even-part knob.
  - SiLU(sz)/s is Swish with beta = s (Ramachandran et al., Searching for Activation Functions, arXiv 1710.05941, Sec 4).
  - Lin, Tegmark & Rolnick make their product gate exact by shrinking pre-activations, the opposite direction. That works because their mirrored neuron pairs cancel the odd part exactly. Trained one-wave nets have no such pairs.
- The odd part hides the adder.
  - He footnote 2 has the linear part cancel under phase symmetry. Yip App I finds it a small help.
  - Liu & Lu Sec 3.1 say ReLU stores label noise non-symmetrically.
  - Kumar et al. Sec 5.3 and App 8.3.2 blame the linear component for worse-than-random test loss, in Gaussian regression.
  - Wang App C.1 sets the second-order term against higher-order terms at large scale, not against the linear term.
  - Ours: at finite width with a small even part, the linear term does not cancel. It swamps an adder that the even read-out shows is exact. The searchers read this as the finite-width remainder of He's cancellation.
- Scope a referee will press.
  - Gromov Sec 2 says the results are "only mildly sensitive to the choice of activation function". T2 should answer that line directly.
  - Limit the tanh claim and "the odd part writes nothing" to bias-free nets with one hidden layer and cosine-wave neurons. Four results show why:
    - Manir & Rupa, A Systematic Empirical Study of Grokking, arXiv 2603.25009, Sec 5.4 Table 4: biased depth-4 tanh MLPs grok in 2 or 3 of 5 seeds.
    - Lin, Tegmark & Rolnick's bias shift.
    - Huang & Li, Provable Benefits of Sinusoidal Activation for Modular Addition, arXiv 2511.23443, Thm 4.2: sine is odd, yet it solves the task exactly through a linear phase.
    - Salah & Yevick's x^3 net peaks near 0.65 test accuracy, not chance.
  - Weigh the size of the even part, not only its presence. ReLU's |z|/2 is first order; GELU's even part, about 0.40 z^2, and SiLU's, about 0.25 z^2, are second order.
  - Moniri's Gaussian theory reverses the roles (c1 sets the learned direction). "Information exponent" is a property of the target; on the activation side the condition is c2 != 0.
  - Do not cite Holzmuller Table 1 for SiLU. It lists SiLU's odd part as non-polynomial, but the odd part is z/2.

3. Not found in any opened paper
- A wd-0 GELU or SiLU memorizer whose projection is exact under x^2, |x| or its own even part from step 20 to 50, while its own read-out is wrong on thousands of pairs.
- GELU or SiLU weights read with their own even part, (f(z) + f(-z))/2. For ReLU this read-out is reported: |x| is twice ReLU's even part (He, Wu, Stander).
- Pre-activation scaling f(sz)/s on modular addition, a threshold in the even/odd ratio, or one curve across GELU and SiLU.
- A net trained with |x| on modular addition, or an exact projection of one at every checkpoint.
- A projection of a tanh net, or a null result under even read-outs.
- An explanation of Gromov's GELU result.
- The statement that the linear term hides an exact adder at read-out.

4. Most expected citations
- He 2602.16849: Table 1, Obs 4, footnote 2.
- Wang 2610.11833: Prop 1, Thm 1, App B.
- Gromov 2301.02679: App B Fig 6, and the Sec 2 line.
- Next: Salah & Yevick 2411.05353 for the knob, and Liu & Lu 2605.18022 for activation swaps in memorizers.

Scope:
- Two searchers and a refuter.
- About 50 web searches and a dozen arXiv-API queries.
- Forward citations of eight anchor papers, about 210 citing titles screened. The citations of Wu 2410.07476 could not be crawled (HTTP 429).
- About 40 papers opened.
- Values from Gromov Fig 6, Liu & Lu Fig 5, Salah & Yevick Figs 6-7 and Holzmuller Table 1 were read off rendered figures and are approximate.

CORRECTIONS TO /Users/thomas/lean-checked-network/.claude/worktrees/project-direction-next-steps-a594e6/experiments/mlp-sweep/results/prior_art_2026-11-01.md
- Line 183 says Barak 2207.08799 has no one-step claim. It has one: Sec 4.1 footnote 9, Thm 4 in App B.1, and Prop 9 in App B.2. A searcher and the refuter both checked the PDF.
- Lines 156 and 193 grade Kumar & Sankaranarayanan 2610.22593 as not close and report nothing at steps 0 to 1 in the first 40% of the paper. Thm 4.2(iii), which comes later, is the closest weaker statement to the one-step result.
- Wang 2610.11833 App B (the second-order term is the key, and tanh lacks it) is prior art for the even-part reading. The earlier search missed it.
- Liu & Lu Fig 25: one searcher found only 40% to 60% training ratios in the text (App C.1). The refuter's full-text check of the Fig 25 caption lists ratios 0.15 to 0.5, which supports the ratio on line 135. The accuracies on that line remain a figure read that has not been re-verified.
