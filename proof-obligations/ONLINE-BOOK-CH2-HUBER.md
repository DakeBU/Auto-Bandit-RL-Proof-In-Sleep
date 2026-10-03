# Example2.15 obligations

Task id: `ONLINE-BOOK-CH2-HUBER`
Kind: `theorem`
Status: `accepted-local`
Harness: `hierarchical`

Source v10 pp15-16/PDF27-28. Required: exact Huber loss; delta>=0 including zero; both seam derivatives; source sign-gradient formula; global convexity; real Euclidean feature pullback gradient and bounded-feature estimate; actual full-space projected OGD (identity projection), comparator-independent horizon step and sublinear regret/vanishing upper average regret. No bounded-domain premise. No full-sequence algorithm choice.

Current frozen leaf: online-huber-derivative-v1 (global derivative join and actual scalar derivative). Prior seam/scalar scratch candidates remain unpublished. Later source terminals require exact typed contracts before proof work. Accepted-local requires public canaries, axioms, root/Tests/full harness, graph and shared Book/site mapping, with integration against current main explicitly checked. No Chapter2 closure.

Update: scalar convexity/source derivative, vector gradient/convexity/bound, actual full-space projection/regularity/update and fixed-step residual regret all have frozen compiled scratch candidates. See runs/online-huber-20261003/05_chain-review.md. Remaining: horizon tuning/vanishing upper average regret and all public acceptance gates.

Final Example2.15 acceptance:19public targets and all combined current-main gates pass. Evidence: runs/online-huber-20261003/acceptance-decision.md. Earlier proving/scratch paragraphs are historical. Chapter2 remains incomplete.
