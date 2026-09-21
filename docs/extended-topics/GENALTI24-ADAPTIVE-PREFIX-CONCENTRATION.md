# Genalti concentration: fixed-prefix transfer to adaptive counts

Date: 2026-09-20. Proposed corollary for separate review. Prerequisites: reviewed root and split-mean reconstructions in genalti-root-concentration.md and genalti-split-mean-concentration.md. This proof concerns confidence events, not regret or arbitrary stopped conditional laws.

Fix p in (1,2] and finite u>=0. Each arm law satisfies integral |x|^p<=u, and mu_i denotes its integrable real mean. Here t is the source paired-round counter tau, not the physical pull counter 2tau. For each arm i in a finite K-arm model, realize two infinite independent iid reward streams of law nu_i; the two streams within an arm are independent, and assume the usual independent product model across arms for a causal paired-pull realization. Each paired pull of an arm reveals the next unused coordinate from EACH of its two streams. Each stream retains duplicates. No future observation is used to choose an arm. The prefix probability arguments below need only each arm's two-stream law, but the causal product model identifies these variables with the actual paired algorithm's observations. If the real environment does not admit this stationary iid stream representation, this corollary is not an adapter for it.

At integer paired round t>=2 and prefix length 1<=n<=t-1, put delta_t=t^(-3) and L_t=log(t^3). In particular delta_t<=1/8<1/4. Let E_i,n,t be the unique-root event for the first n threshold-stream observations, with target cL_t, c=(1+sqrt2)^2. Let Mhat_i,n,t be that root on E and muhat_i,n,t the truncated average of the first n OTHER-stream observations. The frozen count is n per stream, total estimator sample count2n. Define
A_i,n,t = E_i,n,t intersect {|muhat_i,n,t-mu_i|>8 u^(1/p)(L_t/(2n))^((p-1)/p)}.
All fixed-count premises are satisfied for n>=2. For n=1, E is empty: cL_t>=c log8>1, exceeding the possible nonzero count. Thus P(A_i,n,t)<=4/t^3 for every listed n.

Define B_i,t=union_{n=1}^{t-1} A_i,n,t. A finite union gives
P(B_i,t)<=4(t-1)/t^3<=4/t^2.
This is a fixed round's simultaneous-in-prefix event. It is not obtained by applying a fixed-count iid theorem conditionally at a stopped count.

Let N_i(t-1) be any measurable random count in {0,...,t-1}, including one depending on both observed streams and all arms. The event that N_i(t-1)>=1, the corresponding unique root exists, and its actual prefix mean violates the displayed n=N_i(t-1) bound is contained pathwise in B_i,t. Hence its probability is at most4(t-1)/t^3. No independence of the two prefixes CONDITIONED ON THE RANDOM COUNT is asserted or needed. For a random selected arm, a union over arms costs at most4K(t-1)/t^3, unless a more specific selection argument is supplied.

For a fixed arm and finite horizon H>=2, the expected number of rounds t=2,...,H with an adaptive-prefix failure is at most
sum_{t=2}^H 4(t-1)/t^3 <=4 sum_{t=2}^H 1/t^2<=4.
The last inequality uses 1/t^2<=1/(t(t-1)) and a telescoping sum. For two FIXED arms (e.g. a specified suboptimal arm and a fixed optimal comparator), a union costs at most8 expected failure rounds. These are counts of failure rounds, not rewards or regret. No all-time probability1-4 statement is used; the crude numeric union bound is useful for expectation accounting even when a probability bound would be trivial.

The root-bracket theorem alone yields the parallel prefix bound 2(t-1)/t^3 for a fixed arm, with its own two-sided root-good event. If both that bracket and the split-mean endpoint are needed simultaneously, their probability budgets must be tracked jointly; adding the two marginal budgets is a valid but possibly loose bound. Do not silently count a shared root event twice or assume unrelated events coincide.

This resolves adaptive COUNT transfer for these particular confidence events under the explicit two-stream causal representation. It does not itself prove the empirical-variance index confidence, a bound on forced exploration, correctness of the original guard, Eq57's count threshold, a total regret bound, or an odd-horizon action convention. No Lean implementation or whole-topic completion is asserted.

## Publication boundary

This corollary is bound with its separate reviews in `runs/extended-topics-20260919/genalti-concentration-audit.json`. It adds no production Lean declaration or site/graph claim. Root and split-mean proofs are in `GENALTI24-ROOT-CONCENTRATION.md` and `GENALTI24-SPLIT-MEAN-CONCENTRATION.md`. All-ten completion and ICLR obligations remain unchanged. This is an explicitly mathematical stream-to-prefix adapter, not a compiled adapter.
