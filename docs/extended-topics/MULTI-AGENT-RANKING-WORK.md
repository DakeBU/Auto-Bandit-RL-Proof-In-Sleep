# Actual empirical ranking and source exploration event work

Source: Rosenski--Shamir--Szlak ICML2016 static Algorithm1 and supplement A.1
Lemma2/3, frozen MULTI-AGENT-CONTRACT.md. Target: actual fixed-tie descending
empirical sort, retain the actual local population estimate, prove nonempty
candidate outputs on every valid local history and common true top-n sets on
the existing joint mean/population event. Then prove the source exploration-good
event probability>=1-delta on the same law at the exact explorationLength.
Owner: runs/extended-topics-20260920/MusicalChairsRankingPrototype.lean.

Reuse: compiled private sort trial, Finset.sort/length_sort/pairwise_sort and
sort_nodup; List.take_sublist, pairwise_append and take_append_drop; finite
cardinality equality. Ranking comparison is score-descending then index-ascending,
so ties are deterministic without assuming distinct within-top means. Exact
boundary separation transfers from true means to empirical scores via eps/2
accuracy and eps<gap. The known true top set and n occur in analysis only.
Actual candidates use localPopulationEstimate/localEmpiricalMean only.

Measurability must be proved, not inferred from algorithm syntax; finite
order-comparison events provide a route. Keep all count/duration domains and
bad-event candidate nonemptiness. No future feedback or conditioned successful
loop may define the policy. Full coordination continuation/regret remains open.

Plan independent source-blind reconstruction and source review of the full new
chain, standard axiom audit, exact folded reader, and conservative ledger update.
No public-root integration or full gate claim at scratch stage.

## Compiled source-event endpoint

Actual sort/prefix/cardinality and all-history candidate nonemptiness compile.
The strict cross-gap transfer consumes actual local mean accuracy and actual
Nhat correctness. explorationGoodEvent explicitly asserts actual Nhat=n and
localCandidateSet=S; comparison-based characterization proves its measurability.
The same-law probability producer gives the canonical trueTopArms event>=1-delta
at exact explorationLength. Bounded reward laws imply means in[0,1]; nonempty
top/complement sets givegap<=1 and remove an extraeps<=1 endpoint premise.
The cross-set separation model is explicit; no numeric order-statistic gap
function was added or claimed. Continuation and full regret remain open.

Focused compilation exited0; separate axiom audit exited0 for44 new named
declarations:40 scanned (30theorems,10definitions), plus four explicit
order/decidability instances. Only propext, Classical.choice and Quot.sound.
Nine canaries cover actual sorting/ties/truncation, all-collision candidates,
and differing actual local empirical vectors with equal selected sets.
Independent semantic evidence is bound in the separate ranking receipt.
No new public root/Tests/harness/site gate is claimed for scratch.

Compiler fixes were interface-level: mark exact real-rational score definitions
noncomputable, supply explicit distinct Fin3 numeral facts instead of looping
Fin.ext_iff simp, and use simp_all after finite case splits. These did not
change any mathematical target, algorithm choice or probability assumption.

## Next continuation boundary

Production jointDraw already accepts a family of nonempty local candidate sets;
transition/stateLaw use it without a common-set hypothesis. The performance
module's<=8n^2 endpoint currently assumes a common supplied S. Next must derive
that common family from the actual explorationGoodEvent and construct the fresh
continuation law, retaining total nonempty candidates on bad histories.

Potential finite-configuration route: encode candidate families as a finite
subtype satisfying per-player nonemptiness, prove the actual candidate-family
map measurable via its equality/comparison characterization, build a countable
kernel with Kernel.ofFunOfCountable, then pull it back along that actual map.
This is a proposed API route, not a proved conditional law. A real path/marginal
identity must connect fresh causal draws to the existing stateLaw/regret sum;
merely reusing a fixed-S consumer is insufficient. Global true-top comparator
optimality/boundedness and the delta*n*T residual remain explicit obligations.

Reviewer wording correction: the final probability model uses fixed per-arm
laws sampled independently across arms and rounds, independently of exploration
coins. The reader now states this explicitly; it does not allow time-varying
reward laws or claim independent per-player reward arrays. Code and folded
code were unchanged by this prose clarification.

The private next-step continuation-api.lean compiled an equality-fiber
measurability lemma for each actual local candidate output, without assuming
population correctness or S.card=n. It is a useful candidate-kernel producer
but is not included in this checkpoint's audited/reviewed declarations and
does not establish a fresh continuation or path/marginal law.

Independent source review accepted with explicit delta after the fixed-law prose
clarification; it matches the completed blind reconstruction and binds the new
reader hash. Source numeric order-statistic gap adapter remains explicitly on
the ledger, rather than treating the current cross-set formulation as proof of
that unencoded interface. Final scratch receipt binds all44 audit names,
unchanged context, exact fold and review artifacts.
