# Batch40 phase 3 independent body, definition and reuse review

Verdict: **accepted-with-explicit-delta** for the six original production bodies, the complete two canaries, and the bounded valid-domain definition/reuse obligations. No blocking body or definition repair is identified. Original production and test bytes remain unchanged. D1-D7 from phase2 remain visible. This is not source-correction approval, a whole-carrier literal-definition seal, a full-project gate, reader approval, publication, or final candidate acceptance.

## Exact scope and verified compilation

The reviewed worktree W is `candidate-worktree`, branch `codex/online-ch2-prescient-source-integration-20261105`. Its base is M=`0bf7485af39beb87cbf7aeb66ef5c9074fa7d2cf`. Validation worktree V is `validation-worktree` at the same base. Both use the shared project and pinned dependencies.

I independently verified in W and V the exact original production SHA256 `57832c9dfb4e915f9a0578ffb122792b0aac2b3404da4f6c00f2aa9fcd36bc02` and complete canary SHA256 `1cd6d7f26f4c9fed1fa476e1f5360823d3e3b3f743eedfe100c840cf9a345a40`, plus both additive-root import hashes from the preparation/compiled receipts. The tracked root diff consists of one import in BanditRLProof.lean and one in Tests.lean. All 12 inspected production/test parent files match their contents at M, modulo line endings. No parallel library or replacement shared definition was introduced.

The focused-build receipt SHA256 `f6b7f9a69ca9ec8babf5065a382f6a2b2338fda8830c6d059233c0d596577e72` and its actual log agree: the two target modules built successfully, exit 0, 3317 jobs. This is focused compilation, not the combined project gate.

The public-probe receipt SHA256 `5a2790d5ca17cd4dba8551ab3c6706123137234635a1775078cb3426b45a027a` has four terminal exit-0 commands. I checked all probe/log/source hashes, the actual graph (`88b9a261774b5479a00873d21bceb7b25b8867ca6f434ed555fd89851375539a`), and the independently selected numeric branches (`c7495c6028140e7398de2c9cc07ebae2ac01f6aced07451ad52aca122fa6cf4d`). I compared the six and two typed application headers to the original files, including all 8 and 6 canary conjuncts. All 16 original/application axiom lists were parsed from the raw logs and contain only propext, Classical.choice and Quot.sound. All 22 required direct VALUE dependencies are present. No placeholder or extra axiom was found in the selected theorem dependency evidence.

The graph has 8 selected theorem nodes and 1431 coalesced direct TYPE/VALUE constant-presence edges. These are not occurrence counts, a complete transitive source graph, or a count of source mathematical contributions. Diagnostic tools use unsafe IO to read the compiled environment; they are not production proof axioms. I did not run a competing build.

## Six production bodies

1. `sourceProper_of_domain` selects a point in nonempty V and uses hdom plus hbot to invoke EReal.coe_toReal. It constructs precisely the finite witness in SourceProper. No closedness, convexity or optimizer is manufactured.
2. `penalized_strictConvex` calls the accepted finitePart_convex_of_subdifferentiable, obtains psi's strict Jensen inequality, explicitly distributes the fixed continuous-linear derivative term, and combines strict penalty curvature with convex loss under inverse eta>0. An arbitrary center is legitimate here because only affine algebra is used. It never infers source Bregman nonnegativity at an invalid center.
3. `advance_eq_some_of_minimizer` first proves every feasible f-value finite using proper global support. It transports both the supplied and chosen minima through proximal_finitePart_minimizer_iff. Mathlib StrictConvexOn.eq_of_isMinOn identifies the chosen point with p. The existential witness used to enter advance's some branch is exactly the supplied hp/hmin pair. There is no hidden existence theorem or default point.
4. `iterate_eq_of_source_updates` uses induction. The base is hinit. The successor obtains t<T from t+1<=T, rewrites the already proved previous some-state, and applies the new unique-minimizer transport to the given next update. No future loss or comparator influences the recurrence.
5. `source_fixed_regret` produces properness from the source codomain/domain premises, produces optional-run agreement from the supplied exact updates, and applies the accepted iterate_fixed_regret. It consumes the properness and iteration adapters rather than merely restating a parent with its conclusions as assumptions.
6. `source_variable_regret` performs the analogous domain/properness and update transport before applying iterate_variable_regret. Positive horizon and previous-state max semantics are retained. Both endpoint bodies leave _hVc and _hpsic unused syntactically, while retaining them as required source contract premises. Their nonuse is not a reason to erase the printed assumptions.

## Actual alternative proof route and source gaps

The implementation does not use the source's problematic nonsmooth invocation of Theorem2.8. The accepted chain is:

`source_*_regret -> iterate_*_regret -> iterate_*_sharp / iterate_divergence_sum -> iterate_one_step -> proximal_one_step_extended -> proximal_one_step -> convex_minimizer_comparison`.

The extended bridge establishes real-valued convexity only on V from proper global supports, with each finite-part conversion justified there. The finite minimum-order bridge compares the same actual extended-real penalized objective to its real restriction. It does not assert global convexity of loss.toReal outside V and imports no loss differentiability/closedness premise.

The real comparison theorem considers q(a)=p+a(u-p) and H(a)=a(f(u)-f(p))+h(q(a))-h(p). Convexity plus the supplied minimum proves H>=H(0)=0 on [0,1]. Only the differentiable penalty h is differentiated. The feasible right tangent at zero gives H'(0)>=0, hence f(p)-f(u)<=Dh(p)(u-p). The Bregman penalty derivative and shared three-point identity then give the signed one-step bound. This is a real proof under the declared inputs, not the author's displayed smooth citation or an assumed first-order subgradient result.

The sum theorem divides by each positive rate and sums. The fixed sharp bound uses sum_range_sub' and preserves the terminal comparator divergence. The fixed printed bound then deletes that nonnegative quotient using source-valid divergence_nonneg. Thus the constant-rate exercise has an actual implementation completion, while remaining an omitted proof in the source graph.

The variable sharp bound reuses weighted_potential_sum with a(t)=2*B(u,x(t)) and C=2*M; cancellation of the factor two is explicit, leaving exactly the source coefficients. The previous-state finite maximum supplies hbound, and the nonnegative terminal quotient is deleted only afterwards. No bounded domain or uniform all-time diameter is inserted.

Consequently the implementation obligation is discharged by a derived alternative route and an exercise completion. The source citation gap itself is not repaired, the source graph must not be rewritten to claim the author gave this argument, and D2's extra-index discrepancy remains unchanged. No source correction is approved by this review.

## Complete bounded definition evidence

`advance_some_spec` proves the selected point satisfies membership and the exact minimum relation. `advance_none_iff` characterizes failure by absence of any feasible minimizer. The new `advance_eq_some_of_minimizer` proves the converse some-value identification under the exact proper/support/strict/positive library inputs. Together these named results provide the complete valid-domain optional-selector characterization and uniqueness: any two feasible minimizers identify the same some-value and hence are equal. Conditional existence comes from the supplied minimum, not from closedness. A redundant new combined iff/ExistsUnique wrapper is not required for this bounded interface review.

`iterate_succ_some_spec` recovers every successful next-step update and its preceding some-state. The new `iterate_eq_of_source_updates` supplies the forward valid-prefix direction, with initialization from the recursion. Existing iterate_prefix and iterate_no_recovery retain finite-prefix dependence and absorbing failure. This closes the bounded relation/recursion correspondence. It does not assert universal attained or interior runs.

I inspected `divergence_extension_eq`: EqOn psi phi X and an interior reference yield eventual equality on a neighborhood, Mathlib's EventuallyEq.fderiv_eq gives the derivative equality, and equality at the first argument and reference closes the divergence equation. Its exact carrier is first argument in X and reference in interior X. The accepted `divergence_eq_gradient` uses differentiability and HasGradientAt.fderiv_apply to identify the continuous-dual expression with the source gradient pairing in a complete real inner-product space. Finite-dimensional endpoints supply completeness and actual interior differentiability. These are actual bodies, not just suggestive names.

This substantiates representative independence and gradient correspondence on the reviewed source-valid carrier. It grants no whole-carrier literal Bregman or optional-algorithm seal, no boundary-reference independence, and no arbitrary-coordinate/matrix transport certificate. The accepted boundary counterexample explicitly distinguishes two extensions agreeing on X at a nondifferentiable boundary reference. The accepted exponential example also proves that closed strict regularity alone need not produce an argmin. Both boundaries remain valid and are not diluted by the new endpoints.

## Full canaries and numeric consumption

The fixed canary's 8 conjuncts are all present and proved: proper first loss; strict penalized first objective; advance=some 0; complete three-state prefix; movements 11/64 and 9/64; every-comparator source_fixed_regret instance; and the final numerical inequality -9/8<=5/16. The properness, strictness, choice, sequence and endpoint conjuncts consume the corresponding new production declarations. The final branch specializes the NEW endpoint at u=-1/2 and converts its two sides using explicit loss/movement values. The movement sum is 20/64=5/16; initial comparator divergence is 5/8, giving upper bound 5/16.

The decreasing canary's 6 conjuncts are: full prefix for rates 1 and 1/2; weighted movement 29/64; previous-state max 5/8 at negative comparator; previous-state max 9/64 at positive comparator; every-comparator source_variable_regret instance; and -1/2<=-11/64. At u=1/2, max divided by the final rate is 18/64 and movement is 29/64. The final numerical branch consumes the NEW source endpoint and the concrete max/movement values.

The accepted parent canaries construct actual minima and unique next states using nonsmooth absolute loss, polynomial regularizer, and explicit positive polynomial factorization for the second update. They do not depend on the new source module. Recovering hmin from those established runs and rechecking the new source transports is therefore not a proof cycle. The examples have positive-infinity values off V and a genuine nonsmooth loss at zero.

The compiled numeric auditor substitutes top-level lets, removes only metadata/explicit id, selects each And.intro conjunct separately, and checks its actual expression constants without unfolding or proof-irrelevance normalization. The zero-based branches 7 and 5 both have head Eq.mpr and contain their required new production endpoint. This establishes syntactic proof-value consumption of the endpoint in each numerical tail, not merely a whole-conjunction dependency or standalone arithmetic success. It does not claim the endpoint is logically indispensable to an inequality that is independently numerically true.

## Reuse and purification result

All shared definitions are reused. The new source endpoints are useful contract adapters: they replace parent implementation premises (proper losses and optional-run equality) with the literal source codomain/domain/update relation and preserve printed closedness. They are not duplicate source theorems earning new mathematical credit. Their small wrapper bodies are justified at the source interface.

Properness is a small adapter used by both endpoints and canaries. Penalized strictness is a specialized composition used by uniqueness and its canary, not a new convex-analysis discovery. Mathlib already supplies generic convex-plus-strict-convex and strict-minimizer uniqueness results; the implementation reuses the latter, and its explicit affine arithmetic is legitimate specialization rather than a separate redundant framework. The iterative transport is induction over the existing recursion, with actual endpoint consumers. No dead new declaration or mutually duplicate new proposition was found. Broader repository-wide minimal-import and performance optimization remains ordinary purification, not a reason to remove original scope or change frozen proof bytes here.

## Required before source publication

No additional production proof or definition theorem is required by this bounded body review. Publication must still: retain D1-D7; identify the direct convex-segment implementation route and source-omitted exercise separately; preserve supplied-valid-run conditionality and both failure/domain boundaries; expose the initial/post-update index mapping and previous-state max; keep whole-carrier definitions labeled as library interfaces; and retain all original 8+6 canary conjuncts and six declarations.

The full combined root, Tests and harness gates, complete scope/conservation artifacts, reader/exposition review, final candidate checks, integration, and live publication verification remain separate. Focused compilation and selected dependency checks do not substitute for those gates. No whole Chapter15/book completion or generic numerical solver claim follows.

## Integrity and disposition

Only create-only phase3 evidence files were written by this reviewer. No production edit, new proof construction, build, remote mutation or worktree retirement was performed. Existing phase1/phase2 artifacts remain preserved. The receipt binds inspected original/parent/Mathlib files and terminal validation artifacts, and distinguishes accepted bounded obligations from future publication/project gates.
