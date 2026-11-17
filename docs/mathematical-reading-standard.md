# Mathematical reading standard

This standard applies to library lessons, research pages, and both natural-language
and Lean BanditRLBench tasks. Authors and reviewers use it alongside the theorem
publication protocol and the benchmark task protocol. Public content is English.

## Reading order

Keep the first view short. Show the question or result, its essential assumptions,
and a short orientation. Use labelled diagrams to explain a dependency, a sequence
of operations, or a counterexample. Provide equivalent text for every diagram.
Put detailed derivations, exact Lean, and provenance in named disclosures. A
reader must be able to locate every substantive proof step from the overview.

For a library lesson or a revealed benchmark solution, use this order:

1. **Setup.** Define the objects, notation, domains, dimensions, index conventions,
   assumptions, and parameter range before using them in a derivation.
2. **Claim.** State the precise guarantee and explain what its quantities mean.
3. **Proof idea.** Describe the mathematical moves and why they establish the claim.
4. **Derivation.** Give the intermediate steps. For each substantive equality or
   inequality, name the definition, assumption, or lemma that justifies it.
5. **Scope.** Explain boundary cases, extra assumptions, and unresolved obligations.
6. **Evidence.** Link the primary source and the exact formal statement, proof,
   and actual dependencies where available.

Use standard LaTeX with consistent notation. Explain important displayed formulas
in nearby prose. Check matrix shapes and units where applicable. Long equations
must remain readable on mobile and with the formula renderer unavailable.
An illustrative example should clarify a defined claim and retain its assumptions.

## Probability and algorithms

For a stochastic claim, specify the probability space or law, random variables,
conditioning, and expectation. State measurability and integrability requirements.
For sequential claims, state the history/filtration, when actions are selected,
what feedback is available, and the horizon or stopping-time convention. Define
covariance when it is used. Identify deterministic, almost-sure, expectation,
and high-probability conclusions precisely.

For algorithms, state inputs, outputs, assumptions, execution steps, stopping
rule, resource model, and applicable convergence, stability, or error guarantee.
State the regime and parameter dependence of each complexity bound. Compare
methods under explicitly matched objectives, access models, and accuracy.

For quantum algorithms, also specify state encoding, preparation, oracle and
inverse access, coherent memory, queries, shots, gates, depth, readout, and error
accounting as applicable. Support any claimed advantage with a comparison under
those contracts. Identify the cost of loading data and producing the output.

## Sources and evidence

Attribute each substantive external result to its original paper or book with
version and theorem, page, or section locator. Include a verified DOI, arXiv ID,
or original publication link when available. Record preprint versus published
status. Verify current claims by retrieval and record the date and source version.
Mark unverifiable citations and conclusions as unresolved.

Label the evidence attached to each claim accurately: cited theorem, local
kernel-checked proposition, reviewed mathematical argument, numerical check,
empirical observation, or conjecture. State whether a derivation is original or
adapted from a source. Preserve the distinction between Lean acceptance and the
independent review of the correspondence to the cited source.

## Benchmark prompts and revealed solutions

The agent-facing prompt supplies the definitions, assumptions, allowed access,
and requested output needed to make the task well-posed. Keep proof ideas,
solutions, rubrics, and evaluator evidence in the appropriate reviewer/solution
view. A task may explicitly ask the model to discover a missing assumption or
definition; describe that objective without supplying its answer.

In Lean QA, display the exact graded target before reference proofs. Label the
relationship between that target and its parent natural-language problem. Put
the formal reference and parent explanation in separate disclosures. For
non-Lean QA, distinguish the argument from its grading criteria. Rubrics should
credit mathematical validity, justified steps, and correctly identified limits.

Editing a sealed task's mathematical content requires a versioned successor and
fresh review under the task protocol. Presentation changes must preserve the
sealed question, reference content, and export behavior.

## Review and acceptance

For each changed page, record the route, the reviewer, identified defects,
repairs, and remaining gaps. Check symbols and assumptions, the justification
of each mathematical move, evidence status, source links, and formal scope.
Include desktop/mobile and rendered-formula checks for changed layouts.

Structural CI checks and visual checks establish their stated properties.
Independent mathematical review supplies the semantic verdict. Record both
separately. Existing pages acquire an accepted exposition status only after
their own review; the publication of this standard does not certify the archive.
