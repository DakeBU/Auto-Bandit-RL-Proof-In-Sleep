# OSD v3 source-contract review

Verdict: **accepted-with-explicit-delta**, solely for stabilization of the exact standalone Lemma 2.31 header and structural selector/recurrence definitions. Actor `/root/source_reviewer`; requested GPT-6 Astra / medium, distinct automated review, external_human=false. Runtime model identity is not independently verified. No target proof body was supplied or accepted.

The original pinned PDF was independently rehashed and freshly extracted across physical28-33. Definition2.20 and its subdifferentiability paragraph, Lemma2.31 printed19/PDF31, Algorithm2.2 and Example2.32 printed20/PDF32, and the printed21/PDF33 constant-step discussion were read. Digest: `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`. All five v3 contract files, active pointer/repair, fresh blind packet/reconstruction/receipt and context03 evidence were read. Actual shared interfaces were reread at SourceProper, SourceSubdifferential, subgradient_point_finite, Domain, project, project_spec and proposition_2_11. Whole dependency files are hashed; unrelated declarations are not newly certified.

## Seven semantic slots

1. **Objects.** Finite-dimensional real inner-product space represents source Euclidean Rd, including zero dimension. Domain supplies precisely nonempty closed convex V. Imported project is the actual constructed nearest-point choice with its distance-minimization specification. Finite dimension supplies completeness. No arbitrary next-point oracle or full-dimensionality restriction is introduced.
2. **Hypotheses and quantifiers.** Source Definition2.20 explicitly defines supports for proper functions. SourceProper inside SubdifferentiableOn thus inherits the source convention. Every feasible point has a support tested globally at every ambient y. The lemma takes arbitrary ambient x, every supplied actual global g at x, and every feasible comparator u. No global convexity, differentiability, boundedness, interior or support-norm premise is added. Removing hx repairs the genuine v2 narrowing of the standalone source lemma.
3. **Finite values.** Properness supplies a finite comparison witness. The given hg at arbitrary x excludes top via that witness; properness excludes bottom. At u, hu plus all-feasible-point subdifferentiability provides a support and the same argument applies. Actual subgradient_point_finite proves the top exclusion without convexity or x feasibility. Future proof must perform the finite conversions before interpreting toReal differences; unconditional toReal itself is not a finite-value witness.
4. **Exact conclusion.** Both inequalities retain eta times the finite loss difference, eta inner(g,x-u), initial squared distance divided by two, minus projected terminal squared distance divided by two, and eta squared divided by two times norm(g) squared. Eta is positive and the same arbitrary g appears throughout. The source next iterate is replaced by its exact projection definition. Actual proposition_2_11 accepts arbitrary z and only feasible u, so no hx is needed. No desired inequality is a premise.
5. **Information.** currentSubgradient accepts only current f,x, chooses from the actual global support set if nonempty and otherwise returns zero. This is noncomputable whole-function choice, not an executable finite-query oracle. iterate0=x1; iterate(t+1) reads loss(t), eta(t), iterate(t), structurally matching output before the current-loss update. Source round1 corresponds to Lean0. Externally supplied initialization and schedules are not constrained against future information by these definitions alone. Algorithm2.2 feasible initialization, selector correctness, all-round feasibility and formal prefix causality remain distinct proof obligations; they do not restrict the standalone lemma.
6. **Degeneracies.** Zero-dimensional E, singleton/lower-dimensional/unbounded V and empty interior remain admitted; empty V is excluded. The theorem excludes nonpositive eta but definitions do not. T=0 is an empty regret sum. Infinite values at other ambient points remain permitted. Generic regret only sums real projections until later hypotheses establish finite trajectory/comparator values. No blanket support existence outside V is asserted: the arbitrary query is covered when its hg is supplied.
7. **Blind comparison and status.** Fresh v3 decoding accurately reconstructs arbitrary x, properness plus actual hg finiteness, both exact inequalities and global support semantics. Tool comparison confirmed the v3 header equals v2 with ONLY hx removed, context raw bytes are identical, and native JSON statement equals whitespace-collapsed header. Context03 log/exit shows definitions/selector compilation and standard three axioms only, not a proof or compilation of Lemma2.31. Earlier failed context/preparation evidence is not promoted to proof success.

## Decision boundary

The native fingerprint is `c0c785c373909f3b27cea91e44a85f90a7e94a3036f5c167bc2ac95a7f529462`. Explicit representation deltas: coordinate-free finite-dimensional Euclidean space, EReal with inherited properness and required finite conversion, conjunction/elimination of the named next iterate, and zero-based indexing. They do not narrow the source lemma. No further source-header repair is required for v3. The historical v2 rejection remains valid and unchanged; this is a new reviewed version.

Only the single-step header and structural definitions are stabilized. Fixed-step, variable-step and tuned regret statements must each receive exact separately frozen headers and source reviews; manifest names are a roadmap, not completed contracts. Selection correctness, feasible iteration, formal strict-prefix causality and finite regret must be proved. Example2.32 remains mandatory subsequent work. No target proof, public/root/Tests/harness/site/reader/immutable-binding/PR acceptance is certified. Goal, Chapter2/book, older migration and main/live remain open. No production, contract, old receipt, DAG, trial or frontier was edited.

## Raw SHA256 inventory

Exact raw bytes without normalization or JSON reserialization. Dependency inspection scope is stated above.

| File | Raw SHA256 |
|---|---|
| `docs/contracts/online-osd-v3/context.txt` | `b162f92f05924622d248b0673321078b35330dc3980f7b53c1adc4ba64087a5c` |
| `docs/contracts/online-osd-v3/contract-manifest.json` | `784689fec9709ffb4d7e4f1fe8eb1e4cb80a52e1c3fa264084e42db855edd577` |
| `docs/contracts/online-osd-v3/contract.md` | `d149d6bdef5a04eb863f3e131b3569c3da0bc51ac77f28ac3a8976af283bf02e` |
| `docs/contracts/online-osd-v3/lemma_2_31-header.txt` | `aebea9f6cabea55adb5ccc9ac57fde75e8092c101aeb0c0cdb0c3283dda1ce9d` |
| `docs/contracts/online-osd-v3/lemma_2_31.json` | `c6b9af9a1f7774d108671ac1e6195ac4853615b8193ae0d281e9e00c145f6f19` |
| `runs/online-osd-20261004/active-contract-v3.json` | `793e86aa64d13fd3a8064d99734402fb4e9256be99f8d94e5ae5f982b62df4a2` |
| `runs/online-osd-20261004/source-contract-repair-v3.md` | `1d47870aba7ac49d5d718460e7473d56a820c1ed9739adb35031f2a3e89ad714` |
| `runs/online-osd-20261004/blind-packet-v3.txt` | `fd38ff61544e34581ea8c25f0c0b73d55a8700314d55557f5becd713c4879b76` |
| `runs/online-osd-20261004/blind-reconstruction-v3.md` | `eb4ce0a9624519a27b82d0cf1fc4c1064e32e3a4761536aa609c72265d4327d0` |
| `runs/online-osd-20261004/blind-receipt-v3.json` | `549c920188ae910ed4b7c5b8b22d89c9321fc72d833fdbb3ea713859262a3e2b` |
| `runs/online-osd-20261004/context-probe-03.log` | `ca4e75580856533bbb825429aeb98b023082f53c3495f3233a544cffb6857194` |
| `runs/online-osd-20261004/context-probe-03-exit.json` | `a50f37d35ca5e0f0ae948630d13491aa2228d7c959a989005cea475d777d4b86` |
| `docs/contracts/online-osd-v2/context.txt` | `b162f92f05924622d248b0673321078b35330dc3980f7b53c1adc4ba64087a5c` |
| `docs/contracts/online-osd-v2/lemma_2_31-header.txt` | `f0a97dd2e79050e43c54c778145e75f3a04d57279d72f3d0c842af19cdf6720d` |
| `BanditRLProof/OnlineGradientDescent.lean` | `e7edba540c2f60032bb4a34aaf0768b3107b94276b67b6f41fc289009c8924c1` |
| `BanditRLProof/OnlineSubgradientBasic.lean` | `4c17a466091b88d90451be897a2f01afa204b41933191244e0093e48396d1962` |
| `BanditRLProof/OnlineClosedProper.lean` | `9a5fcfb9e26a2a35d8e5bb7ef7b7a7dfd65a7f1c8daab03faebb51e41d54e7c6` |
| `../research-online-ogd/tmp/pdfs/orabona-v10.pdf` | `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17` |
