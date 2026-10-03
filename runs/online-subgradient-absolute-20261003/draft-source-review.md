# Example 2.24 draft source contract review

Verdict: **accepted-with-explicit-delta for contract stabilization only**. No mathematical header repair is required. The sole representational delta is embedding the source real-valued scalar absolute function into EReal to reuse the global support definition. No proof, compilation of the target, source-example completion, public acceptance, Chapter 2/book completion or future normal-cone/maximum/OSD result is certified.

Actor: `/root/source_reviewer`, separate automated anti-anchored reviewer, requested GPT-6 Astra / medium; 2026-10-03. Not external-human review. The fresh separate decoder's own source-blind scope is retained.

## Original source and read inventory

I independently hashed the original cached Orabona arXiv:1912.13213v10 PDF and freshly extracted physical page 30, printed page 18. Its SHA256 is cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17, matching the pin. Example 2.24 gives exactly the absolute-value subdifferential: singleton plus one for positive x, the closed interval [-1,1] for x=0, and singleton minus one for negative x.

I read all eleven v1 contract files (context, contract, manifest, four headers and four native fences), the complete v2 neutral packet and reconstruction, actual SourceSubdifferential definition with scoped typeclass context in OnlineSubgradientBasic, api-probe01 output, the target syntax scaffold, and the initial rejected fence-capture log. I did not use the original incomplete-context blind reconstruction as authoritative evidence, and did not edit it. Hashes below bind whole containing files; only the definition and immediate context of the reused production module are freshly reviewed here.

## Seven semantic slots

| Slot | Mismatch search and result |
| --- | --- |
| 1. Objects/spaces | Actual leaves and terminal specialize to E=real line and f(y)=abs(y), with finite EReal embedding. The generic imported definition has normed additive group and real inner-product structure; its generality does not turn this target into a higher-dimensional norm theorem. |
| 2. Quantifiers | Terminal quantifies every real x. Set equality covers every candidate slope g, and membership quantifies every real test y, including points across zero. No local neighborhood, restricted sign domain or bounded feasible set replaces the global support relation. |
| 3. Assumptions | Positive leaf has only 0<x; negative only x<0; zero has no premise. Terminal has no sign exclusion or properness/convexity/differentiability/support-existence input. Those properties of absolute value need not be added as hypotheses. |
| 4. Conclusion | Exact full set equality in each case, not merely existence or a chosen subgradient. Both necessity and sufficiency are required. The zero leaf must produce and bound the whole interval, not just slope zero. |
| 5. Constants/normalization | Exact slopes +1 and -1; Icc(-1,1) includes both endpoints. Real inner product on the scalar line is multiplication (order of factors immaterial); finite coercion preserves sums and order, so the relation is abs(x)+g*(y-x)<=abs(y) without scaling. |
| 6. Probability/information | Deterministic scalar convex analysis. No probability, feedback, algorithm, regret or causality claim. |
| 7. Boundaries | Strict positive and negative leaves exclude zero. Terminal tests 0<x, then x=0; the remaining real-order branch is exactly x<0. Thus every query is covered and zero endpoints are inclusive. No x!=0 premise is added to the whole theorem. |

## Header, decoder and representation audit

The four native JSON statement fields agree with the four actual header statements. All four tool-measured raw header hashes match the manifest fingerprints. The neutral terminal name differs from the named source endpoint only as anonymization; its mathematical type is identical. The v2 packet explicitly supplies the missing generic definition context and correctly specializes the supporting relation to the scalar line. Its reconstruction accurately preserves all-x, all-g, all-y quantifiers, exact constants, inclusive endpoints, strict sign cases and the distinction between a full characterization and a selected slope.

Because abs(y) is always finite real, the EReal representation encounters neither positive nor negative infinity in this example's support inequality. Finite coercion and the real inner product therefore give exactly the ordinary scalar source relation. The unguarded-support convention for improper EReal functions discussed in earlier sum packets has no extra case here. No substantive source weakening or stronger hypothesis is present.

api-probe01 displays the actual named SourceSubdifferential, EReal coercion/order, absolute-value, scalar multiplication and set-membership interfaces. This is API-retrieval evidence, not evidence that any of these four target proofs compiles. No target proof body is supplied in the inspected scaffold: each := by slot contains only a comment. It is intentionally incomplete and must not be compiled or advertised as a successful declaration. Absence of literal sorry is not a proof. The earlier fence capture really failed because the parser found no top-level assignment; the syntax slots repair the capture format only. The failed log and original context-caveat history remain preserved.

## Stabilization and remaining work

The contract may stabilize with the explicit real-to-EReal representation noted above. All three sign leaves and the whole-line terminal remain required proof obligations. Later proof repair must not alter their hypotheses, switch Icc to an open interval, omit either direction, assume existence, or replace the zero set by a chosen point. Planned probes for nonzero queries, fractional slopes, interval endpoints and outside slopes are not yet acceptance evidence. Public shared-root integration, canaries, technical gates and later source/body/reader/binding reviews remain future stages. This receipt authorizes no claim about subsequent examples or the broader program.

## Independently measured raw SHA256

Current filesystem bytes, without line-ending normalization or JSON reserialization. Paths relative to E:/ABRL/worktrees/research-online-book.

| File | Raw SHA256 |
| --- | --- |
| `docs/contracts/online-subgradient-absolute-v1/abs_subgradient_negative-header.txt` | `f359b9dd5e7dd8e6009b5d0835565cbe368b6ccd1e625d234b25bd03e52b1108` |
| `docs/contracts/online-subgradient-absolute-v1/abs_subgradient_negative.json` | `0e808e2f48a678e87afb260fc91df4d530c469304ac61a8c7a7d6a37379ca524` |
| `docs/contracts/online-subgradient-absolute-v1/abs_subgradient_positive-header.txt` | `cfb2df66eda35e65a83318b5b59f570e56b9afa4f11d0dcdf372d6f9b1ad856d` |
| `docs/contracts/online-subgradient-absolute-v1/abs_subgradient_positive.json` | `8c4370b9c55e3c88a6358029f63b0916211df587ffe66fb72567eefbcaa3f8fb` |
| `docs/contracts/online-subgradient-absolute-v1/abs_subgradient_zero-header.txt` | `c5f9745262f576971cf7096bc268258885b391dd0bef85786e1c81dcc1d8b332` |
| `docs/contracts/online-subgradient-absolute-v1/abs_subgradient_zero.json` | `bc325ee4fd9ef8cd7e6e34194c8782133c8e32fc069492c59d33e34ea56b5ca0` |
| `docs/contracts/online-subgradient-absolute-v1/context.txt` | `ecb3d1316f53b564bd8cd52a1af4b38c83c2b9f31d043595b0f1d87a851f8ba9` |
| `docs/contracts/online-subgradient-absolute-v1/contract-manifest.json` | `433327d2dc9af0b8463812ff249b50e6bcdca7793f6b3701463e9a4925704f27` |
| `docs/contracts/online-subgradient-absolute-v1/contract.md` | `6365f9c7eb76281e9b9eced733c802b60134a2670fc5e93c2c8fe6c87a1eb45d` |
| `docs/contracts/online-subgradient-absolute-v1/example_2_24-header.txt` | `b0322da57a4477f93638dd5845349c715b519a441bbafe15d28f785d7f66d118` |
| `docs/contracts/online-subgradient-absolute-v1/example_2_24.json` | `302d299be4bcc52eb3fc7c9fd8defb5d7e759281e66a329ba0220771a01deb30` |
| `runs/online-subgradient-absolute-20261003/blind-packet-v2.txt` | `9d65343f308bb4bae9a569afb88c0f94240f8a35b523d71ae74afbf0fb1a1156` |
| `runs/online-subgradient-absolute-20261003/blind-reconstruction-v2.md` | `9845fd5ba702a59424dc40b21f028b9bba99e206cf8aabccf1d8b614312df9ca` |
| `BanditRLProof/OnlineSubgradientBasic.lean` | `4c17a466091b88d90451be897a2f01afa204b41933191244e0093e48396d1962` |
| `runs/online-subgradient-absolute-20261003/api-probe01.log` | `4b595fc836273af28ccfce38c3b8c31aed88bc355603a4939960893e8fc123fe` |
| `tmp/online-subgradient-absolute-target.lean` | `fd825010006b6b2b0fe042516bcf29ca19924917f58c26b59135527eb018e1b2` |
| `runs/online-subgradient-absolute-20261003/fence-capture01-rejected.log` | `1ecccd282dd563570107765893223d262fe4ee69c1f9aebe23f57ddd3066bb5f` |
| `../research-online-ogd/tmp/pdfs/orabona-v10.pdf` | `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17` |
