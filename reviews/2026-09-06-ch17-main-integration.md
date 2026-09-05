# Chapter 17 integration after Chapters 13--16

Base: `5558f0f8a129bb3e5607b3875d816974d7b33ae2` (PR #104 merged).
Chapter 16 explicitly released the Pages/live gate after run `33979529011`
and live acceptance; this branch may now proceed without cancelling that work.

The integration preserves upstream Chapter 13--16 source files and accepted
chapter metadata, while retaining Chapter 17's user-approved corrections:
Claim 17.6 uses `T_i<=n/2`; Theorem 17.4 has `0<delta<=1/32`, `c=1/160`,
`C=64`, and the strict actual-random-regret CDF complement. It is not a proof
of the unchanged printed statements.

Conflict resolution combines append-only manifest records, regenerates global
declaration/reference indexes, retains upstream Ch13--16 table rows and Ch17's
corrected rows, and preserves both Ch15/Ch16 and Ch17 website acceptance gates.
The overview count is computed from source-theorem statuses rather than frozen
at four terminals; the Mermaid diagram preserves Ch16 and exposes the corrected
Ch17 closure. No Lean source conflict occurred.

Four focused website gate tests pass, including all-chapter metadata acceptance
and preservation of the separate Ch15/16 gates. The generated-site structural
checker passes for 716 pages, 662 modules, 8877 declarations and 9710 source
links. This is structural evidence, not a replacement for integrated Lean CI.

The full local integration gate is running on the short-path snapshot with
log `E:/Temp/ch17-integrated-full-gate.log`; exact-head CI remains required
before merge. Prior local and deployed results are not a substitute for this
integration gate. The Ch16 source/root Lean files remain identical to main.
