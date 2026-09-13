# Orabona v10 Chapter 2 projected OGD fixed-step chain

Task id: `ONLINE-OGD-CH2-FIXED`
Kind: `theorem`
Status: `accepted`
Harness: `hierarchical`

## Goal and boundary

Complete Algorithm 2.1 at constant step, Proposition 2.11, Lemma 2.12,
Theorem 2.13 fixed-step branch (negative terminal residual retained), and Eq. (2.1).
No claim for all Chapter 2, varying steps, general OMD, or Tsallis dual guarantees.

Source: Francesco Orabona, arXiv:1912.13213v10 (21 June 2026), printed pp.12-15.
Source card, digest, signature and initial dependency DAG:
`docs/contracts/online-ogd-v1/contract.md`.
Target file: `BanditRLProof/OnlineGradientDescent.lean`.
Public namespace: `BanditRL.OnlineGradientDescent`.

## Public interfaces

`project_spec`, `project_eq_of_variational`, `proposition_2_11`, `first_order`,
`lemma_2_12`, `iterate_mem`, `iterate_prefix`, `theorem_2_13_fixed`,
`equation_2_1_distance`, `equation_2_1`.
All declarations are publicly exported from BanditRLProof. No regret or
single-step certificate is assumed by the terminal theorem.

## Current evidence

- Draft header elaboration preceded ten original native statement fences.
- Actual proof chain passed focused Lean compilation (`attempt-04.log`).
- Public root build passed; concrete canary and all printed dependency audits passed
  (`canary-02.log`; one unused-simp lint subsequently removed).
- Native fence metadata repair preserved every original statement hash.
- Full root/Tests/exporter/Python gate passed (422 tests, 7 skipped), recorded in `full-gate.log` and its exit receipt.
- Same-registry Book source map and strict chapter boundary are in website/content.

Role outputs, failures, transitions, review, and acceptance receipts:
`runs/online-ogd-20260913/`. Semantic review and complete gate passed for local acceptance; see acceptance.json.
PR delivery is separate from merging or deployment. Existing SGB global frontier
is preserved; this task uses its own method-level lifecycle ledger.
