# Contributor baseline strategy

Checker compares `BASE...HEAD`, never the index. Run only after clean committed merge.

Prospective staged trees plus draft V2 coverage: c445 baseline has7 protected paths and6 stale historical-main affected paths; f07 baseline has84 protected paths and5 stale historical-branch paths; common ancestor fea256b1 has89 protected paths and no uncovered/stale coverage. These are set calculations, not successful gate receipts.

Recommended cumulative integration command: bundled Python3.12 `-B -X utf8 tools/check_contributor_contract.py --base fea256b1c03b14b79c6c84a965e8ac2b5a738f64`, after actual clean commit. Label it common-ancestor aggregate gate. Separately bind exact first-parent7 changes and preserve main historical manifest byte-for-byte.

If the actual PR gate uses c445 or f07, this aggregate run does not replace it: current checker unions all changed manifests, so a new successor cannot subtract stale historical coverage. Do not mutate old manifests or manufacture source changes. A separately reviewed inherited-manifest/baseline policy repair is needed if actual PR-base passing is mandatory.

Draft V2 affected7 is correct for first-parent maintenance scope. Add baseline explanation in durable sidecar or verification prose, not inflated affected scope. No gate, Git mutation or active file edit performed.
