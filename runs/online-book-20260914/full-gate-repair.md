# Full gate repair audit

full-gate-01: root and Tests build pass; 423 Python tests ran, errors9, skipped7. Eight errors arise during temporary OpenSSH Ed25519 key generation/cleanup (public-key Bad file descriptor and private-file Access denied). One error is capped-output child termination followed by wait timeout. These are failures, not skipped tests or proof failures.

A narrowly scoped rerun of the positive signature test with TEMP/TMP under this authorized worktree reproduced private-key Access denied. No ACL change, deletion workaround, signature mock, test removal or replacement crypto implementation was attempted. Preserve these temporary files; do not treat them as ordinary disposable cache. The environment permission profile changed before this work to restricted managed execution. Attribution to environment is a diagnosis supported by these symptoms, not an independently proven cause of every failure.

Next: retain local failures and obtain full CI evidence when the candidate package is ready for a reviewable PR. Continue remaining mathematical/semantic gates; do not mark chapter accepted now. No harness code was modified to bypass the failures.

Uniqueness audit repair: original scratch used a missing order lemma. Public empiricalMean_unique was frozen and proved using positivity and the exact squared-loss decomposition; focused check passed. Root and Tests must rebuild with this new theorem and its public canary.
