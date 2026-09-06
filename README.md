# BanditRLlib — anonymous review snapshot

This frozen appendix accompanies **ABRL: A Target-Faithful Autoformalization
Harness and Lean 4 Library for Bandit and Reinforcement Learning Theory**.

The release contains the complete Lean library and tests from a verified
snapshot, the declaration dependency exporter, and a reproducible anonymous
reading website. The prebuilt website is in `docs/index.html`.

[Open the reading website](docs/index.html).

## Read and check

Download the anonymous archive and install [Lean through Elan](https://lean-lang.org/install/).
The toolchain and Mathlib dependency are pinned in the checked-in configuration.

```sh
lake exe cache get
lake build
lake build Tests
python3 website/scripts/build_site.py --lean-verified
python3 website/scripts/check_site.py
python3 -m http.server 8000 --directory docs
```

Open `http://localhost:8000/` for chapters, exact declarations, and the Lean graph.
The site is static: it is not an online compiler or submission service.
Compiled labels come from the unchanged, CI-verified Lean snapshot. The build
flag verifies file integrity, not Lean execution; the two Lake commands above
perform independent proof checking. Partial/planned results remain labelled.

## Scope and development policy

This is a **frozen review branch**, not a development branch. All subsequent
library development belongs on **main**. Do not merge this review branch into
main, and do not automatically mirror later main commits into this snapshot.
An explicit, separately checked release is required if reviewers need an update.

Author records, contributor cards, operational logs, original repository links,
and original Git history are excluded. Required third-party licensing is retained
in [NOTICE.md](NOTICE.md). Bibliographic references identify mathematical sources,
not project contributors. The website graph is a teaching/import/declaration map;
it must not be mistaken for the separately frozen proof-body analysis in the paper.

Only share the anonymization service link with reviewers. A branch URL on the
original GitHub host is **not anonymous**, even when its file contents are.

## License

[MIT](LICENSE), using the project's existing anonymous-artifact license.
