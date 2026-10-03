# Shared integration base, not canonical acceptance

Combine exact PR130 head f24f62c12835190fd5476f4f67e98aa5a056a34f with current canonical main6847b678a73db68dee5101d6f05c2453c1405afc. Preserve the previous Online Learning PR history and all newer Bandit library/site changes. This separate worktree allows registration conflict repair without modifying the active Huber build's checkout.

Three actual conflicts: root imports, Tests imports, Books summary. Resolution preserves the union of imports in main order, appending earlier Online imports; no imports are lost. Books are three-way merged, retaining Online source-mapped scope and main's separate adjacent-frontier classification. No theorem body is edited by conflict repair. The resolver and counts are retained in this run.

The global diff whitespace check reports trailing blank lines already present in incoming main theorem/doc files; those files remain byte-for-byte incoming content rather than being reformatted. Scoped conflict-resolution diff checks pass separately. This integration base is not yet compiled or accepted. Combined validation will run after replaying the Huber package on this base, and must include all existing Bandit and Online declarations. Canonical main, published site, old PR heads and shared .lake stores are unchanged. Worktree retained until safe retirement review.
