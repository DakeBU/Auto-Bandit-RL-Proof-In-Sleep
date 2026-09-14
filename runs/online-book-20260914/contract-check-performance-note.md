# Contract check execution note

Initial checker process57878 performs the native complete BanditRLProof/Tests placeholder scan for every header. Inspection of abrl_lifecycle.safe_verify shows this repeats the same whole-source check. It is still running and is not restarted.

The checker source is updated for future runs to perform one full-root placeholder scan, then verify every remaining immutable header against the same unchanged source snapshot. No placeholder scope is removed: all library and Tests Lean files are scanned once, and each native statement/assumption check still runs. This avoids multiplying the full-tree scan by the number of fences. The existing process result remains valid for its stricter repeated scan.
