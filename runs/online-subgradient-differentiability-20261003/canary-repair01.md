# Rejected scratch canary attempt

interior-canary01 failed: unrestricted simp pushed the real coercion through the square before toReal/bottom/top rules, and an assumed embedding helper name does not exist. Error recovery printed sorryAx; these outputs are rejected evidence. Keep actual coe-boundary APIs with simp only, and reuse the real-domain convexity equivalence. No frozen theorem header or main proof changed.
