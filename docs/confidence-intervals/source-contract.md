# Absolute-error certificates and finite interval comparisons

Source: author-derived reusable mathematical interface, version 1 (2026-10-09).
This is elementary certificate transport; no new statistical bound is claimed.

For real target μ, intermediate value ν and estimate x, certificates
|ν−μ|≤b and |x−ν|≤s imply |x−μ|≤b+s by the triangle inequality.
The numbers b,s need no separate nonnegativity premise: the two certificates
already force it.

For a finite active set A of indices in Fin K, define surviving indices as
those i∈A whose upper endpoint x_i+r_i is at least every active lower endpoint
x_j−r_j. Endpoints that merely touch survive. An active maximizer of μ survives
whenever all active intervals contain their targets: x_j−r_j≤μ_j≤μ_*≤x_*+r_*.
No unique maximizer is required. If all active radii are at most r and
μ_*−μ_i>4r, then x_*−r_*≥μ_*−2r>μ_i+2r≥x_i+r_i, so i is removed.
If i is initially inactive it is already absent from the filter.

All four declarations are literal deterministic statements. K may be zero;
the two comparison theorems require a displayed active witness star, so their
premises then cannot hold. There is no random law, independence, measurability,
concentration producer, stopping claim or executable finite-bit comparison.

Actual Lean parents are Mathlib abs_add_le, abs_le, Finset membership/filter,
ring and linear arithmetic. The interval filter is a literal finite predicate;
it introduces no choice or default target. Its two real consumers are
optimal_survives and large_gap_removed. No existing source theorem is repaired.
The module belongs to reusable confidence infrastructure. Teaching-route,
results, roadmap and conceptual hypergraph remain unchanged with this scope:
no downstream algorithm or rate is completed. Module imports are not theorem
implications.
