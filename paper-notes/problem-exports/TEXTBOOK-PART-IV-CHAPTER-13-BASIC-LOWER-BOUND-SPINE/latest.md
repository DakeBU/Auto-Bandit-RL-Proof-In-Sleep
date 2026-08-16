# Proof Export: Chapter 13 Lower-Bound Basic Ideas Spine

Task id: `TEXTBOOK-PART-IV-CHAPTER-13-BASIC-LOWER-BOUND-SPINE`

Status: locally gate-verified at `47ef4fe42679cd53e208aed540b6aa2bdb253aa8`.

This export covers the Chapter 13 semantic and deterministic slice. It does
not claim the Gaussian minimax lower bound in Theorem 13.1, whose proof the
source defers to Chapter 15.

## Lean Declarations

- `LowerBounds.worstCaseExpectedRegret`
- `LowerBounds.minimaxExpectedRegret`
- `LowerBounds.expectedRegret_le_worstCaseExpectedRegret`
- `LowerBounds.minimaxExpectedRegret_le_worstCaseExpectedRegret`
- `LowerBounds.le_minimaxExpectedRegret`
- `LowerBounds.exists_alternative_le_average`
- `LowerBounds.alternativeExpectedPullBudget_le`
- `LowerBounds.exists_leastExploredAlternative`
- `LowerBounds.baseEnvironmentRegret`
- `LowerBounds.changedEnvironmentRegretLowerBound`
- `LowerBounds.max_base_changed_regretLowerBound_ge_half_sub_error`
- `LowerBounds.max_base_changed_regretLowerBound_ge_half`

## Natural-Language Proof

Let `R(pi,nu)` take values in `ENNReal`. The worst-case value of a policy is
the supremum of `R(pi,nu)` over the explicit environment subtype, and the
minimax value is the infimum of these worst-case values over the explicit
policy subtype. The three order lemmas are direct complete-lattice rules:
membership supplies an index for the supremum or infimum, and a lower bound
valid for every admissible policy passes through the infimum.

For `m+1` arms, split the finite sum at arm zero. Nonnegativity of its expected
pull count and the exact total-pull identity imply that the sum over the `m`
alternative arms is at most the horizon. If every alternative exceeded the
average, its finite sum would exceed that budget; Mathlib's finite averaging
lemma therefore supplies an `i : Fin m` with the `Fin.succ` arm bounded by
`n/m`.

For the deterministic two-environment step, abbreviate

```text
B = Delta * (n - x),    C = Delta * y,
```

where `x` and `y` are the expected base-arm pull counts under the base and
changed laws. From `Delta >= 0` and `x-y <= error`, multiplication preserves
order, so `B+C >= Delta*(n-error)`. Both `B` and `C` are at most
`max B C`, hence their sum is at most twice that maximum. Dividing the combined
bound by two gives

```text
Delta * (n - error) / 2 <= max B C.
```

Setting `error = 0` yields the half-horizon corollary under `x <= y`. The Lean
theorem treats the transport comparison as a premise; it proves no likelihood
ratio, KL, absolute-continuity, policy-consistency, or Gaussian statement.

## Verification boundary

- Focused module, root-import canary, `lake build Tests`, axiom print, and
  `python3 tools/bandit.py check` passed.
- The printed axioms are only `propext`, `Classical.choice`, and `Quot.sound`.
- The lean-verified site build and site checker passed; desktop and 390-pixel
  mobile browser views were inspected without document-level overflow.
- Theorem 13.1 remains `planned` for Chapter 15; Chapters 14--15 must provide
  the same-policy history-law change-of-measure bridge.
- PR #9, main Actions run `31942624241`, Pages deployment job `95156292456`,
  and the live desktop/mobile Chapter 13 page passed; the scoped Chapter 13
  task is therefore `accepted` while the chapter page remains `partial`.
