# BanditRLlib semantic round trip

Use this skill for every source-facing theorem, bound, algorithm guarantee, or theorem-level correction.

## Why

Lean checks the proposition that was encoded. It does not check that the proposition faithfully represents the cited mathematics.

## Roles

Three distinct actors are required:

1. **formalizer** — writes/adapts the Lean statement/proof;
2. **blind decoder** — receives Lean statement/context but no source identity or prior verdict;
3. **source reviewer** — receives source + Lean + blind reconstruction, but is instructed to search for mismatch rather than confirm the formalizer.

The formalizer cannot fill the two independent roles.

## Seven semantic slots

Compare:

1. mathematical objects and spaces;
2. quantifiers and order of quantification;
3. assumptions/regularity;
4. conclusion/metric;
5. constants, normalization, asymptotics;
6. probability, feedback, filtration/stopping semantics;
7. stated boundary / excluded regimes.

## Workflow

1. Freeze source version and anchor.
2. Freeze the actual Lean declaration text and required scoped context.
3. Create a source-blind packet containing only the Lean statement, imports/scoped parameters needed to understand it, and neutral notation.
4. Have the decoder reconstruct the theorem in natural language and LaTeX, including all assumptions.
5. Create the anti-anchored review packet with source + reconstruction + Lean.
6. Reviewer returns `accepted | rejected | accepted-with-explicit-delta` plus slot-by-slot differences.
7. If a repair is proposed, keep source, actual theorem, mismatch, and repair proposal separate. Obtain a separate repair review.
8. Record the result in the contribution manifest.

## Accepted states

- `not-required` only for genuinely non-source-facing infrastructure;
- `planned`;
- `blind-reconstructed`;
- `source-reviewed`;
- `accepted`;
- `rejected`.

A source-facing contribution cannot be integrated as faithful with `planned`, `blind-reconstructed`, or `rejected`.

## Output

The contribution manifest records:

```json
{
  "semantic_roundtrip": {
    "required": true,
    "status": "accepted",
    "formalizer": "...",
    "blind_decoder": "...",
    "source_reviewer": "...",
    "verdict": "accepted",
    "remaining_semantic_delta": "none"
  }
}
```
