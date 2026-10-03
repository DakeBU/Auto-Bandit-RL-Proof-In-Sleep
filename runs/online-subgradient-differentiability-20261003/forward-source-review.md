# Forward and gradient scratch candidate: independent source review

Verdict: **accepted-with-explicit-delta for the forward implication and generic local-representative gradient identity only**. No semantic repair is required for these inspected candidate endpoints. This is not acceptance of the reverse implication or full Theorem 2.22, and not certification of compilation or public integration.

Actor: `/root/source_reviewer`, a separate automated reviewer requested GPT-6 Astra / medium, dated 2026-10-03. This is not external-human review. I inspected the actual scratch proof bodies and their imported first-order consumer rather than relying on prior contract approval as proof evidence.

## Source and raw read inventory

All paths below are relative to `E:/ABRL/worktrees/research-online-book`. All listed candidate/contract/reconstruction files were read completely. Hashes are raw SHA256.

| File | SHA256 |
| --- | --- |
| `runs/online-subgradient-differentiability-20261003/gradient-candidate.lean.txt` | `27aaa642ac5bc5e7750a34076b2296a88d35da4b688caa8443a1a8223e0c7c44` |
| `runs/online-subgradient-differentiability-20261003/forward-candidate.lean.txt` | `448f9f8a14a78a425a48aa645c02cb328524ccbd9a2c93472c3fefe89fd31deb` |
| `runs/online-subgradient-differentiability-20261003/forward-canary.lean.txt` | `00ebaf34941d7b52e906c37c6a5665c0ab28892d17791bc7e1722f0062de9a04` |
| `docs/contracts/online-affine-finite-neighborhood-v1/contract.md` | `68afcd99f0e90590768cfd8fe7c0069b5240415f53bc50d620501ce441fe8c57` |
| `docs/contracts/online-affine-finite-neighborhood-v1/header.txt` | `812521342d20dcf8a9ccbc41972bd9ea838db884e6be14096b10a1a17d63fa13` |
| `docs/contracts/online-affine-finite-neighborhood-v1/context.txt` | `8aeed8a4446c3da769b93ec5574c5eeec58731eaf590a0b6db02c9ae426e70d8` |
| `BanditRLProof/OnlineConvexFirstOrder.lean` | `9921bf1ed9391ddf01221be77f0321cc72a3caa4c1c97b058da3e145d8b2c60e` |
| `docs/contracts/online-subgradient-differentiability-v2/full-header.txt` | `7029e22ec2d7e84879a3c97109e5d17709372628fa516b309c2d5391ef5e94b9` |
| `docs/contracts/online-subgradient-differentiability-v2/gradient-header.txt` | `fd8f6b3d690b24692f0ab8462f8ab9a842b9381c96717da81c217ecf9254381e` |
| `docs/contracts/online-subgradient-differentiability-v2/context.txt` | `0638affef80952cde5777ece5cdcf2fa8ec46efd2c3ada2c670de2b0df8f5348` |
| `runs/online-subgradient-differentiability-20261003/blind-reconstruction-v2.md` | `89e90ba9abad3c07c3c7150f50fff62cef83b97a56ed4c22dc408285ca3d56a9` |

Source `E:/ABRL/worktrees/research-online-ogd/tmp/pdfs/orabona-v10.pdf` was freshly rehashed: `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`, matching the pinned version. Physical page 29 was freshly extracted directly from that PDF. Theorem 2.22, printed page 17, asserts differentiability iff singleton subdifferential for convex extended-real f finite at x and identifies the element with the gradient. Only its differentiability-to-singleton direction and gradient identification are candidates here.

## Seven semantic slots

| Slot | Finding |
| --- | --- |
| 1. Objects/spaces | Source Euclidean geometry is represented by finite-dimensional real inner-product space. The geometric core is formulated more generally on a finite-dimensional real normed space and returns a continuous linear functional. f remains extended-real-valued; the chosen real h agrees with it only locally. |
| 2. Quantifiers | The gradient endpoint works for every admissible local representative h. Its conclusion is equality of the entire global support set to the singleton gradient, so the same gradient supports f for every ambient y and every supporting vector equals it. The forward endpoint unpacks the existential differentiability witness and uses this exact identity. |
| 3. Assumptions | Source endpoints retain convexity and finite f(x), plus differentiability expressed by the neighborhood representative. They do not require global properness, interior membership, closedness, lower semicontinuity, boundedness, or global convexity/real-valuedness of h as inputs. Finite-dimensionality supplies completeness for the imported Hilbert-space consumer; it is not an additional source restriction. |
| 4. Conclusion | The actual gradient vector is both a global support and unique. This is stronger than a uniqueness-only implication and does not rely on a support-existence premise. It gives the source forward direction, not the reverse or full iff. |
| 5. Constants/normalization | Contact and supporting inequalities retain exact equality and coefficient one. Epigraph normalization uses c<0 and flips division inequalities correctly. The real representative's gradient is identified with the derivative of the finite part by local equality, not by a separate arbitrary choice. |
| 6. Probability/feedback | Entirely deterministic convex analysis, without probability, filtration, causal trajectories or stopping claims. |
| 7. Boundaries | Ambient neighborhoods include x and imply genuine local finiteness; no toReal-only boundary shortcut occurs. Positive infinity outside the neighborhood is allowed and handled by the global inequality. Negative infinity anywhere is ruled out by a proof. Zero-dimensional geometry remains allowed. Reverse singleton-to-differentiability and public integration remain absent. |

## Genuine producer-to-consumer chain

The new `affine_support_of_finite_neighborhood` assumes actual finite values on a neighborhood, not a pre-proved global nowhere-bottom condition. It constructs a nonzero supporting functional at the actual finite epigraph point `(x,f(x))`. The point is not interior to the epigraph, since a finite vertical coordinate cannot be a local minimum of the identity height function. No closed-epigraph premise is inserted.

Writing the functional as A(y)+ct, upward closure gives c<=0. If c=0, the actual finite neighborhood gives a local maximum of the linear functional A at x, forcing A=0 and contradicting nonzero support. With c<0, a hypothetical bottom-valued point y has every real height in its epigraph fiber. The proof chooses a finite height below the supporting threshold, giving a direct contradiction. Thus nowhere-bottom is derived globally, including points far outside the finite neighborhood. Normalization then proves both exact contact and a lower bound against every ambient y; positive-infinite f(y) is discharged separately.

In the gradient endpoint, the real representative directly produces the finite-neighborhood premise. The new core's global affine minorant yields nowhere-bottom. The core also proves contact, although this particular consumer does not use its `htouch` field: it uses the minorant to recover nowhere-bottom and then the already shared `theorem_2_7` to produce the actual gradient support. This unused stronger component is not a false support assumption or a fake consumer; the global minorant has a real downstream role.

`sourceDifferentiableAt_regular` derives ambient interior and differentiability of the finite part by eventual equality. These are outputs supplied to the older first-order API, not newly added source endpoint inputs. I inspected that imported `theorem_2_7`: it proves support on the effective domain from convexity and the derivative inequality, and handles the remaining y by positive infinity. Consequently the candidate really obtains global support, rather than restricting the conclusion to the local representative's neighborhood.

Uniqueness is separately derived: any global support g makes the finite part minus its linear functional have a local minimum at x. Differentiation gives equality of the represented continuous linear functionals, and dual injectivity gives equality of vectors. Local agreement identifies the finite-part gradient with `gradient h x`, independent of arbitrary values of h away from x. Combining existence and uniqueness yields the exact singleton identity. The finite-x parameter `hx` is redundant under local agreement, but preserving it matches the source contract and introduces no strengthening.

## Canary and reconstruction assessment

The interval canary uses the actual zero/top indicator of [0,2] at 1, constructs neighborhood equality to the zero real function, and derives the singleton {0} through the gradient endpoint. It therefore exercises genuine positive-infinite exterior values. The quadratic canary obtains the generic singleton identity and combines it with the existing support at 1 to identify the nonzero value 2. Both invoke actual theorem producers; neither assumes the singleton conclusion.

The version 2 blind reconstruction matches the candidate endpoint's quantifiers, global support, generic local representative and absence of properness/interior premises. That reconstruction described statement signatures, not these proof bodies; the body checks above are this actor's independent review and must not be attributed to the decoder.

These two canaries are focused examples, not proof of every boundary regime or of the reverse implication. I did not run the compiler or use unseen test logs as evidence.

## Verdict boundary and integration obligations

Semantic verdict: **accepted-with-explicit-delta** for `theorem_2_22_gradient`, `theorem_2_22_forward`, and their inspected scratch producer chain. Deltas are the already explicit coordinate-free finite-dimensional presentation and neighborhood-real-representative encoding of extended-real differentiability; no new source hypothesis is added. Required semantic repairs: **none**.

The finite-neighborhood affine-contact helper is a derived implementation lemma, not a separately printed source theorem. Its eventual shared-core integration must preserve old public consumer headers and avoid duplicated public geometric proofs, as its contract specifies. The repeated self-contained scratch snapshots do not establish that integration has happened. The full reverse implication remains unproved in this packet; full Theorem 2.22, public acceptance, deployment and Chapter 2 completion remain outstanding. This receipt is separate automated semantic review only, with no external-human-review claim.
