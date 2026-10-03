# Interior subgradient existence from affine contact

Task id: `ONLINE-BOOK-CH2-SUBGRADIENT-INTERIOR`
Kind: `theorem`
Status: `candidate`
Harness: `hierarchical`

## Goal

Orabona v10 printed p.17/PDF29: every proper convex extended-real function is subdifferentiable on the interior of its effective domain. Finite-dimensional real inner-product spaces; global support inequality for every y. No closedness, boundedness, or differentiability assumption. No probabilistic/information assumptions apply.

## Lean Target

`BanditRL.OnlineConvex.subgradient_exists_of_domain_interior` in `BanditRLProof/OnlineSubgradientInterior.lean`. Shared intermediate `affine_support_of_domain_interior` in `OnlineConvexMinorant.lean` retains contact at x; unchanged old minorant terminal consumes the same proof. Native public fences in docs/contracts/online-subgradient-interior-public-v1 match original scratch headers.

## Proof route and retrieval

The actual existing supporting_functional_at_closure and affine-minorant body supply a contact functional, and Mathlib InnerProductSpace.toDual_symm_apply supplies its representing vector. No external dependency or toolchain change. General contact helper is reusable; source predicate adapter is project-local. Public interval-center canary instantiates actual extended-valued indicator on a nontrivial interval.

## Acceptance boundary

Public focused compilation, distinct blind/source review, reader and shared graph publication, frozen headers, axiom audit, combined root/Tests/harness and site/contribution gates all required. Chapter2 and the whole book remain incomplete. Global SGB frontier is not repointed. See runs/online-subgradient-interior-20261003/00_context.md.
