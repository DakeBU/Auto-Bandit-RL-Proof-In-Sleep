# Global affine minorant dependency

Previous goal turn was progress: exact barycenter accepted locally and delivered PR126. Current branch codex/research-online-minorant, stacked on PR126 exact38316cf121cef8b3fb05569e5b064ca374200095, canonical main unchanged. Total Goal active, no budget. Same-model GPT-6 Astra/medium sequential roles.

Director: close the existing online-jensen-v2 convex_affine_minorant exact header without adding interior/closedness/continuity assumptions. Architect: restrict to affine span direction with a relative interior point, apply the frozen compiled interior helper, extend the real linear functional to the ambient finite-dimensional space. Body edits only; parent and helper headers remain frozen. APIs read: Set.Nonempty.intrinsicInterior, AffineIsometryEquiv.vaddConst, Homeomorph.preimage_interior, LinearMap.exists_extend. Closed/lsc minorant results do not match the source.

Full public integration, canary, axiom, graph, harness and site gates remain required. No full Jensen or chapter acceptance from this dependency alone.
