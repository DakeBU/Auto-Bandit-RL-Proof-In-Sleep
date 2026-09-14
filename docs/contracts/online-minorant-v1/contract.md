# Global affine minorant integration v1

Two headers are byte-identical to online-minorant-interior-v1 and online-jensen-v2. The helper uses an interior point; the final target only nonempty effective domain, no bottom values, convex real epigraph and finite dimension. Parent measurable/Borel instances are retained although unused. The integration context adds pinned Intrinsic and LocalExtr APIs and imports accepted barycenter; no target hypothesis changed.

Original contracts predate proof attempts. The current integration context is reviewed separately after scratch compilation; it preserves typeclass quantification and public names. The initial source frontier was barycenter plus interior scratch, and the parent exact target was already stabilized. Director/architect planning and leaf01/02 are in runs/online-minorant-20260914. No separate independent reviewer claimed.

DAG: epigraph support -> negative vertical coefficient via interior/local Fermat -> interior affine minorant; relative interior of domain -> affine-span direction pullback -> interior helper -> algebraic linear extension and finite-dimensional continuity -> global affine minorant. Canonical mathlib closed/lsc variants are not drop-in substitutes. Next Jensen negative part and final endpoint remain required.

Conversion window: theorem bodies only; exact headers and section contexts frozen. Acceptance requires nontrivial lower-dimensional/nonclosed-domain canary, public axioms, root/Tests/full harness, proof graph, registry and site. No whole Jensen or chapter acceptance.
