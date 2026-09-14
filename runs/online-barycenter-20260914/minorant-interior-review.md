# Next dependency candidate, not accepted

The exact interior-domain helper header and context were reviewed/frozen before the proof. The first attempt failed only because `ext p` recursively split a product, leaving p:E rather than a pair. Leaf02 repairs this with explicit ContinuousLinearMap.ext; it compiles with exit0 and no diagnostic. Native header verification passes. The retained candidate is not imported in the public root and has not passed public canary/axiom/full gates.

The proof separates the real epigraph at (x,f(x)). The vertical coefficient is nonpositive by the upward ray. If zero, the horizontal functional has a local maximum at the interior point, so its derivative vanishes; the whole separator would vanish. The strictly negative coefficient gives a finite affine minorant by division with the correct reversed order. Infinite function values are handled directly. Only the helper assumes an interior domain point. The general frozen parent target still requires a relative-interior/affine-span restriction and extension, then negative-part finiteness and source Jensen. No silent weakening of that parent.

Same-model sequential roles, not independent external review. This draft was developed without changing the public sources during barycenter acceptance.
