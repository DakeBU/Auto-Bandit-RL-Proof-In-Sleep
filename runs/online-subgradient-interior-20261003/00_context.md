# Interior subgradient existence

Base PR #137 at 6571dcea0670463f12ad24edd067b7483a16ac98. Active whole-book Goal remains incomplete. Source Orabona v10 printed p.17/PDF29, unnumbered interior-subdifferentiability assertion. Source SHA256 cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17. Scratch contracts and successful producer/canary logs are retained in the preceding packet; public acceptance is separate.

Director: close the actual interior producer, not a consumer assuming supporting vectors. Architect: strengthen the canonical affine-minorant construction with contact equality; preserve the old minorant terminal and route it through the stronger helper. The finite-dimensional Riesz correspondence supplies the vector. Worker: path-only integration of the compiled scratch proofs and one wrapper refactor. No new closedness, boundedness, or differentiability assumptions.

DAG: supporting functional -> affine support with contact -> (old affine minorant, interior subgradient producer) -> interval-center public canary. Same actor performs director/architect/worker; independent blind/source actors still required. Reader and graph updates remain pending. No chapter/main/live acceptance.
