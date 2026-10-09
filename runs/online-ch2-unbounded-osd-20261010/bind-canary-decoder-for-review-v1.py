from common import *
fixed()
paths=[RUN/'canary-neutral-packet-v1.json',RUN/'canary-neutral-inputs-v1.json',RUN/'canary-blind-reconstruction-v1.md',RUN/'canary-blind-reconstruction-v1.json',CONTRACT/'canary-headers-draft-v2.json',RUN/'CanaryTypeProbeV2.lean',RUN/'canary-type-probe-v2.json',RUN/'canary-type-probe-inspected-v2.json',RUN/'canary-type-repair-v2.json',RUN/'CanaryTypeProbeV1.lean',CONTRACT/'canary-headers-draft-v1.json',RUN/'canary-type-probe-v1.json',RUN/'canary-type-probe-inspected-v1.json']
assert sha(RUN/'canary-blind-reconstruction-v1.md')=='990323a7a1ee7ffb8c99c882d1092d87b6cb86224f3157d9e8f63f78c5541d80'
assert sha(RUN/'canary-blind-reconstruction-v1.json')=='8563b49a394ce817a0d131c859a95a91be9a3ab3852f32793a5639108837a4f7'
write(RUN/'full-body-canary-review-supplement-v1.json',dict(kind='Distinct decoder exact additional RAW input bindings for same pending BODY/canary review',rows=[dict(path=r['path'],sha256=r['sha256'],before_raw_base64=base64.b64encode(Path(r['path']).read_bytes()).decode('ascii')) for r in rows(paths)],types_and_context_current='canary-headers-draft-v2.json',Test_bodies_lowered=False,scope='7 and9 complete top-level conjuncts. Horizon2 and64 witness sequences switch at1 and32 respectively, not a common stream prefix. Actual canonical OSD algorithm unchanged. All11 source terminal BODYs and exact canary CONTRACT review only.'))
fixed()
