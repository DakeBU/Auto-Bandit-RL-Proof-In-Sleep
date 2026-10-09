from common import *
fixed()
assert not PUBLIC.exists()
paths=list(RUN.rglob('*'))+list(CONTRACT.rglob('*'))
paths += [ROOT/d/(TASK+'.md') for d in ['tasks','conversion-windows','proof-obligations','research-wiki/retrieval-index']]
for packet in [load(CONTRACT/'source-fingerprint-v1.json'),load(RUN/'retrieval-packet-v2.json')]:
    def collect(obj):
        if isinstance(obj,dict):
            for k,v in obj.items():
                if k in ['path','pdf','image_path','prior_text_path'] and isinstance(v,str) and Path(v).is_file(): paths.append(Path(v))
                else: collect(v)
        elif isinstance(obj,list):
            for v in obj: collect(v)
    collect(packet)
paths += [ROOT/p for p in ['AGENTS.md','CONTRIBUTING.md','docs/contributor-codex-contract.md','docs/theorem-publication-protocol.md','.agents/skills/bandit-semantic-roundtrip/SKILL.md','docs/hierarchical_harness.md','docs/lifecycle_and_proof_frontier_hardening.md','tools/abrl_lifecycle.py']]
write(RUN/'contract-review-inputs-v2.json',dict(stage='source CONTRACT review before BODY',rows=rows(paths),production_module_absent=True,chapter_complete=False,whole_Goal='active'))
write(RUN/'contract-review-request-v2.md','''# Source contract review request v2

Independently review the exact proposed Lemma4.13 contract against the pinned original PDF, printed40/PDF52, also inspect printed39/PDF51 for downstream context. Personally view both original PNGs. First reconstruct the source assumptions/conclusion yourself; then compare exact v2 header, scoped imports/context, seven-slot signature and the distinct neutral reconstruction. Root has read the full decoder report and both original images. Related reused automated role history is disclosed; do not claim human/external or absolute blindness/runtime attestation.

Verify all input RAW hashes before/after and report all actual reads. Inspect v1 failed typecheck and v2 repair (explicit Set.Ici disambiguation), complete successful v2 Prop/API and neutral Prop probes, actual narrow retrieval/API declarations. Type elaboration is not a proof. No production BODY exists. Retain nonnegativity even if unnecessary for this inequality; no global continuity, positive offset, positive increment or positive horizon may be silently added. Check zero horizon/increments, initial offset, current-inclusive right endpoint, real ambient extension and orientation. Do not approve singular inverse-sqrt-at-zero application. Theorem4.14 min/inf edge is a separate future correction, not a repaired source in this terminal.

Review exact conversion scope: after favorable review only NEW BanditRLProof/OnlineAdaptiveSummation.lean may implement this frozen header/context and necessary private helpers. No root/Test/readers/registry/coverage or old baseline edits. Own NEW role/attempt/lifecycle evidence may be appended. One lower interval-comparison/telescoping route. This is reusable prerequisite growth toward Chapter2 required adaptive-rate mathematics, not a new Chapter4 main task/algorithm/regret proof. Chapter2 partial/null, Chapter4 and future inventories unenumerated/null, eight forward containers and six future mathematics remain required/open; total Goal ACTIVE. Review exact old forward inventory and current DAG. Full candidate/integration gates remain future obligations.

Produce contract-source-review-v2.md and contract-source-review-v2.json ONLY inside this RUN. Include input SHA, all inspected rows, unchanged inputs, verdict accepted-with-explicit-delta or repair with exact issues, seven-slot comparison and permitted proof window. Do not write theorem BODY, mutate contracts or claim accepted mathematical proof.
''')
fixed()
print('Contract input index',sha(RUN/'contract-review-inputs-v2.json'),flush=True)
