from common_v1 import *

names = ['bandit_paper_cards','bandit_scenario_cards','bandit_textbook_cards',
         'proof_weapon_cards','local_leaf_cards','local_lean_declarations']
files = [RUN/'baseline'/('retrieval-'+name+'.raw') for name in names]
files += [ROOT/'research-wiki/retrieval-index'/(name+'.json') for name in names]
files += [RUN/'draft-retrieval-scope-audit-v1.json',RUN/'source-contract-review-v1.md',
          RUN/'source-contract-receipt-v1.json',ROOT/'docs/contracts/online-completed-causal-v1/targets-v1.json']
rows = raw_index(files)
write(RUN/'retrieval-supplement-inputs-v1.json',dict(rows=rows,fixed_input_count=len(rows),
      purpose='Independent historical six scanner RAW before/current comparison, supplementing disclosed original review limitation',
      proof_progress=False,chapter_complete=False,goal_complete=False))
write(RUN/'retrieval-supplement-packet-v1.md',
      'Original CONTRACT report accurately states that historical scanner comparison was not independently reproduced because six scanner originals are NOT in draft-baseline rows. They are actually the six exact designated baseline/retrieval-NAME.raw paths in this supplementary16RAW index, recorded by the executed repair-draft-context-v2.py BEFORE native reference-index. Independently hash all16before/after and parse each original/current JSON, remove only generated timestamp, require the five non-Lean indexes identical. For local_lean_declarations require all old full records/order preserved, exactly four new names/records matching completed-causal targets and no current-kernel entries. Compare actual result against bound draft-retrieval-scope-audit-v1.json. Do not overwrite the original104 review/report; its limitation remains historically accurate.\n\n'
      'Write ONLY retrieval-supplement-review-v1.md / retrieval-supplement-receipt-v1.json with actual16RAWchecks/reportSHA/verdict/blockers and precise independent comparison findings. This closes only a retrieval provenance audit if successful, no compiled/source/chapter/Goal or package acceptance. Do not rerun CLI scanners/native/Git or read/write production during ongoing K1 proof build. Reused distinct reviewer, requested Astra/medium; no human/external/absolute blind/runtime attestation.\n')
print('Supplement exact RAW inputs:',len(rows),'historical audit only.',flush=True)
