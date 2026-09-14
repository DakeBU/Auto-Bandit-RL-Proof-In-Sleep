import json, hashlib
from pathlib import Path
path=Path("tmp/online-book-graph-final.json")
raw=path.read_bytes(); graph=json.loads(raw)
ns="BanditRL.OnlineLearning."
nodes=[n for n in graph["nodes"] if n["name"].startswith(ns)]
names={n["name"] for n in nodes}
assert ns+"empiricalMean_unique" in names, "stale export predates uniqueness repair"
edges=[e for e in graph["edges"] if e["source"] in names]
assert not any("sorryAx" in str(e) for e in edges)
required=[("theorem_1_3","lemma_1_2"),("theorem_1_3","meanPredict_stability"),
          ("meanPredict_noRegret","theorem_1_3"),("empiricalMean_unique","empiricalMean_decomposition"),
          ("iid_meanPredict_excess","independent_prediction_square"),
          ("iid_meanPredict_excess","meanPredict_independent"),
          ("history_policy_loss_ge_variance","history_policy_independent")]
checks=[]
for source,target in required:
    assert any(e["source"]==ns+source and e["target"]==ns+target and
               (e["kind"]=="value" or e.get("also_in_value")) for e in edges), (source,target)
    checks.append({"source":ns+source,"target":ns+target,"proof_value_occurrence":True})
boundary={e["target"] for e in edges}-names
out={"schema_version":1,"scope":"Chapter1 direct constant dependencies from compiled root; not execution trace",
     "extraction":graph["extraction"],"lean_version":graph["lean_version"],
     "full_export_sha256":hashlib.sha256(raw).hexdigest(),"full_export_counts":graph["counts"],
     "required_chain_checks":checks,
     "source_lf_hashes":{str(p).replace(chr(92),"/"):hashlib.sha256(p.read_text(encoding="utf-8-sig").encode()).hexdigest()
                         for p in Path("BanditRLProof").glob("OnlineLearning*.lean")},
     "nodes":nodes+[n for n in graph["nodes"] if n["name"] in boundary],"edges":edges}
Path("runs/online-book-20260914/compiled-dependencies.json").write_text(json.dumps(out,indent=2)+"\n")
print({"scope_nodes":len(nodes),"boundary_nodes":len(boundary),"edges":len(edges),"chain_checks":len(checks)})
