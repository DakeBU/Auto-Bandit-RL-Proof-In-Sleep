"""Python 3.8; read-only checks, one create-only result. Prepared, never auto-applies."""
import argparse
import hashlib
import json
import re
import subprocess
import zipfile
from pathlib import Path
from html.parser import HTMLParser
from html import unescape

NAMES = ["BanditRL.OnlineBregman.quadratic_geometry", "BanditRL.OnlinePrescientBregman.euclidean_variable_regret", "BanditRL.OnlinePrescientBregman.euclidean_fixed_regret"]
TEST_NAMES = ["variable_quadratic_actual_run", "fixed_quadratic_actual_run"]
GOVERNANCE = ["docs/proof-digestion-protocol.md", "docs/evidence-routed-memory-protocol.md", "docs/openai-math-assimilation-protocol.md", "research-wiki/openai-math-2026-intake.json", "runs/process_memory.json"]
CORE_SHA = "9b755a12d540c1039b068e4b97af90ac483a58fd1a8b40af9c806264f95d42b8"
TEST_SHA = "dbc2a2f7660e70517a6f50826944976aa9cbbba17e37f88b8bac9fbef97e0122"

def require(ok, message):
    if not ok:
        raise ValueError(message)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def load(path):
    return json.loads(path.read_bytes())

def norm(s):
    return re.sub(r"\s+", " ", s).strip()

def pointer(value, path):
    require(path == "" or path.startswith("/"), "invalid JSON pointer")
    for part in path.split("/")[1:]:
        part = part.replace("~1", "/").replace("~0", "~")
        value = value[int(part)] if isinstance(value, list) else value[part]
    return value

class Folds(HTMLParser):
    def __init__(self):
        HTMLParser.__init__(self)
        self.blocks = {}
        self.current = None
        self.depth = 0
        self.pre = False
    def handle_starttag(self, tag, attrs):
        a = dict(attrs)
        if tag == "details":
            if self.current is not None:
                self.depth += 1
            elif "declaration" in a.get("class", "").split():
                self.current = {"header": [], "links": [], "open": "open" in a}
                self.blocks[a["id"]] = self.current
                self.depth = 1
        if self.current is not None:
            if tag == "pre" and "lean-code" in a.get("class", "").split():
                self.pre = True
            if tag == "a" and "href" in a:
                self.current["links"].append(a["href"])
    def handle_endtag(self, tag):
        if self.current is not None:
            if tag == "pre":
                self.pre = False
            if tag == "details":
                self.depth -= 1
                if self.depth == 0:
                    self.current = None
    def handle_data(self, text):
        if self.current is not None and self.pre:
            self.current["header"].append(text)

def main(a):
    root = a.root.resolve()
    spec = load(a.spec)
    require(digest(a.spec.read_bytes()) == a.spec_sha256, "spec hash")
    require(spec["ready_for_execution"] is True, "reviewed complete spec required")
    evidence = {}
    for key, item in spec["bindings"].items():
        path = root / item["path"]
        require(digest(path.read_bytes()) == item["sha256"], "binding drift: " + key)
        evidence[key] = path
    required = ["core", "test", "production_freeze", "canary_freeze", "core_review", "canary_review", "topology", "topology_review", "values", "integration_review", "schema3_manifest", "normalization_receipt"]
    require(all(k in evidence for k in required), "missing required evidence binding")
    require(digest(evidence["core"].read_bytes()) == CORE_SHA, "core hash")
    require(digest(evidence["test"].read_bytes()) == TEST_SHA, "Test hash")
    core = evidence["core"].read_text(encoding="utf-8")
    test = evidence["test"].read_text(encoding="utf-8")
    require(re.findall(r"^theorem\s+(\w+)", core, re.M) == [n.rsplit(".", 1)[1] for n in NAMES], "exact 3 core theorems")
    require(re.findall(r"^theorem\s+(\w+)", test, re.M) == TEST_NAMES, "exact 2 Test theorems")
    require(not re.search(r"^(?:noncomputable\s+)?(?:def|abbrev|lemma)\s", test, re.M), "unexpected named Test helper")
    require(load(evidence["core_review"])["source_sha256"] == CORE_SHA, "core/review join")
    require(load(evidence["core_review"])["blocking_repairs"] == [], "core review blockers")
    require(load(evidence["canary_review"])["blocking_repairs"] == [], "canary review blockers")
    require(load(evidence["core_review"])["verdict"] == "accepted-candidate-core-only", "core BODY verdict")
    require(load(evidence["canary_review"])["verdict"] == "accepted-candidate-canaries-only", "canary BODY verdict")
    require(load(evidence["canary_review"])["production_sha256"] == CORE_SHA, "canary/core join")
    require(load(evidence["canary_review"])["Test_sha256"] == TEST_SHA, "canary/Test join")
    require(spec["json_assertions"], "exact schema3/review assertions required")
    require({x["meaning"] for x in spec["json_assertions"]} >= {"schema3", "freeze bindings", "source versus VALUE nodes", "edge semantics", "single route source gap"}, "missing required contract assertion meanings")
    for assertion in spec["json_assertions"]:
        require(pointer(load(root / assertion["path"]), assertion["pointer"]) == assertion["equals"], "JSON assertion: " + assertion["path"] + assertion["pointer"])
    gate = load(a.gate)
    require(digest(a.gate.read_bytes()) == a.gate_sha256, "gate receipt hash")
    require(gate["actual_exit"] == 0 and gate["capture_integrity_ok"] is True, "actual gate/integrity")
    require("tools/bandit.py" in gate["argv"] and "check" in gate["argv"], "combined gate argv")
    for key in ["pre_git", "post_git"]:
        require(gate[key]["HEAD"] == a.head and gate[key]["status_porcelain_v1_z_hex"] == "", "gate exact clean HEAD")
    require(subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=str(root)).decode().strip() == a.head, "current HEAD drift")
    require(subprocess.check_output(["git", "status", "--porcelain=v1", "--untracked-files=all"], cwd=str(root)) == b"", "current tree not clean")
    artifacts = {}
    for name in ["pre-source-inputs.json", "post-source-inputs.json", "pre-selected-ZIP-inputs.json", "pre-selected-source-raw.zip", "stdout.raw", "stderr.raw"]:
        path = a.gate.parent / name
        require(digest(path.read_bytes()) == gate[name + "_sha256"], "gate artifact hash: " + name)
        artifacts[name] = path
    pre = load(artifacts["pre-source-inputs.json"])
    post = load(artifacts["post-source-inputs.json"])
    require(pre == post, "source RAW inventory drift")
    raw = {x["path"]: x for x in post}
    require(len(raw) == len(post), "duplicate RAW paths")
    for path, row in raw.items():
        require(digest((root / path).read_bytes()) == row["raw_sha256"], "current RAW drift: " + path)
    selected = load(artifacts["pre-selected-ZIP-inputs.json"])
    selected_map = {x["path"]: x for x in selected}
    require(len(selected_map) == len(selected), "duplicate ZIP manifest paths")
    with zipfile.ZipFile(str(artifacts["pre-selected-source-raw.zip"])) as z:
        require(len(z.namelist()) == len(set(z.namelist())), "duplicate archive entries")
        require(set(z.namelist()) == set(selected_map), "ZIP entry-set mismatch")
        for path, row in selected_map.items():
            require(digest(z.read(path)) == row["raw_sha256"], "ZIP byte mismatch: " + path)
            require(row["raw_sha256"] == raw[path]["raw_sha256"], "ZIP/RAW mismatch: " + path)
        for path in GOVERNANCE:
            require(path in raw and path in selected_map, "missing governance RAW/ZIP: " + path)
            require(z.read(path) == (root / path).read_bytes(), "governance byte mismatch: " + path)
    require(digest(a.old_registry.read_bytes()) == a.old_registry_sha256, "baseline registry pin")
    oldreg = load(a.old_registry)
    newreg = load(a.site / "books/registry.json")
    oldnodes = {n["id"]: n for n in oldreg["nodes"]}
    newnodes = {n["id"]: n for n in newreg["nodes"]}
    require(len(oldnodes) == len(oldreg["nodes"]) == 11101, "old registry count")
    require(len(newnodes) == len(newreg["nodes"]) == 11104, "new registry count")
    require(all(newnodes.get(k) == v for k, v in oldnodes.items()), "old complete registry object changed")
    require(set(newnodes) - set(oldnodes) == {"declaration:" + n for n in NAMES}, "exact new production IDs")
    require(newreg["source_commit"] == a.head and newreg["lean_verified"] is True, "site HEAD/verification")
    for name in NAMES:
        node = newnodes["declaration:" + name]
        require(node["status"] == "compiled", "new node status")
        relative, anchor = node["url"].split("#", 1)
        parser = Folds()
        parser.feed((a.site / relative).read_text(encoding="utf-8"))
        block = parser.blocks[anchor]
        require(block["open"] is False, "module Lean fold unexpectedly open")
        short = name.rsplit(".", 1)[1]
        header = core[core.index("theorem " + short + " "):].split(":= by", 1)[0]
        require(norm("".join(block["header"])) == norm(header), "raw section header mismatch: " + name)
        line = next(i for i, s in enumerate(core.splitlines(), 1) if s.startswith("theorem " + short + " "))
        require(any("/blob/" + a.head + "/" + spec["bindings"]["core"]["path"] + "#L" + str(line) in u for u in block["links"]), "pinned proof link")
    olddocs = {}
    newdocs = {}
    for kind in ["chapters", "readings", "highlights"]:
        path = "website/content/" + kind + ".json"
        oldpath = a.before / path
        require(digest(oldpath.read_bytes()) == spec["before_sha256"][path], "historical before pin: " + path)
        olddocs[kind] = load(oldpath)
        newdocs[kind] = load(root / path)
    import copy
    restored = copy.deepcopy(newdocs)
    cr = next(x for x in restored["chapters"]["chapters"] if x["slug"] == "online-ogd")
    require(cr["module_globs"].pop() == spec["bindings"]["core"]["path"], "module append")
    rr = next(x for x in restored["readings"]["readings"] if x["slug"] == "online-ogd")
    require(len(rr["source_theorems"]) == 22, "22 source cards")
    card = rr["source_theorems"].pop()
    require(len(rr["source_theorems"]) == 21, "21 prior source cards")
    lessons = restored["highlights"]["highlights"][-3:]
    require([x["full_name"] for x in lessons] == NAMES, "three ordered highlight additions")
    del restored["highlights"]["highlights"][-3:]
    require(restored == olddocs, "unrelated object or other chapter changed")
    html = unescape((a.site / "chapters/online-ogd/index.html").read_text(encoding="utf-8"))
    require(card["math"] in html, "full grouped formula absent")
    require(card["url"] in html, "source PDF link absent")
    for lesson in lessons:
        require(lesson["math"] in html and lesson["title"] in html, "lesson formula/title")
    require('class="exact-lean"' in html, "chapter exact Lean folds absent")
    values = {x["declaration"]: x for x in load(evidence["values"])["nodes"]}
    for lesson in lessons:
        require(all(n in values[lesson["full_name"]]["VALUE_constants"] for n in lesson["dependencies"]), "claimed dependency absent from VALUE")
    topology = load(evidence["topology"])
    require(any(n["id"] == "SRC-OPTIMALITY" and n["justification_status"] == "UNRESOLVED_SOURCE_PROOF_JUSTIFICATION" for n in topology["nodes"]), "source gap erased")
    require(any(n["id"] == "SPEC-ACTUAL-RUN" for n in topology["nodes"]), "source actual-run obligation absent")
    require(evidence["topology"].resolve() != evidence["values"].resolve(), "source/actual graph conflation")
    manifest = load(evidence["schema3_manifest"])
    rb = manifest["learning_contract"]["reader_backpressure"]
    require(set(rb["source_expansion_nodes"]) == {n["id"] for n in topology["nodes"]}, "source topology expansion mismatch")
    require(rb["lean_expansion_nodes"] == NAMES, "actual declaration expansion mismatch")
    for view in spec["rendered_view_checks"]:
        require(view["required_markers"], "empty rendered-view checks forbidden")
        content = (a.site / view["path"]).read_text(encoding="utf-8")
        for marker in view["required_markers"]:
            require(marker in content, "view marker missing: " + marker)
    require({v["kind"] for v in spec["rendered_view_checks"]} == {"source", "actual_VALUE"}, "both view semantics must be explicitly bound")
    coverage = load(root / spec["coverage_path"])
    c2 = next(x for x in coverage["chapters"] if x["chapter"] == 2)
    require(c2["accepted"] is False and c2["mandatory_count"] is None, "chapter falsely complete")
    require(c2["required_open_forward_containers"] == 7 and c2["required_future_mathematical_claims_open_unenumerated"] == 6, "7+6 boundary")
    require(spec["governance_status_assertions"], "B4/Goal exact assertions required")
    for assertion in spec["governance_status_assertions"]:
        require(pointer(load(root / assertion["path"]), assertion["pointer"]) == assertion["equals"], "governance status assertion")
    require({x["meaning"] for x in spec["governance_status_assertions"]} >= {"B4 7.47 open", "B4 15.31 open", "Goal ACTIVE local metadata only", "Chapter2 partial"}, "missing named open-state evidence")
    normal = load(evidence["normalization_receipt"])
    require(normal["pre_RAW_sha256"] == "5515f2800132a23830d92bace395942e1546d1446870a956c5e3c0513b2007f0" and normal["staged_and_post_RAW_sha256"] == "88745d354bbc89880245ca3c5be78a79f383412d27712064024d0a5ade4cf414", "normalization record")
    # Historical snapshots are never asserted equal to current MANIFEST after merge.
    return {"status": "passed structural checks; visual QA separate", "head": a.head, "old_nodes_preserved": 11101, "new_node_ids": ["declaration:" + n for n in NAMES], "source_cards": 22, "core_theorems": 3, "Test_theorems": 2, "governance_RAW_and_ZIP": GOVERNANCE, "source_graph_distinct_from_VALUE": True, "Goal_status_scope": "local metadata only; actual Goal tool status must be checked separately", "chapter_accepted": False, "open_containers": 7, "future_claims": 6, "source_writes": False}

if __name__ == "__main__":
    p = argparse.ArgumentParser()
    for name in ["root", "site", "gate", "before", "old-registry", "spec", "output"]:
        p.add_argument("--" + name, type=Path, required=True)
    for name in ["head", "gate-sha256", "old-registry-sha256", "spec-sha256"]:
        p.add_argument("--" + name, required=True)
    args = p.parse_args()
    if args.output.exists():
        raise SystemExit("create-only output already exists")
    try:
        result = main(args)
        code = 0
    except Exception as exc:
        result = {"status": "failed", "error_type": type(exc).__name__, "error": str(exc), "source_writes": False}
        code = 1
    with args.output.open("x", encoding="utf-8", newline="\n") as stream:
        json.dump(result, stream, ensure_ascii=False, indent=2)
        stream.write("\n")
    print(json.dumps(result, ensure_ascii=False))
    raise SystemExit(code)
