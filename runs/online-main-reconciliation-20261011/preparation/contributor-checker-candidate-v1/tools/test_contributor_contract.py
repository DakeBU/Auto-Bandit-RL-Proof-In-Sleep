from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from tools import check_contributor_contract as contract


def base_contract() -> dict:
    return {
        "schema_version": "2.0",
        "id": "TEST-CONTRACT",
        "route": "internal",
        "frontier_cell": "n/a",
        "source_facing": False,
        "source": {
            "kind": "internal-design",
            "title": "test",
            "version": "test",
            "anchor": "test",
            "url": ""
        },
        "target": "test target",
        "affected_files": ["website/content/example.json"],
        "declarations": [],
        "reuse_plan": {
            "classification": "out_of_scope",
            "decision": "out_of_scope",
            "searched_existing": [],
            "reused_declarations": [],
            "new_shared_declarations": [],
            "known_consumers": [],
            "planned_consumers": [],
            "no_duplicate_wrapper": True,
            "decision_reason": "tooling-only fixture"
        },
        "reader_contract": {
            "source_anchor_visible": False,
            "natural_language_formula_proof": False,
            "hidden_assumptions_visible": False,
            "source_vs_lean_delta_visible": False,
            "lean_folded": False,
            "dependencies_visible": False,
            "remaining_boundary_visible": False
        },
        "semantic_roundtrip": {
            "required": False,
            "status": "not-required",
            "formalizer": "fixture",
            "blind_decoder": "",
            "source_reviewer": "",
            "verdict": "not-required",
            "remaining_semantic_delta": "n/a"
        },
        "graph_contribution": {
            "lean_graph": "no-change-with-reason",
            "overview_graph": "updated",
            "functor_hypergraph": "none-found-with-reason",
            "functor_reason": "fixture does not add mathematics",
            "focus_targets": [],
            "visual_review": "fixture",
            "edge_semantics": "formal-solid; overlays-dashed"
        },
        "progress_updates": {
            "teaching_route": "no-change-with-reason: fixture",
            "banditrlwiki": "no-change-with-reason: fixture",
            "results_ledger": "no-change-with-reason: fixture",
            "roadmap": "no-change-with-reason: fixture",
            "website_surfaces": ["fixture"]
        },
        "truth_boundary": "fixture only",
        "verification": {
            "focused_checks": [],
            "bandit_check": "fixture",
            "site_build": "fixture",
            "site_check": "fixture",
            "independent_review": "fixture"
        },
        "contributor": {"name": "fixture", "role": "test"}
    }


def validate(payload: dict) -> list[str]:
    with tempfile.TemporaryDirectory(dir=contract.ROOT / "tools") as directory:
        path = Path(directory) / "contract.json"
        path.write_text(json.dumps(payload), encoding="utf-8")
        _data, errors = contract.validate_contract(path)
        return errors


class ContributorContractTests(unittest.TestCase):
    def test_internal_design_contract_can_be_valid(self) -> None:
        self.assertEqual(validate(base_contract()), [])

    def test_source_facing_requires_distinct_accepted_reviewers(self) -> None:
        payload = base_contract()
        payload["source_facing"] = True
        payload["source"]["kind"] = "paper"
        payload["source"]["url"] = "https://example.invalid/source"
        payload["declarations"] = ["BanditRLProof.Example.sourceTheorem"]
        payload["reader_contract"] = {
            key: True for key in contract.READER_REQUIRED
        }
        payload["semantic_roundtrip"] = {
            "required": True,
            "status": "accepted",
            "formalizer": "same-agent",
            "blind_decoder": "same-agent",
            "source_reviewer": "reviewer",
            "verdict": "accepted",
            "remaining_semantic_delta": "none"
        }
        errors = validate(payload)
        self.assertTrue(any("roles must be distinct" in error for error in errors))

    def test_new_shared_requires_two_consumers(self) -> None:
        payload = base_contract()
        payload["reuse_plan"]["classification"] = "missing"
        payload["reuse_plan"]["decision"] = "new_shared"
        payload["reuse_plan"]["new_shared_declarations"] = ["BanditRLProof.Shared.foo"]
        payload["reuse_plan"]["planned_consumers"] = ["route:a"]
        errors = validate(payload)
        self.assertTrue(any("at least two named consumers" in error for error in errors))


import contextlib
import io
import json
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
from tools import check_contributor_contract as contract

class HistoricalRows(unittest.TestCase):
    source = "BanditRLProof/Shared.lean"
    manifest = "research-wiki/contribution-contracts/HIST.json"

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.saved = contract.ROOT
        contract.ROOT = self.root
        self.addCleanup(setattr, contract, "ROOT", self.saved)
        self.git("init", "-b", "main")
        self.git("config", "user.email", "fixture@example.test")
        self.git("config", "user.name", "Fixture")
        self.git("config", "core.autocrlf", "false")
        self.write("README", "fixture\n")
        self.commit("root")
        self.root_commit = self.rev()
        self.git("checkout", "-b", "source")
        self.write(self.source, "theorem shared : True := True.intro\n")
        d = base_contract(); d["affected_files"] = [self.source]
        self.write(self.manifest, json.dumps(d))
        self.commit("source and contract")
        self.origin = self.rev()

    def git(self, *args):
        p = subprocess.run(["git", *args], cwd=self.root, capture_output=True)
        if p.returncode: raise AssertionError(p.stderr.decode(errors="replace"))
        return p.stdout.decode().strip()

    def rev(self): return self.git("rev-parse", "HEAD")
    def write(self, p, text):
        q = self.root / p; q.parent.mkdir(parents=True, exist_ok=True); q.write_bytes(text.encode())
    def commit(self, msg): self.git("add", "."); self.git("commit", "-m", msg)
    def integrate(self, mismatch=False):
        raw = (self.root / self.source).read_bytes()
        self.git("checkout", "main")
        self.write(self.source, raw.decode() if not mismatch else "different\n")
        self.commit("independent main integration")
        self.base = self.rev()
        if mismatch:
            # Resolve this intentionally conflicting fixture with main source.
            p = subprocess.run(["git", "merge", "--no-ff", "source", "-m", "merge"], cwd=self.root, capture_output=True)
            assert p.returncode != 0
            self.git("checkout", "--ours", self.source); self.git("add", self.source); self.git("commit", "--no-edit")
        else: self.git("merge", "--no-ff", "source", "-m", "merge")
    def cert(self): return contract.historical_row_certificate(self.base, self.manifest, self.source)
    def test_positive_and_gate(self):
        self.integrate(); self.assertIsNotNone(self.cert())
        self.write("website/content/new.json", "{}")
        d=base_contract(); d["id"]="NEW"; d["affected_files"]=["website/content/new.json"]
        self.write("research-wiki/contribution-contracts/NEW.json",json.dumps(d));self.commit("active covered")
        with patch("sys.argv", ["checker", "--base", self.base]), contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(0, contract.main())
    def test_new_stale_and_duplicate_not_masked(self):
        self.integrate(); d=base_contract();d["id"]="NEW";d["affected_files"]=[self.source,"website/content/new.json"]
        self.write("research-wiki/contribution-contracts/NEW.json",json.dumps(d));self.write("website/content/new.json","{}");self.commit("new stale")
        self.assertIsNotNone(self.cert())
        with patch("sys.argv", ["checker", "--base", self.base]), contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(1, contract.main())
    def test_dirty_historical_manifest(self):
        self.integrate();self.write(self.manifest,(self.root/self.manifest).read_text()+" ")
        self.assertIsNone(self.cert())
    def test_modified_historical(self):
        self.integrate();self.write(self.manifest,(self.root/self.manifest).read_text()+" ");self.commit("modify")
        self.assertIsNone(self.cert())
    def test_modified_then_reverted(self):
        self.integrate();raw=(self.root/self.manifest).read_text();self.write(self.manifest,raw+" ");self.commit("modify");self.write(self.manifest,raw);self.commit("revert")
        self.assertIsNone(self.cert())
    def test_source_origin_bytes_mismatch(self):
        self.integrate(mismatch=True);self.assertIsNone(self.cert())
    def test_source_mode_mismatch(self):
        self.integrate();self.git("update-index","--chmod=+x",self.source);self.git("commit","-m","mode")
        self.assertIsNone(self.cert())
    def test_no_integration_witness(self):
        self.base=self.root_commit;self.assertIsNone(self.cert())
    def test_removed_readded(self):
        raw=(self.root/self.manifest).read_text();d=json.loads(raw);d["affected_files"]=[]
        self.write(self.manifest,json.dumps(d));self.commit("remove row");self.write(self.manifest,raw);self.commit("readd row")
        self.integrate();self.assertIsNone(self.cert())
    def test_historical_prose_amendment(self):
        d=json.loads((self.root/self.manifest).read_text());d["target"]="historical correction"
        self.write(self.manifest,json.dumps(d));self.commit("amend historically");self.integrate();self.assertIsNotNone(self.cert())
    def test_uncovered_production(self):
        self.integrate();self.write("website/content/new.json","{}");self.commit("uncovered")
        with patch("sys.argv", ["checker", "--base", self.base]), contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(1, contract.main())
    def test_five_rows(self):
        # Five distinct protected rows, identical independently integrated source.
        paths=[self.source]+["BanditRLProof/Shared%d.lean"%i for i in range(4)]
        for p in paths[1:]:self.write(p,"theorem t : True := True.intro\n")
        d=base_contract();d["affected_files"]=paths;self.write(self.manifest,json.dumps(d));self.commit("five row amendment")
        payload={p:(self.root/p).read_text() for p in paths}
        self.git("checkout","main")
        for p,t in payload.items():self.write(p,t)
        self.commit("main five");self.base=self.rev();self.git("merge","--no-ff","source","-m","merge")
        self.assertEqual(5,sum(contract.historical_row_certificate(self.base,self.manifest,p) is not None for p in paths))


if __name__ == "__main__":
    unittest.main()
