"""Recheck shared heavy-tail identities and rendered declaration destinations."""
import json
from html.parser import HTMLParser
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "website" / "_site"

class Anchors(HTMLParser):
    def __init__(self):
        super().__init__()
        self.ids = set()
        self.hrefs = set()
    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if "id" in attrs:
            self.ids.add(attrs["id"])
        if tag == "a" and "href" in attrs:
            self.hrefs.add(attrs["href"])

def verify():
    wiki = json.loads((ROOT / "website/content/banditrlwiki.json").read_text(encoding="utf-8"))
    topic = next(t for t in wiki["topics"] if t["id"] == "heavy-tailed")
    mapping = topic["formalization"]
    registry = json.loads((OUT / "books/registry.json").read_text(encoding="utf-8"))
    nodes = {n["id"]: n for n in registry["nodes"]}
    setting = next(s for s in registry["settings"] if s["id"] == "heavy-tailed")
    graph = json.loads((OUT / "lean-graph/scopes/settings/heavy-tailed.json").read_text(encoding="utf-8"))
    expected = {"declaration:" + d["name"] for d in mapping["declarations"]}
    assert setting["formalization"] == mapping
    assert setting["status"] == "mapped-reviewed-partial"
    assert mapping["topic_complete"] is False
    assert set(setting["node_ids"]) == expected
    assert {n["id"] for n in graph["nodes"] if n["id"].startswith("declaration:")} == expected
    page = OUT / "banditrlwiki/topics/heavy-tailed/index.html"
    rendered = page.read_text(encoding="utf-8")
    assert "topic incomplete" in rendered
    anchors = Anchors()
    anchors.feed(rendered)
    resolved = set()
    for href in anchors.hrefs:
        if ":" in href or "#" not in href:
            continue
        path, anchor = href.split("#", 1)
        resolved.add(((page.parent / path).resolve(), anchor))
    targets = []
    for key in sorted(expected):
        node = nodes[key]
        assert "heavy-tailed" in node["settings"]
        path, anchor = node["url"].split("#", 1)
        target = OUT / path
        assert (target.resolve(), anchor) in resolved, key
        actual = Anchors()
        actual.feed(target.read_text(encoding="utf-8"))
        assert anchor in actual.ids, key
        targets.append({"id": key, "url": node["url"], "statement_sha256": node["statement_sha256"]})
    return {"mapped_declarations": targets, "scope_nodes": len(graph["nodes"]),
            "scope_edges": len(graph["edges"]), "canonical_node_count": len(nodes),
            "all_rendered_destinations_valid": True, "topic_complete": False,
            "source_commit": registry["source_commit"], "lean_verified": registry["lean_verified"]}

if __name__ == "__main__":
    print(json.dumps(verify(), indent=2))
