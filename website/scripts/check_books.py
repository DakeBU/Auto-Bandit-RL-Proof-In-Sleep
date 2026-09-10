"""Validate generated memberships and compatibility, independently of rendering."""
import json
from html.parser import HTMLParser
from pathlib import Path


class Anchors(HTMLParser):
    def __init__(self):
        super().__init__()
        self.ids = set()

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if attrs.get("id"):
            self.ids.add(attrs["id"])


def check_books(output):
    output = Path(output)
    errors = []
    try:
        registry = json.loads((output / "books/registry.json").read_text(encoding="utf-8"))
        graph = json.loads((output / "lean-graph/graph.json").read_text(encoding="utf-8"))
        scopes = json.loads((output / "lean-graph/scope-index.json").read_text(encoding="utf-8"))["scopes"]
        manifest = json.loads((output / "site-manifest.json").read_text(encoding="utf-8"))
        source_dir = Path(__file__).resolve().parents[1] / "content"
        config = json.loads((source_dir / "books.json").read_text(encoding="utf-8"))
        wiki = json.loads((source_dir / "banditrlwiki.json").read_text(encoding="utf-8"))
    except (OSError, ValueError, KeyError) as error:
        return [f"shared Books export missing or invalid: {error}"]
    nodes = {n["id"]: n for n in registry["nodes"]}
    graph_nodes = {n["id"]: n for n in graph["nodes"] if n["id"].startswith("declaration:")}
    if len(nodes) != len(registry["nodes"]) or nodes.keys() != graph_nodes.keys():
        errors.append("canonical registry must contain each graph declaration exactly once")
    if registry["books"] != config["books"]:
        errors.append("generated book registration differs from source")
    if registry["source_commit"] != manifest["source_commit"] or registry["lean_verified"] != manifest["lean_verified"]:
        errors.append("Books registry provenance differs from the site manifest")
    for node_id, node in nodes.items():
        other = graph_nodes.get(node_id, {})
        for key in ("books", "chapters", "settings", "status"):
            if node[key] != other.get(key):
                errors.append(f"canonical node differs across graph and registry: {node_id} ({key})")
                break
        if not manifest["lean_verified"] and node["status"] == "compiled":
            errors.append(f"preview registry falsely marks node compiled: {node_id}")
    expected_scope_keys = {(kind, r["id"]) for kind in ("books", "settings") for r in registry[kind]}
    if {(s["kind"], s["id"]) for s in scopes} != expected_scope_keys or len(scopes) != len(expected_scope_keys):
        errors.append("missing or duplicate book/setting graph scope")
    for scope in scopes:
        expected = {key for key, node in nodes.items() if scope["id"] in node[scope["kind"]]}
        if set(scope["node_ids"]) != expected:
            errors.append(f"scope reference set disagrees with canonical membership: {scope['id']}")
        shard = json.loads((output / "lean-graph" / scope["slice"]).read_text(encoding="utf-8"))
        for node in shard["nodes"]:
            if node["id"] in nodes and node["status"] != nodes[node["id"]]["status"]:
                errors.append(f"scope status override: {node['id']}")
    routes = {
        "index.html": {"books", "primary-textbook", "book-map", "textbook-spine", "reading-order"},
        "learning/index.html": {"learning", "path", "book-map", "textbook-spine"},
        "textbook-spine/index.html": {"spine", "source", "chapters", "dependencies"},
        "banditrlwiki/index.html": {"overview", "settings", "cases", "topics"},
    }
    routes.update({chapter["url"]: {"chapter"} for chapter in registry["chapters"]})
    for route, anchors in routes.items():
        target = output / route
        if not target.is_file():
            errors.append(f"legacy route missing: {route}")
            continue
        parser = Anchors()
        parser.feed(target.read_text(encoding="utf-8"))
        if anchors - parser.ids:
            errors.append(f"legacy anchors missing: {route}: {sorted(anchors - parser.ids)}")
    for book in config["books"]:
        source = (output / f"books/{book['id']}/index.html").read_text(encoding="utf-8")
        if book["status"] == "planned" and ('class="status compiled"' in source or 'chapter contracts compiled' in source):
            errors.append(f"planned book displays compiled coverage: {book['id']}")
    for topic in wiki["topics"]:
        source = (output / f"banditrlwiki/topics/{topic['id']}/index.html").read_text(encoding="utf-8")
        if source.count("Pending source verification</dd>") != len(wiki["comparison_fields"]):
            errors.append(f"topic lacks the full pending comparison contract: {topic['id']}")
    return errors
