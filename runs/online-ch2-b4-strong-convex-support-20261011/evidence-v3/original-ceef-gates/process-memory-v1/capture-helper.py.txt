"""Gate recorder for prescient Euclidean and current-main governance, Python3.8 stdlib; no gate executed by preparation."""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import zipfile


def utc():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def digest(data):
    return hashlib.sha256(data).hexdigest()


def create(path, data):
    if not isinstance(data, bytes):
        data = (json.dumps(data, ensure_ascii=False, indent=2) + "\n").encode("utf-8")
    with path.open("xb") as stream:
        stream.write(data)


def git(root, *args):
    proc = subprocess.run(["git", "-c", "core.longpaths=true"] + list(args), cwd=str(root), stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE)
    if proc.returncode:
        raise RuntimeError("git failed: " + repr(args) + ": " + proc.stderr.decode("utf-8", "replace"))
    return proc.stdout


def state(root):
    return {"HEAD": git(root, "rev-parse", "HEAD").decode().strip(),
            "branch": git(root, "branch", "--show-current").decode().strip(),
            "status_porcelain_v1_z_hex": git(root, "status", "--porcelain=v1", "-z").hex()}


def inventory(root, run, owned):
    # Start with tracked names, then explicitly filter to current source/input trees below.
    names = set(x.decode("utf-8") for x in git(root, "ls-files", "-z", "--cached").split(b"\0") if x)
    # Add new source paths, including ignored additions inside actual source trees.
    for folder in ("BanditRLProof", "Tests", "tools", "website/scripts", "website/content",
                   "website/static", "research-wiki/contribution-contracts", ".github/workflows"):
        for path in (root / folder).rglob("*"):
            if path.is_file() and "__pycache__" not in path.parts:
                names.add(path.relative_to(root).as_posix())
    for name in ("BanditRLProof.lean", "Tests.lean", "lean-toolchain", "lakefile.lean",
                 "lake-manifest.json", ".gitattributes"):
        names.add(name)
    names.update(owned)
    contract_roots = [name.rsplit("/", 1)[0] for name in owned if name.startswith("docs/contracts/")]
    extra = {"README.md", "AGENTS.md", "CONTRIBUTING.md", "docs/contribution-contract.schema.json", "docs/contributor-codex-contract.md", "docs/theorem-publication-protocol.md", "docs/contracts/online-book-v1/coverage.json", "docs/proof-digestion-protocol.md", "docs/evidence-routed-memory-protocol.md", "docs/openai-math-assimilation-protocol.md", "research-wiki/openai-math-2026-intake.json", "runs/process_memory.json"}
    names = {name for name in names if selected_for_zip(name, contract_roots) or name in extra}
    result = []
    for name in sorted(names):
        path = root / name
        resolved = path.resolve()
        if resolved == run or run in resolved.parents:
            continue
        if root not in resolved.parents or path.is_symlink() or not path.is_file():
            raise RuntimeError("Input must be an existing ordinary repository file: " + name)
        data = path.read_bytes()
        result.append({"path": name, "raw_sha256": digest(data), "bytes": len(data)})
    return result


def selected_for_zip(name, contract_roots):
    # Historical runs are excluded from both selected RAW inventory and ZIP; clean HEAD binds them.
    if name == "runs/process_memory.json":
        return True
    if name.startswith("runs/"):
        return False
    prefixes = ("BanditRLProof/", "Tests/", "tools/", "website/scripts/",
                "website/content/", "website/static/", "research-wiki/contribution-contracts/",
                ".github/workflows/")
    exact = {"README.md", "AGENTS.md", "CONTRIBUTING.md", "docs/contribution-contract.schema.json", "docs/contributor-codex-contract.md", "docs/theorem-publication-protocol.md", "docs/contracts/online-book-v1/coverage.json", "BanditRLProof.lean", "Tests.lean", "lean-toolchain", "lakefile.lean",
             "lake-manifest.json", ".gitattributes", "docs/proof-digestion-protocol.md", "docs/evidence-routed-memory-protocol.md", "docs/openai-math-assimilation-protocol.md", "research-wiki/openai-math-2026-intake.json"}
    return (name in exact or name.startswith(prefixes) or
            any(name.startswith(folder.rstrip("/") + "/") for folder in contract_roots))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", required=True)
    parser.add_argument("--run", required=True, help="New evidence namespace beneath runs/ or an already ignored tmp/ namespace")
    parser.add_argument("--label", required=True)
    parser.add_argument("--owned-source", action="append", default=[])
    parser.add_argument("--leaf-contract", action="append", required=True,
                        help="Current leaf docs/contracts subtree to include in ZIP")
    parser.add_argument("argv", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    root = Path(args.root).resolve()
    run = (root / args.run).resolve()
    argv = args.argv[1:] if args.argv[:1] == ["--"] else args.argv
    if not argv or not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_.-]*", args.label):
        raise RuntimeError("Exact argv and safe unique label required")
    if root / "runs" not in run.parents and root / "tmp" not in run.parents:
        raise RuntimeError("Evidence namespace must be beneath root/runs/ or root/tmp/")
    if root / "tmp" in run.parents:
        probe = run.relative_to(root).as_posix() + "/.capture-ignore-probe"
        result = subprocess.run(["git", "check-ignore", "--quiet", "--", probe],
                                cwd=str(root), stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        if result.returncode != 0:
            raise RuntimeError("tmp evidence namespace must already be ignored; no ignore rule changes permitted")
    for folder in args.leaf_contract:
        resolved = (root / folder).resolve()
        if root / "docs" / "contracts" not in resolved.parents:
            raise RuntimeError("Leaf contract must be a docs/contracts subtree")
        if not resolved.is_dir():
            raise RuntimeError("Leaf contract subtree missing")
        args.owned_source.extend(path.relative_to(root).as_posix()
                                 for path in resolved.rglob("*") if path.is_file())
    dest = run / args.label
    dest.mkdir(parents=True, exist_ok=False)
    helper = Path(__file__).resolve().read_bytes()
    create(dest / "capture-helper.py.txt", helper)
    record = {"argv": argv, "cwd": str(root), "helper_sha256": digest(helper),
              "evidence_namespace_excluded": run.relative_to(root).as_posix(),
              "actual_evidence_namespace": str(run),
              "evidence_port_boundary": "Receipts originate here; any later exact copy into RUN requires a separate port manifest. No contemporaneous canonical RUN claim.",
              "owned_source": args.owned_source, "command_started": False, "actual_exit": None,
              "ZIP_is_whole_repository_archive": False,
              "ZIP_scope": "Selected active source/input trees and current leaf contracts; historical runs excluded; curated current runs/process_memory.json included",
              "full_RAW_inventory_scope": "Every library/Test source and enumerated current harness/site source/input tree plus current leaf contracts. Historical archives not separately RAW-hashed (curated current process memory is an active input); committed HEAD and clean Git status bind repository state.",
              "leaf_contract_roots": args.leaf_contract}
    try:
        before = inventory(root, run, args.owned_source)
        record["pre_git"] = state(root)
        if record["pre_git"]["status_porcelain_v1_z_hex"]:
            raise RuntimeError("Clean committed candidate required before gate")
        create(dest / "pre-source-inputs.json", before)
        selected = [row for row in before if selected_for_zip(row["path"], args.leaf_contract)]
        create(dest / "pre-selected-ZIP-inputs.json", selected)
        record["ZIP_selected_files"] = len(selected)
        record["full_RAW_inventory_files"] = len(before)
        with zipfile.ZipFile(str(dest / "pre-selected-source-raw.zip"), "x", zipfile.ZIP_DEFLATED) as archive:
            for row in selected:
                data = (root / row["path"]).read_bytes()
                if digest(data) != row["raw_sha256"]:
                    raise RuntimeError("Source changed during snapshot: " + row["path"])
                archive.writestr(row["path"], data)
        if any(digest((root / row["path"]).read_bytes()) != row["raw_sha256"] for row in selected):
            raise RuntimeError("Selected ZIP source changed before command")
        if state(root) != record["pre_git"]:
            raise RuntimeError("Git changed before command")
        record["precommand_check"] = "Selected ZIP RAW hashes and Git state; no redundant second full inventory. Full pre/post manifests remain authoritative."
        record["start_utc"] = utc()
        record["command_started"] = True
        with (dest / "stdout.raw").open("xb") as out, (dest / "stderr.raw").open("xb") as err:
            proc = subprocess.run(argv, cwd=str(root), stdout=out, stderr=err,
                                  env=dict(os.environ, PYTHONDONTWRITEBYTECODE="1"))
        record["end_utc"] = utc()
        record["actual_exit"] = proc.returncode
        after = inventory(root, run, args.owned_source)
        create(dest / "post-source-inputs.json", after)
        record["post_git"] = state(root)
        record["complete_source_path_set_and_RAW_unchanged"] = before == after
        record["HEAD_and_branch_unchanged"] = all(record["pre_git"][k] == record["post_git"][k]
                                                 for k in ("HEAD", "branch"))
        record["git_status_unchanged"] = record["pre_git"] == record["post_git"]
        record["capture_integrity_ok"] = before == after and record["HEAD_and_branch_unchanged"] and record["git_status_unchanged"]
    except Exception as exc:
        record["capture_error"] = repr(exc)
        record["capture_integrity_ok"] = False
        record.setdefault("end_utc", utc())
    for name in ("stdout.raw", "stderr.raw", "pre-source-inputs.json", "post-source-inputs.json",
                 "pre-selected-ZIP-inputs.json", "pre-selected-source-raw.zip"):
        path = dest / name
        if path.exists():
            record[name + "_sha256"] = digest(path.read_bytes())
    create(dest / "receipt.json", record)
    print(json.dumps({"receipt": str(dest / "receipt.json"), "actual_exit": record["actual_exit"],
                      "capture_integrity_ok": record["capture_integrity_ok"]}))
    if not record["capture_integrity_ok"]:
        return 125
    return record["actual_exit"] if record["actual_exit"] is not None else 125


if __name__ == "__main__":
    sys.exit(main())
