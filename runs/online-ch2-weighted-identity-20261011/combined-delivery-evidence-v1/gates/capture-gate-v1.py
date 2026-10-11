"""Prepared gate recorder, Python 3.8 stdlib; execution requires separate authorization."""
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
    proc = subprocess.run(["git"] + list(args), cwd=str(root), stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE)
    if proc.returncode:
        raise RuntimeError("git failed: " + repr(args) + ": " + proc.stderr.decode("utf-8", "replace"))
    return proc.stdout


def state(root):
    return {"HEAD": git(root, "rev-parse", "HEAD").decode().strip(),
            "branch": git(root, "branch", "--show-current").decode().strip(),
            "status_porcelain_v1_z_hex": git(root, "status", "--porcelain=v1", "-z").hex()}


def inventory(root, run, owned):
    # All tracked regular inputs, except the explicitly declared evidence namespace.
    names = set(x.decode("utf-8") for x in git(root, "ls-files", "-z", "--cached").split(b"\0") if x)
    # Add new source paths, including ignored additions inside actual source trees.
    for folder in ("BanditRLProof", "Tests", "tools", "website/scripts", "website/content",
                   "website/static", "research-wiki/contribution-contracts"):
        for path in (root / folder).rglob("*"):
            if path.is_file() and "__pycache__" not in path.parts:
                names.add(path.relative_to(root).as_posix())
    for name in ("BanditRLProof.lean", "Tests.lean", "lean-toolchain", "lakefile.lean",
                 "lake-manifest.json", ".gitattributes"):
        names.add(name)
    names.update(owned)
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


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", required=True)
    parser.add_argument("--run", required=True, help="New evidence namespace beneath runs/")
    parser.add_argument("--label", required=True)
    parser.add_argument("--owned-source", action="append", default=[])
    parser.add_argument("argv", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    root = Path(args.root).resolve()
    run = (root / args.run).resolve()
    argv = args.argv[1:] if args.argv[:1] == ["--"] else args.argv
    if not argv or not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_.-]*", args.label):
        raise RuntimeError("Exact argv and safe unique label required")
    if root / "runs" not in run.parents:
        raise RuntimeError("Evidence namespace must be beneath root/runs/")
    dest = run / args.label
    dest.mkdir(parents=True, exist_ok=False)
    helper = Path(__file__).resolve().read_bytes()
    create(dest / "capture-helper.py.txt", helper)
    record = {"argv": argv, "cwd": str(root), "helper_sha256": digest(helper),
              "evidence_namespace_excluded": run.relative_to(root).as_posix(),
              "owned_source": args.owned_source, "command_started": False, "actual_exit": None}
    try:
        before = inventory(root, run, args.owned_source)
        record["pre_git"] = state(root)
        create(dest / "pre-source-inputs.json", before)
        with zipfile.ZipFile(str(dest / "pre-source-raw.zip"), "x", zipfile.ZIP_DEFLATED) as archive:
            for row in before:
                data = (root / row["path"]).read_bytes()
                if digest(data) != row["raw_sha256"]:
                    raise RuntimeError("Source changed during snapshot: " + row["path"])
                archive.writestr(row["path"], data)
        if inventory(root, run, args.owned_source) != before or state(root) != record["pre_git"]:
            raise RuntimeError("Inputs/Git changed before command")
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
        record["capture_integrity_ok"] = before == after and record["HEAD_and_branch_unchanged"]
    except Exception as exc:
        record["capture_error"] = repr(exc)
        record["capture_integrity_ok"] = False
        record.setdefault("end_utc", utc())
    for name in ("stdout.raw", "stderr.raw", "pre-source-inputs.json", "post-source-inputs.json",
                 "pre-source-raw.zip"):
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
