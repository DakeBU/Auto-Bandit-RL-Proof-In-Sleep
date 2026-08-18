#!/usr/bin/env python3
"""Result-free structural and text-only audit for paired target-drift wording."""

from __future__ import annotations

import argparse
import json
import math
import re
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_BANK = ROOT / "evaluation" / "target-drift-v2" / "paired-requirements.json"
TOKEN = re.compile(r"[a-z0-9]+")


def load(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def tokens(text: str) -> set[str]:
    return set(TOKEN.findall(text.lower()))


def render(template: str, field: str, value: str) -> str:
    return template.replace("{{FIELD}}", field).replace("{{VALUE}}", value)


def leave_one_pair_out_accuracy(payload: dict[str, Any]) -> float:
    documents: list[tuple[int, int, set[str]]] = []
    template = payload["common_template"]
    for pair_index, entry in enumerate(payload["cases"]):
        for label, key in enumerate(("source_faithful_value", "injected_drift_value")):
            documents.append((
                pair_index,
                label,
                tokens(render(template, entry["field"], entry[key])),
            ))
    correct = 0
    for held_pair, label, held_tokens in documents:
        train = [item for item in documents if item[0] != held_pair]
        vocabulary = set().union(*(item[2] for item in train))
        class_counts = [sum(item[1] == value for item in train) for value in (0, 1)]
        scores = []
        for class_label in (0, 1):
            score = math.log(class_counts[class_label] / len(train))
            for word in vocabulary:
                present = sum(
                    1 for _, candidate_label, words in train
                    if candidate_label == class_label and word in words
                )
                probability = (present + 1) / (class_counts[class_label] + 2)
                score += math.log(probability if word in held_tokens else 1 - probability)
            scores.append(score)
        predicted = int(scores[1] > scores[0])
        correct += predicted == label
    return correct / len(documents)


def audit(payload: dict[str, Any]) -> dict[str, Any]:
    template = payload["common_template"]
    if template.count("{{FIELD}}") != 1 or template.count("{{VALUE}}") != 1:
        raise SystemExit("wording audit failed: common template placeholders are invalid")
    rendered = []
    for entry in payload["cases"]:
        for key in ("source_faithful_value", "injected_drift_value"):
            text = render(template, entry["field"], entry[key])
            if "{{" in text or "}}" in text:
                raise SystemExit("wording audit failed: unresolved template placeholder")
            rendered.append(text)
    if len(rendered) != 60 or len(set(rendered)) != 60:
        raise SystemExit("wording audit failed: expected sixty unique rendered requirements")
    legacy_markers = re.compile(
        r"implement a lean target that preserves|while retaining|with no |without |"
        r"is retained|are retained|faithful variant|drift variant",
        re.IGNORECASE,
    )
    marker_hits = [text for text in rendered if legacy_markers.search(text)]
    if marker_hits:
        raise SystemExit(
            f"wording audit failed: {len(marker_hits)} rendered requirements contain legacy style cues"
        )
    return {
        "schema_version": 1,
        "suite_id": payload["suite_id"],
        "paired_case_count": len(payload["cases"]),
        "rendered_requirement_count": len(rendered),
        "identical_template": True,
        "legacy_style_marker_hits": 0,
        "deterministic_leave_one_pair_out_bernoulli_nb_accuracy":
            leave_one_pair_out_accuracy(payload),
        "interpretation": (
            "This diagnostic is a preregistered negative control, not a result of the "
            "formalization evaluation. A separate frozen text-only model audit and blind "
            "human review remain mandatory before primary execution."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--bank", type=Path, default=DEFAULT_BANK)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = audit(load(args.bank.resolve()))
    payload = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output is not None:
        if args.output.exists():
            raise SystemExit("wording audit failed: refusing to overwrite output")
        args.output.write_text(payload, encoding="utf-8")
    print(payload, end="")


if __name__ == "__main__":
    main()
