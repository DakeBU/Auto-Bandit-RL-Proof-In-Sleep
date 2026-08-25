#!/usr/bin/env python3
"""Regression tests for the frozen result-ineligible wording audit record."""

from __future__ import annotations

import copy
import json
import sys
import unittest
from pathlib import Path


TOOLS = Path(__file__).resolve().parent
ROOT = TOOLS.parent
V2 = ROOT / "evaluation" / "target-drift-v2"
sys.path.insert(0, str(TOOLS))

import audit_target_drift_wording as wording  # noqa: E402
import validate_target_drift_suite_v2 as validator  # noqa: E402


class TargetDriftWordingRecordTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.paired_path = V2 / "paired-requirements.json"
        cls.script_path = TOOLS / "audit_target_drift_wording.py"
        cls.paired = json.loads(cls.paired_path.read_text(encoding="utf-8"))
        cls.record = json.loads(
            (V2 / "wording-negative-control-record.json").read_text(encoding="utf-8")
        )
        cls.wording_result = wording.audit(cls.paired)

    def validate(
        self,
        record: dict,
        wording_result: dict | None = None,
    ) -> None:
        validator.validate_wording_negative_control_record(
            record,
            self.wording_result if wording_result is None else wording_result,
            protocol_suite_id="ABRL-TARGET-DRIFT-V2",
            paired_path=self.paired_path,
            wording_script=self.script_path,
        )

    def test_checked_in_record_reproduces_under_exact_schema(self) -> None:
        self.validate(copy.deepcopy(self.record))

    def test_every_record_object_rejects_extra_result_or_claim_fields(self) -> None:
        object_paths = [(), ("input",), ("script",), ("audit",)]
        for object_path in object_paths:
            for forbidden_key in ("result", "claim"):
                with self.subTest(object_path=object_path, key=forbidden_key):
                    mutated = copy.deepcopy(self.record)
                    target = mutated
                    for key in object_path:
                        target = target[key]
                    target[forbidden_key] = "must be rejected"
                    with self.assertRaisesRegex(SystemExit, "keys differ"):
                        self.validate(mutated)

    def test_recomputed_audit_rejects_extra_result_or_claim_fields(self) -> None:
        for forbidden_key in ("result", "claim"):
            with self.subTest(key=forbidden_key):
                mutated_result = copy.deepcopy(self.wording_result)
                mutated_result[forbidden_key] = "must be rejected"
                with self.assertRaisesRegex(SystemExit, "keys differ"):
                    self.validate(copy.deepcopy(self.record), mutated_result)

    def test_every_record_object_rejects_missing_keys(self) -> None:
        object_schemas = [
            ((), validator.WORDING_RECORD_KEYS),
            (("input",), validator.WORDING_BINDING_KEYS),
            (("script",), validator.WORDING_BINDING_KEYS),
            (("audit",), validator.WORDING_AUDIT_KEYS),
        ]
        for object_path, expected_keys in object_schemas:
            for missing_key in sorted(expected_keys):
                with self.subTest(object_path=object_path, key=missing_key):
                    mutated = copy.deepcopy(self.record)
                    target = mutated
                    for key in object_path:
                        target = target[key]
                    del target[missing_key]
                    with self.assertRaisesRegex(SystemExit, "keys differ"):
                        self.validate(mutated)

    def test_nested_record_values_must_remain_objects(self) -> None:
        for object_key in ("input", "script", "audit"):
            with self.subTest(object_key=object_key):
                mutated = copy.deepcopy(self.record)
                mutated[object_key] = []
                with self.assertRaisesRegex(SystemExit, "must be an object"):
                    self.validate(mutated)

    def test_schema_versions_are_fixed_integers(self) -> None:
        mutations = [
            ("record-version", lambda record, result: record.__setitem__("schema_version", 2)),
            ("record-bool-version", lambda record, result: record.__setitem__("schema_version", True)),
            ("audit-version", lambda record, result: record["audit"].__setitem__("schema_version", 2)),
            ("recomputed-version", lambda record, result: result.__setitem__("schema_version", 2)),
        ]
        for label, mutate in mutations:
            with self.subTest(label=label):
                record = copy.deepcopy(self.record)
                result = copy.deepcopy(self.wording_result)
                mutate(record, result)
                with self.assertRaisesRegex(SystemExit, "schema_version"):
                    self.validate(record, result)

    def test_command_is_byte_for_byte_frozen(self) -> None:
        mutations = [
            "python3 tools/audit_target_drift_wording.py --bank "
            "evaluation/target-drift-v2/paired-requirements.json",
            validator.WORDING_RECORD_COMMAND + " --output result.json",
            validator.WORDING_RECORD_COMMAND + " ",
        ]
        for command in mutations:
            with self.subTest(command=command):
                mutated = copy.deepcopy(self.record)
                mutated["command"] = command
                with self.assertRaisesRegex(SystemExit, "frozen command"):
                    self.validate(mutated)


if __name__ == "__main__":
    unittest.main()
