from __future__ import annotations

from datetime import datetime, timedelta, timezone
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from unittest import mock

from tools import prepare_target_drift_human_contract_review as review_prepare
from tools import validate_target_drift_human_contract_review as review_validate
from tools import validate_target_drift_human_contract_external_verification as external


SSH_KEYGEN = shutil.which("ssh-keygen")


def dump(path: Path, value: dict) -> None:
    path.write_text(
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )


def utc_text(value: datetime) -> str:
    return value.astimezone(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


class ExternalVerificationAvailabilityTest(unittest.TestCase):
    def test_production_validator_fails_closed_without_ssh_keygen(self) -> None:
        with mock.patch.object(external.shutil, "which", return_value=None):
            with self.assertRaises(external.ExternalVerificationError):
                external.ssh_keygen_path()

    def test_frozen_protocol_rejects_namespace_role_and_schema_drift(self) -> None:
        protocol = external.load(external.DEFAULT_PROTOCOL)
        mutations = []
        namespace = json.loads(json.dumps(protocol))
        namespace["signature_namespace"] = "attacker-selected-namespace"
        mutations.append(namespace)
        role = json.loads(json.dumps(protocol))
        role["required_registry_roles"]["reviewer_a"] = "attacker-selected-role"
        mutations.append(role)
        schema = json.loads(json.dumps(protocol))
        schema["external_receipt_template"]["unreviewed_extension"] = "UNSET"
        mutations.append(schema)
        for mutation in mutations:
            with self.subTest(mutation=mutation.get("signature_namespace")):
                with self.assertRaises(external.ExternalVerificationError):
                    external.validate_protocol(mutation)


@unittest.skipUnless(SSH_KEYGEN, "OpenSSH ssh-keygen is unavailable")
class ExternalVerificationSignatureTest(unittest.TestCase):
    def make_reviewer(self, template: dict, reviewer_id: str) -> dict:
        value = json.loads(json.dumps(template))
        value.update({
            "reviewer_id": reviewer_id,
            "self_attested_human": True,
            "self_attested_independent_bandit_or_formalization_expert": True,
            "viewed_other_review_before_submission": False,
            "evaluation_outcomes_observed": False,
        })
        for case in value["cases"]:
            case["review"].update({
                "faithful_contract": "match",
                "injected_drift": "source_critical_change",
                "source_locator": "exact",
                "source_hash_verified": True,
                "complete_common_target_card": json.loads(json.dumps(
                    case["canonical_frozen_benchmark_card"]
                )),
                "confidence_1_to_3": 3,
                "rationale": "Checked the frozen source and all benchmark fields.",
            })
        return value

    def make_adjudication(
        self, template: dict, reviewer_a_path: Path, reviewer_b_path: Path
    ) -> dict:
        value = json.loads(json.dumps(template))
        value.update({
            "adjudicator_id": "adjudicator-id",
            "self_attested_human": True,
            "self_attested_independent_bandit_or_formalization_expert": True,
            "evaluation_outcomes_observed": False,
            "reviewer_a_sha256": hashlib.sha256(
                reviewer_a_path.read_bytes()
            ).hexdigest(),
            "reviewer_b_sha256": hashlib.sha256(
                reviewer_b_path.read_bytes()
            ).hexdigest(),
        })
        for case in value["cases"]:
            case.update({
                "final_decisions": dict(review_validate.PRODUCTION_DECISIONS),
                "final_common_target_card": json.loads(json.dumps(
                    case["canonical_frozen_benchmark_card"]
                )),
                "source_contract_valid": True,
                "reviewer_disagreement_present": False,
                "reviewer_disagreement_dimensions": [],
                "reviewer_disagreement_resolved": False,
                "adjudication_rationale": "The two source reviews agree.",
            })
        return value

    def generate_key(self, root: Path, name: str) -> Path:
        key = root / name
        process = subprocess.run(
            [SSH_KEYGEN, "-q", "-t", "ed25519", "-N", "", "-f", str(key)],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=False,
        )
        self.assertEqual(process.returncode, 0, process.stdout.decode(errors="replace"))
        return key

    def public_key(self, key: Path) -> str:
        parts = Path(f"{key}.pub").read_text(encoding="ascii").strip().split()
        return f"{parts[0]} {parts[1]}"

    def sign_value(self, root: Path, name: str, key: Path, value: dict) -> Path:
        payload = root / name
        payload.write_bytes(external.canonical_bytes(value))
        process = subprocess.run(
            [
                SSH_KEYGEN, "-Y", "sign", "-f", str(key),
                "-n", self.protocol["signature_namespace"], str(payload),
            ],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=False,
        )
        self.assertEqual(process.returncode, 0, process.stdout.decode(errors="replace"))
        signature = Path(f"{payload}.sig")
        self.assertTrue(signature.is_file())
        return signature

    def fill_registry(self, root: Path, keys: dict[str, Path]) -> tuple[Path, Path, dict]:
        registry = json.loads(json.dumps(self.protocol["role_registry_template"]))
        registry["registered_at_utc"] = utc_text(
            datetime.now(timezone.utc) - timedelta(minutes=2)
        )
        pseudonyms = {
            "reviewer_a": "reviewer-a",
            "reviewer_b": "reviewer-b",
            "adjudicator": "adjudicator-id",
            "external_verifier": "external-verifier-id",
        }
        for item in registry["signers"]:
            slot = item["slot"]
            item["principal"] = f"principal-{slot.replace('_', '-')}"
            item["pseudonymous_id"] = pseudonyms[slot]
            item["qualification_scope"] = f"externally checked scope for {slot}"
            item["public_key"] = self.public_key(keys[slot])
            item["public_key_fingerprint"] = external.public_key_fingerprint(
                item["public_key"]
            )
        allowed = root / "allowed_signers"
        allowed.write_bytes(external.allowed_signers_bytes(
            registry["signers"], self.protocol["signature_namespace"]
        ))
        registry["allowed_signers_sha256"] = external.sha256_file(allowed)
        registry_path = root / "role-registry.json"
        dump(registry_path, registry)
        return registry_path, allowed, registry

    def fill_receipt(self, bundle: dict) -> dict:
        receipt = json.loads(json.dumps(self.protocol["external_receipt_template"]))
        receipt.update({
            "receipt_id": "external-receipt-fixture",
            "verified_at_utc": utc_text(datetime.now(timezone.utc) - timedelta(minutes=1)),
            "protocol_sha256": external.sha256_file(external.DEFAULT_PROTOCOL),
            "role_registry_canonical_sha256": external.sha256_bytes(
                external.canonical_bytes(bundle["registry_value"])
            ),
            "allowed_signers_sha256": external.sha256_file(bundle["allowed_signers"]),
            "review_completion_canonical_sha256": external.sha256_bytes(
                external.canonical_bytes(bundle["completion_value"])
            ),
            "public_escrow_reference": "https://example.invalid/public-attestation-record",
            "public_escrow_receipt_sha256": "a" * 64,
            "private_escrow_reference": "private-escrow:chair-only-fixture-reference",
            "attestation_statement": external.ATTESTATION_STATEMENT,
        })
        by_slot = {item["slot"]: item for item in bundle["registry_value"]["signers"]}
        for slot in ("reviewer_a", "reviewer_b", "adjudicator"):
            signer = by_slot[slot]
            binding = receipt["signed_payloads"][slot]
            binding.update({
                "principal": signer["principal"],
                "pseudonymous_id": signer["pseudonymous_id"],
                "canonical_payload_sha256": external.sha256_bytes(
                    external.canonical_bytes(bundle[f"{slot}_value"])
                ),
                "detached_signature_sha256": external.sha256_file(
                    bundle[f"{slot}_signature"]
                ),
            })
            receipt["attestations"][slot].update({
                "pseudonymous_id": signer["pseudonymous_id"],
                "identity_evidence_checked": True,
                "qualification_evidence_checked": True,
                "independence_checked": True,
                "conflict_of_interest_checked": True,
                "private_evidence_escrowed": True,
            })
        verifier = by_slot["external_verifier"]
        receipt["external_verifier"].update({
            "principal": verifier["principal"],
            "pseudonymous_id": verifier["pseudonymous_id"],
        })
        return receipt

    def make_bundle(self, root: Path) -> dict:
        self.protocol = external.load(external.DEFAULT_PROTOCOL)
        manifest, reviewer_template, adjudication_template = review_prepare.build_packet()
        packet = root / "packet"
        packet.mkdir()
        dump(packet / "packet-manifest.json", manifest)
        dump(packet / "reviewer-template.json", reviewer_template)
        dump(packet / "adjudication-template.json", adjudication_template)

        # This remains an excluded ephemeral fixture, but its construction order
        # still mirrors preregistration: keys and roles exist before review bytes.
        keys = {
            slot: self.generate_key(root, f"key-{slot}")
            for slot in self.protocol["required_signer_slots"]
        }
        registry, allowed, registry_value = self.fill_registry(root, keys)

        reviewer_a_value = self.make_reviewer(reviewer_template, "reviewer-a")
        reviewer_b_value = self.make_reviewer(reviewer_template, "reviewer-b")
        reviewer_a = root / "reviewer-a.json"
        reviewer_b = root / "reviewer-b.json"
        dump(reviewer_a, reviewer_a_value)
        dump(reviewer_b, reviewer_b_value)
        adjudication_value = self.make_adjudication(
            adjudication_template, reviewer_a, reviewer_b
        )
        adjudication = root / "adjudication.json"
        dump(adjudication, adjudication_value)
        completion_value = review_validate.validate(
            packet, reviewer_a, reviewer_b, adjudication
        )
        completion = root / "review-completion.json"
        dump(completion, completion_value)

        bundle = {
            "packet": packet,
            "reviewer_a": reviewer_a,
            "reviewer_b": reviewer_b,
            "adjudication": adjudication,
            "completion": completion,
            "reviewer_a_value": reviewer_a_value,
            "reviewer_b_value": reviewer_b_value,
            "adjudicator_value": adjudication_value,
            "completion_value": completion_value,
            "keys": keys,
            "registry": registry,
            "registry_value": registry_value,
            "allowed_signers": allowed,
        }
        for slot in ("reviewer_a", "reviewer_b", "adjudicator"):
            bundle[f"{slot}_signature"] = self.sign_value(
                root, f"canonical-{slot}.json", keys[slot], bundle[f"{slot}_value"]
            )
        receipt_value = self.fill_receipt(bundle)
        receipt = root / "external-receipt.json"
        dump(receipt, receipt_value)
        verifier_signature = self.sign_value(
            root, "canonical-external-receipt.json", keys["external_verifier"],
            receipt_value,
        )
        bundle.update({
            "receipt": receipt,
            "receipt_value": receipt_value,
            "verifier_signature": verifier_signature,
        })
        return bundle

    def validate_bundle(self, bundle: dict) -> dict:
        return external.validate(
            external.DEFAULT_PROTOCOL, bundle["packet"],
            bundle["reviewer_a"], bundle["reviewer_a_signature"],
            bundle["reviewer_b"], bundle["reviewer_b_signature"],
            bundle["adjudication"], bundle["adjudicator_signature"],
            bundle["completion"], bundle["registry"], bundle["allowed_signers"],
            bundle["receipt"], bundle["verifier_signature"],
        )

    def resign_receipt(self, root: Path, bundle: dict) -> None:
        dump(bundle["receipt"], bundle["receipt_value"])
        bundle["verifier_signature"] = self.sign_value(
            root, f"canonical-receipt-{len(list(root.iterdir()))}.json",
            bundle["keys"]["external_verifier"], bundle["receipt_value"],
        )

    def test_ephemeral_ed25519_positive_path_is_conservatively_scoped(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            result = self.validate_bundle(self.make_bundle(Path(directory)))
        self.assertEqual(result["status"], external.COMPLETED_STATUS)
        self.assertTrue(result["signed_key_possession_and_payload_integrity_complete"])
        self.assertTrue(
            result["external_identity_qualification_independence_coi_attestation_complete"]
        )
        self.assertFalse(result["cryptographically_proven_human"])
        self.assertFalse(result["pre_outcome_timing_cryptographically_proven"])
        self.assertFalse(result["production_execution_eligible"])
        self.assertFalse(result["production_execution_eligible_from_this_layer_alone"])
        self.assertFalse(result["production_trust_anchor_verified"])

    def test_tampered_receipt_fails_signature_verification(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            bundle = self.make_bundle(Path(directory))
            bundle["receipt_value"]["public_escrow_reference"] = (
                "https://example.invalid/tampered-public-record"
            )
            dump(bundle["receipt"], bundle["receipt_value"])
            with self.assertRaises(external.ExternalVerificationError):
                self.validate_bundle(bundle)

    def test_wrong_reviewer_signing_key_fails(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            bundle = self.make_bundle(root)
            wrong_signature = self.sign_value(
                root, "wrong-reviewer-a-payload.json",
                bundle["keys"]["reviewer_b"], bundle["reviewer_a_value"],
            )
            bundle["reviewer_a_signature"] = wrong_signature
            bundle["receipt_value"]["signed_payloads"]["reviewer_a"][
                "detached_signature_sha256"
            ] = external.sha256_file(wrong_signature)
            self.resign_receipt(root, bundle)
            with self.assertRaises(external.ExternalVerificationError):
                self.validate_bundle(bundle)

    def test_wrong_external_verifier_signing_key_fails(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            bundle = self.make_bundle(root)
            bundle["verifier_signature"] = self.sign_value(
                root, "wrong-external-receipt-payload.json",
                bundle["keys"]["adjudicator"], bundle["receipt_value"],
            )
            with self.assertRaises(external.ExternalVerificationError):
                self.validate_bundle(bundle)

    def test_reused_pseudonymous_identity_fails_registry_validation(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            bundle = self.make_bundle(Path(directory))
            bundle["registry_value"]["signers"][1]["pseudonymous_id"] = "reviewer-a"
            dump(bundle["registry"], bundle["registry_value"])
            with self.assertRaises(external.ExternalVerificationError):
                self.validate_bundle(bundle)

    def test_noncanonical_padding_alias_of_existing_key_fails_registry_validation(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            bundle = self.make_bundle(Path(directory))
            first = bundle["registry_value"]["signers"][0]
            second = bundle["registry_value"]["signers"][1]
            second["public_key"] = first["public_key"] + "="
            second["public_key_fingerprint"] = first["public_key_fingerprint"]
            dump(bundle["registry"], bundle["registry_value"])
            with self.assertRaises(external.ExternalVerificationError):
                self.validate_bundle(bundle)

    def test_post_outcome_receipt_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            bundle = self.make_bundle(Path(directory))
            bundle["receipt_value"]["evaluation_outcomes_observed"] = True
            dump(bundle["receipt"], bundle["receipt_value"])
            with self.assertRaises(external.ExternalVerificationError):
                self.validate_bundle(bundle)

    def test_unsigned_external_receipt_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            bundle = self.make_bundle(root)
            bundle["verifier_signature"] = root / "missing-external-receipt.sig"
            with self.assertRaises(external.ExternalVerificationError):
                self.validate_bundle(bundle)


if __name__ == "__main__":
    unittest.main()
