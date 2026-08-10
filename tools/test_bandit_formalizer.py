"""Deterministic tests for the BanditRLlib formalization adapter."""

from __future__ import annotations

import os
import sys
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import bandit_formalizer as formalizer


class BanditFormalizerTests(unittest.TestCase):
    def request(self) -> formalizer.FormalizationRequest:
        return formalizer.FormalizationRequest.from_payload(
            {
                "latex": r"R_T = \sum_a \Delta_a N_a(T)",
                "natural_language": "Regret is the sum of arm gaps times pull counts.",
                "preferred_domain": "finite stochastic bandits",
            }
        )

    def test_empty_request_is_rejected(self) -> None:
        with self.assertRaises(formalizer.FormalizationError):
            formalizer.FormalizationRequest.from_payload({"latex": "", "natural_language": ""})

    def test_retrieval_grounds_in_local_and_external_cards(self) -> None:
        context = formalizer.build_grounding_context(self.request())
        self.assertTrue(context["banditrl_candidates"])
        self.assertTrue(any("regret" in item["name"].lower() for item in context["banditrl_candidates"]))
        self.assertTrue(context["mathlib_candidates"])
        self.assertTrue(context["lml_candidates"])
        self.assertTrue(all(item["status"] == "compiled-local-declaration" for item in context["banditrl_candidates"]))

    def test_unavailable_provider_never_claims_translation_or_proof(self) -> None:
        with patch.dict(os.environ, {}, clear=True):
            result = formalizer.formalize(self.request())
        self.assertEqual(result.provider_status, "unavailable")
        self.assertEqual(result.translation_status, "candidate")
        self.assertEqual(result.lean_status, "not_checked")
        self.assertEqual(result.proof_status, "unproved")
        self.assertEqual(result.library_status, "proposed")
        self.assertFalse(result.lean_source)

    def test_mock_provider_returns_candidate_not_verified(self) -> None:
        result = formalizer.formalize(self.request(), formalizer.MockProvider())
        self.assertIn("theorem banditRLlib_candidate", result.lean_source)
        self.assertEqual(result.provider_status, "candidate-generated")
        self.assertEqual(result.translation_status, "candidate")
        self.assertEqual(result.lean_status, "not_checked")
        self.assertNotEqual(result.library_status, "integrated")
        self.assertTrue(any("semantic review" in item.lower() for item in result.unresolved_obligations))

    def test_provider_response_schema_is_checked(self) -> None:
        class BadProvider:
            name = "bad"

            def generate(self, request, context):
                return {"lean_source": 7}

        with self.assertRaises(formalizer.FormalizationError):
            formalizer.formalize(self.request(), BadProvider())

    def test_provider_cannot_return_placeholder_or_execution_command(self) -> None:
        class UnsafeProvider:
            name = "unsafe"

            def generate(self, request, context):
                return {"lean_source": "import BanditRLProof\n#eval IO.println \"unexpected\""}

        with self.assertRaises(formalizer.FormalizationError):
            formalizer.formalize(self.request(), UnsafeProvider())


if __name__ == "__main__":
    unittest.main()
