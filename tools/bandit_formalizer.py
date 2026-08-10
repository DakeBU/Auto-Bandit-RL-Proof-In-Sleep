#!/usr/bin/env python3
"""Ground candidate LaTeX-to-Lean translations in BanditRLlib.

The adapter is deliberately provider-independent.  It retrieves compiled local
declarations and Mathlib/LML cards before calling an optional server-side JSON
provider.  Provider output is always labelled as a candidate: compilation and
semantic review are separate gates.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import urllib.error
import urllib.request
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any, Protocol


ROOT = Path(__file__).resolve().parents[1]
DECLARATION_INDEX = ROOT / "research-wiki" / "retrieval-index" / "local_lean_declarations.json"
MATHLIB_CARDS = ROOT / "research-wiki" / "mathlib" / "theorem-cards.md"
LML_CARDS = ROOT / "research-wiki" / "lml" / "theorem-cards.md"
MAX_INPUT_CHARS = 50_000
MAX_PROVIDER_TEXT_CHARS = 200_000
MAX_CANDIDATES = 8
FORBIDDEN_CANDIDATE_SOURCE = re.compile(
    r"(?m)(?:\b(?:sorry|admit|axiom|unsafe|initialize|run_cmd)\b|"
    r"^\s*#(?:eval|reduce|print\s+axioms)\b|@\[\s*extern\b)"
)


class FormalizationError(ValueError):
    """A request or provider response violates the formalizer contract."""


class ProviderUnavailableError(RuntimeError):
    """No server-side model provider is configured for this local session."""


@dataclass(frozen=True)
class FormalizationRequest:
    latex: str
    natural_language: str = ""
    theorem_kind: str = "theorem"
    preferred_domain: str = ""
    preferred_module: str = ""

    @classmethod
    def from_payload(cls, payload: Any) -> "FormalizationRequest":
        if not isinstance(payload, dict):
            raise FormalizationError("The formalization request must be a JSON object.")
        values: dict[str, str] = {}
        for field_name in (
            "latex",
            "natural_language",
            "theorem_kind",
            "preferred_domain",
            "preferred_module",
        ):
            value = payload.get(field_name, "")
            if not isinstance(value, str):
                raise FormalizationError(f"`{field_name}` must be a string.")
            values[field_name] = value.strip()
        if not values["latex"] and not values["natural_language"]:
            raise FormalizationError("Provide LaTeX, a natural-language statement, or both.")
        total = sum(len(value) for value in values.values())
        if total > MAX_INPUT_CHARS:
            raise FormalizationError(f"Formalization input exceeds {MAX_INPUT_CHARS} characters.")
        theorem_kind = values["theorem_kind"] or "theorem"
        if theorem_kind not in {"definition", "lemma", "theorem", "proposition", "corollary"}:
            raise FormalizationError("`theorem_kind` is not a supported declaration kind.")
        values["theorem_kind"] = theorem_kind
        return cls(**values)


@dataclass
class FormalizationResult:
    interpretation: str = ""
    lean_statement: str = ""
    lean_source: str = ""
    assumptions: list[str] = field(default_factory=list)
    imports: list[str] = field(default_factory=list)
    banditrl_candidates: list[dict[str, str]] = field(default_factory=list)
    mathlib_candidates: list[dict[str, str]] = field(default_factory=list)
    lml_candidates: list[dict[str, str]] = field(default_factory=list)
    unresolved_obligations: list[str] = field(default_factory=list)
    translation_status: str = "candidate"
    lean_status: str = "not_checked"
    proof_status: str = "unproved"
    library_status: str = "proposed"
    provider_status: str = "unavailable"
    provider_name: str = "none"

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


class FormalizationProvider(Protocol):
    name: str

    def generate(self, request: FormalizationRequest, context: dict[str, Any]) -> dict[str, Any]: ...


def _tokens(text: str) -> set[str]:
    normalized = re.sub(r"[^A-Za-z0-9]+", " ", text).lower()
    tokens = {token for token in normalized.split() if len(token) >= 3}
    aliases = {
        "regret": {"pseudoregret", "gap", "pullcount"},
        "ucb": {"confidence", "optimism"},
        "exp3": {"adversarial", "importance", "weighted"},
        "reinforcement": {"mdp", "bellman", "occupancy"},
        "latex": {"statement"},
    }
    for token in tuple(tokens):
        tokens.update(aliases.get(token, set()))
    return tokens


def _rank(query: set[str], text: str) -> int:
    haystack = _tokens(text)
    return 4 * len(query & haystack) + sum(1 for token in query if token in text.lower())


def retrieve_banditrl(request: FormalizationRequest, limit: int = MAX_CANDIDATES) -> list[dict[str, str]]:
    payload = json.loads(DECLARATION_INDEX.read_text(encoding="utf-8"))
    declarations = payload.get("declarations", [])
    query = _tokens(
        " ".join(
            (
                request.latex,
                request.natural_language,
                request.preferred_domain,
                request.preferred_module,
            )
        )
    )
    ranked: list[tuple[int, dict[str, Any]]] = []
    for declaration in declarations:
        text = " ".join(
            str(declaration.get(key, ""))
            for key in ("full_name", "name", "statement", "file", "kind")
        )
        score = _rank(query, text)
        if score:
            ranked.append((score, declaration))
    ranked.sort(key=lambda item: (-item[0], item[1].get("full_name", "")))
    return [
        {
            "name": str(declaration.get("full_name", "")),
            "statement": str(declaration.get("statement", "")),
            "file": str(declaration.get("file", "")),
            "status": "compiled-local-declaration",
        }
        for _, declaration in ranked[:limit]
    ]


def _retrieve_markdown_cards(path: Path, request: FormalizationRequest, limit: int = 5) -> list[dict[str, str]]:
    query = _tokens(" ".join((request.latex, request.natural_language, request.preferred_domain)))
    rows: list[tuple[int, dict[str, str]]] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.startswith("|") or line.startswith("| ---"):
            continue
        cells = [cell.strip().strip("`") for cell in line.strip("|").split("|")]
        if not cells or cells[0].lower() in {"card", "card id"}:
            continue
        score = _rank(query, " ".join(cells))
        if score:
            rows.append(
                (
                    score,
                    {
                        "card": cells[0],
                        "detail": " · ".join(cells[1:3]),
                        "status": "retrieval-card-only",
                    },
                )
            )
    rows.sort(key=lambda item: (-item[0], item[1]["card"]))
    return [row for _, row in rows[:limit]]


def build_grounding_context(request: FormalizationRequest) -> dict[str, Any]:
    return {
        "request": asdict(request),
        "banditrl_candidates": retrieve_banditrl(request),
        "mathlib_candidates": _retrieve_markdown_cards(MATHLIB_CARDS, request),
        "lml_candidates": _retrieve_markdown_cards(LML_CARDS, request),
        "verification_boundary": {
            "translation": "candidate until semantic review",
            "lean": "not checked until the pinned compiler accepts the exact source",
            "library": "proposed until maintainer review, full gate, and merge",
        },
    }


class JsonHTTPProvider:
    """Thin adapter for any server exposing the ABRL JSON provider contract."""

    name = "json-http"

    def __init__(self, endpoint: str, api_key: str = "", timeout: int = 90) -> None:
        self.endpoint = endpoint
        self.api_key = api_key
        self.timeout = timeout

    def generate(self, request: FormalizationRequest, context: dict[str, Any]) -> dict[str, Any]:
        body = json.dumps(
            {
                "task": "candidate_banditrl_formalization",
                "request": asdict(request),
                "grounding": context,
                "required_output": [
                    "interpretation",
                    "lean_statement",
                    "lean_source",
                    "assumptions",
                    "imports",
                    "unresolved_obligations",
                ],
            }
        ).encode("utf-8")
        headers = {"Content-Type": "application/json", "Accept": "application/json"}
        if self.api_key:
            headers["Authorization"] = f"Bearer {self.api_key}"
        request_object = urllib.request.Request(self.endpoint, data=body, headers=headers, method="POST")
        try:
            with urllib.request.urlopen(request_object, timeout=self.timeout) as response:
                payload = json.loads(response.read().decode("utf-8"))
        except (OSError, urllib.error.URLError, json.JSONDecodeError) as error:
            raise ProviderUnavailableError(f"The configured formalization provider failed: {error}") from error
        if not isinstance(payload, dict):
            raise FormalizationError("The provider response must be a JSON object.")
        result = payload.get("result", payload)
        if not isinstance(result, dict):
            raise FormalizationError("The provider `result` must be a JSON object.")
        return result


class MockProvider:
    """Deterministic provider for tests; never selected without explicit configuration."""

    name = "deterministic-mock"

    def generate(self, request: FormalizationRequest, context: dict[str, Any]) -> dict[str, Any]:
        return {
            "interpretation": request.natural_language or "A candidate reflexive natural-number lemma.",
            "lean_statement": "theorem banditRLlib_candidate (n : Nat) : n = n",
            "lean_source": (
                "import BanditRLProof\n\n"
                "-- Candidate translation generated by the deterministic test provider.\n"
                "theorem banditRLlib_candidate (n : Nat) : n = n := by\n"
                "  rfl\n"
            ),
            "assumptions": ["n is a natural number"],
            "imports": ["BanditRLProof"],
            "unresolved_obligations": ["Human semantic review against the mathematical input"],
        }


def provider_from_env() -> FormalizationProvider:
    provider_name = os.environ.get("ABRL_FORMALIZER_PROVIDER", "").strip().lower()
    if provider_name == "mock":
        return MockProvider()
    endpoint = os.environ.get("ABRL_FORMALIZER_ENDPOINT", "").strip()
    if provider_name in {"http", "json-http"} or endpoint:
        if not endpoint:
            raise ProviderUnavailableError("ABRL_FORMALIZER_ENDPOINT is not configured.")
        return JsonHTTPProvider(
            endpoint,
            os.environ.get("ABRL_FORMALIZER_API_KEY", ""),
            int(os.environ.get("ABRL_FORMALIZER_TIMEOUT", "90")),
        )
    raise ProviderUnavailableError("AI formalizer unavailable in this local session.")


def _string_list(value: Any, field_name: str) -> list[str]:
    if value is None:
        return []
    if not isinstance(value, list) or not all(isinstance(item, str) for item in value):
        raise FormalizationError(f"Provider field `{field_name}` must be a list of strings.")
    cleaned = [item.strip() for item in value if item.strip()]
    if sum(len(item) for item in cleaned) > MAX_PROVIDER_TEXT_CHARS:
        raise FormalizationError(f"Provider field `{field_name}` is too large.")
    return cleaned


def formalize(
    request: FormalizationRequest,
    provider: FormalizationProvider | None = None,
) -> FormalizationResult:
    context = build_grounding_context(request)
    result = FormalizationResult(
        banditrl_candidates=context["banditrl_candidates"],
        mathlib_candidates=context["mathlib_candidates"],
        lml_candidates=context["lml_candidates"],
    )
    if provider is None:
        try:
            provider = provider_from_env()
        except ProviderUnavailableError as error:
            result.interpretation = request.natural_language
            result.unresolved_obligations = [str(error)]
            return result
    payload = provider.generate(request, context)
    for field_name in ("interpretation", "lean_statement", "lean_source"):
        value = payload.get(field_name, "")
        if not isinstance(value, str):
            raise FormalizationError(f"Provider field `{field_name}` must be a string.")
        if len(value) > MAX_PROVIDER_TEXT_CHARS:
            raise FormalizationError(f"Provider field `{field_name}` is too large.")
        setattr(result, field_name, value.strip())
    if FORBIDDEN_CANDIDATE_SOURCE.search(result.lean_source):
        raise FormalizationError(
            "Candidate Lean source contains a forbidden placeholder or execution command."
        )
    result.assumptions = _string_list(payload.get("assumptions"), "assumptions")
    result.imports = _string_list(payload.get("imports"), "imports")
    result.unresolved_obligations = _string_list(
        payload.get("unresolved_obligations"), "unresolved_obligations"
    )
    if "Human semantic review against the mathematical input" not in result.unresolved_obligations:
        result.unresolved_obligations.append("Human semantic review against the mathematical input")
    result.provider_status = "candidate-generated"
    result.provider_name = provider.name
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--latex", default="")
    parser.add_argument("--natural-language", default="")
    parser.add_argument("--domain", default="")
    parser.add_argument("--module", default="")
    parser.add_argument("--mock", action="store_true", help="use the deterministic test provider")
    args = parser.parse_args()
    request = FormalizationRequest.from_payload(
        {
            "latex": args.latex,
            "natural_language": args.natural_language,
            "preferred_domain": args.domain,
            "preferred_module": args.module,
        }
    )
    provider = MockProvider() if args.mock else None
    print(json.dumps(formalize(request, provider).to_dict(), ensure_ascii=False, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
