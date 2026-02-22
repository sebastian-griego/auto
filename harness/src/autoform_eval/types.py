from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Literal


Bucket = Literal[
    "provider_error",
    "output_parse_reject",
    "lean_parse_fail",
    "elab_fail",
    "shape_fail",
    "semantic_fail",
    "timeout",
    "pass",
]


@dataclass(slots=True)
class SemanticSpec:
    kind: str
    check: str
    extra: str | None = None


@dataclass(slots=True)
class ProvenanceSpec:
    source_kind: str
    source_ref: str
    license: str
    notes: str | None = None


@dataclass(slots=True)
class DatasetItem:
    schema_version: str
    checker_version: str
    id: str
    nl: str
    imports: list[str]
    context: str
    expected: str
    family: str
    tier: Literal["A", "B"]
    split: Literal["pilot", "dev", "test"]
    tags: list[str]
    semantic: SemanticSpec
    provenance: ProvenanceSpec
    forbidden_ok: list[str]


@dataclass(slots=True)
class ParseResult:
    accepted: bool
    candidate: str
    reason: str | None = None


@dataclass(slots=True)
class LeanRunResult:
    ok: bool
    timed_out: bool
    returncode: int
    elapsed_ms: int
    stdout: str
    stderr: str


@dataclass(slots=True)
class AttemptResult:
    bucket: Bucket
    test1_pass: bool
    test2_pass: bool
    shape_pass: bool | None
    test1_elapsed_ms: int
    test2_elapsed_ms: int
    stdout_excerpt: str
    stderr_excerpt: str


def excerpt(text: str, limit: int = 600) -> str:
    if len(text) <= limit:
        return text
    return f"{text[: limit - 3]}..."


def to_jsonable(value: Any) -> Any:
    if hasattr(value, "__dict__"):
        return dict(value.__dict__)
    return value
