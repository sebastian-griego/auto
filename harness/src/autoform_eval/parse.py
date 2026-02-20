from __future__ import annotations

import re

from .types import ParseResult


FORBIDDEN_KEYWORDS = (
    "theorem",
    "lemma",
    "def",
    "example",
    "namespace",
    "section",
    "by",
    "sorry",
)

BLOCK_COMMENT_RE = re.compile(r"/-.*?-/", re.DOTALL)
LINE_COMMENT_RE = re.compile(r"--.*$", re.MULTILINE)
FENCE_RE = re.compile(r"```(?:[a-zA-Z0-9_+-]+)?\s*(.*?)```", re.DOTALL)


def strip_markdown_fences(text: str) -> ParseResult:
    matches = FENCE_RE.findall(text)
    if len(matches) > 1:
        return ParseResult(False, "", "multiple_code_blocks")
    if len(matches) == 1:
        return ParseResult(True, matches[0].strip(), None)
    return ParseResult(True, text.strip(), None)


def strip_comments(text: str) -> str:
    prev = text
    while True:
        nxt = BLOCK_COMMENT_RE.sub("", prev)
        if nxt == prev:
            break
        prev = nxt
    return LINE_COMMENT_RE.sub("", prev)


def unwrap_inline_code(text: str) -> str:
    candidate = text.strip()
    for delimiter in ("``", "`"):
        if not (candidate.startswith(delimiter) and candidate.endswith(delimiter)):
            continue
        if len(candidate) <= len(delimiter) * 2:
            continue
        inner = candidate[len(delimiter) : -len(delimiter)]
        # Only unwrap if the body is a single inline span rather than mixed content.
        if delimiter in inner:
            continue
        unwrapped = inner.strip()
        if unwrapped:
            return unwrapped
    return candidate


def has_forbidden_tokens(text: str, forbidden_ok: set[str] | None = None, strict_reject_assign: bool = False) -> str | None:
    forbidden_ok = forbidden_ok or set()
    scan = text
    for keyword in FORBIDDEN_KEYWORDS:
        if keyword in forbidden_ok:
            continue
        if re.search(rf"\b{re.escape(keyword)}\b", scan):
            return keyword
    if strict_reject_assign and ":=" not in forbidden_ok and ":=" in scan:
        return ":="
    return None


def parse_candidate(raw_text: str, forbidden_ok: set[str] | None = None, strict_reject_assign: bool = False) -> ParseResult:
    fenced = strip_markdown_fences(raw_text)
    if not fenced.accepted:
        return fenced

    no_comments = strip_comments(fenced.candidate)
    candidate = unwrap_inline_code(no_comments)
    if not candidate:
        return ParseResult(False, "", "empty_candidate")

    bad = has_forbidden_tokens(candidate, forbidden_ok=forbidden_ok, strict_reject_assign=strict_reject_assign)
    if bad:
        return ParseResult(False, candidate, f"forbidden_token:{bad}")

    return ParseResult(True, candidate, None)
