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

FENCE_RE = re.compile(r"```(?:[a-zA-Z0-9_+-]+)?\s*(.*?)```", re.DOTALL)


def strip_markdown_fences(text: str) -> ParseResult:
    matches = FENCE_RE.findall(text)
    if len(matches) > 1:
        return ParseResult(False, "", "multiple_code_blocks")
    if len(matches) == 1:
        return ParseResult(True, matches[0].strip(), None)
    return ParseResult(True, text.strip(), None)


def _append_comment_space(out: list[str]) -> None:
    if out and not out[-1].isspace():
        out.append(" ")


def _strip_comments_with_status(text: str) -> tuple[str, bool]:
    out: list[str] = []
    i = 0
    block_depth = 0
    while i < len(text):
        if block_depth > 0:
            if text.startswith("/-", i):
                block_depth += 1
                i += 2
                continue
            if text.startswith("-/", i):
                block_depth -= 1
                i += 2
                if block_depth == 0:
                    _append_comment_space(out)
                continue
            if text[i] == "\n" and (not out or out[-1] != "\n"):
                out.append("\n")
            i += 1
            continue

        if text.startswith("/-", i):
            _append_comment_space(out)
            block_depth = 1
            i += 2
            continue

        if text.startswith("--", i):
            _append_comment_space(out)
            i += 2
            while i < len(text) and text[i] != "\n":
                i += 1
            if i < len(text) and text[i] == "\n":
                out.append("\n")
                i += 1
            continue

        out.append(text[i])
        i += 1

    return "".join(out), block_depth == 0


def strip_comments(text: str) -> str:
    stripped, _terminated = _strip_comments_with_status(text)
    return stripped


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

    no_comments, comments_terminated = _strip_comments_with_status(fenced.candidate)
    if not comments_terminated:
        return ParseResult(False, no_comments.strip(), "unterminated_block_comment")
    candidate = unwrap_inline_code(no_comments)
    if not candidate:
        return ParseResult(False, "", "empty_candidate")

    bad = has_forbidden_tokens(candidate, forbidden_ok=forbidden_ok, strict_reject_assign=strict_reject_assign)
    if bad:
        return ParseResult(False, candidate, f"forbidden_token:{bad}")

    return ParseResult(True, candidate, None)
