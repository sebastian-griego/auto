from __future__ import annotations

from dataclasses import dataclass
import re


LEADING_FORALL_RE = re.compile(r"^\s*(?:\u2200|forall)\s+([^:]+?)\s*:\s*([^,]+?)\s*,\s*(.*)$", re.DOTALL)

_FORBIDDEN_IDENT_CODES = {
    "abs": "forbidden_keyword:abs",
    "by": "forbidden_keyword:by",
    "def": "forbidden_keyword:def",
    "example": "forbidden_keyword:example",
    "fun": "lambda",
    "if": "forbidden_keyword:if",
    "lambda": "lambda",
    "lemma": "forbidden_keyword:lemma",
    "let": "forbidden_keyword:let",
    "max": "forbidden_keyword:max",
    "min": "forbidden_keyword:min",
    "namespace": "forbidden_keyword:namespace",
    "section": "forbidden_keyword:section",
    "sorry": "forbidden_keyword:sorry",
    "theorem": "forbidden_keyword:theorem",
}


class LinearInequalityParseError(ValueError):
    def __init__(self, code: str) -> None:
        super().__init__(code)
        self.code = code


@dataclass(slots=True, frozen=True)
class LinearInequalitySpec:
    binders: tuple[tuple[str, str], ...]
    relation: str
    coeffs: tuple[int, ...]
    const: int


@dataclass(slots=True, frozen=True)
class _Token:
    kind: str
    value: str


@dataclass(slots=True, frozen=True)
class _AffineExpr:
    coeffs: tuple[int, ...]
    const: int
    literal: int | None


def _strip_outer_parentheses(text: str) -> str:
    out = text.strip()
    while out.startswith("(") and out.endswith(")"):
        depth = 0
        wraps_whole = True
        for idx, ch in enumerate(out):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth < 0:
                    wraps_whole = False
                    break
                if depth == 0 and idx != len(out) - 1:
                    wraps_whole = False
                    break
        if depth != 0 or not wraps_whole:
            break
        out = out[1:-1].strip()
    return out


def _extract_binders(expr: str) -> tuple[list[tuple[str, str]], str]:
    binders: list[tuple[str, str]] = []
    rest = expr.strip()
    while True:
        match = LEADING_FORALL_RE.match(rest)
        if not match:
            break
        vars_part = match.group(1).strip()
        ty_part = _strip_outer_parentheses(match.group(2).strip())
        rest = match.group(3).strip()
        if ty_part not in {"Nat", "Int"}:
            raise LinearInequalityParseError(f"unsupported_binder_type:{ty_part}")
        var_names = [name for name in vars_part.split() if name]
        if not var_names:
            raise LinearInequalityParseError("binder_parse")
        for name in var_names:
            binders.append((name, ty_part))
    return binders, rest


def _tokenize(text: str) -> list[_Token]:
    tokens: list[_Token] = []
    idx = 0
    while idx < len(text):
        ch = text[idx]
        if ch.isspace():
            idx += 1
            continue
        if text.startswith("<=", idx):
            tokens.append(_Token("LE", "<="))
            idx += 2
            continue
        if ch == "≤":
            tokens.append(_Token("LE", "<="))
            idx += 1
            continue
        if ch == "<":
            tokens.append(_Token("LT", "<"))
            idx += 1
            continue
        if ch == "+":
            tokens.append(_Token("PLUS", ch))
            idx += 1
            continue
        if ch == "*":
            tokens.append(_Token("STAR", ch))
            idx += 1
            continue
        if ch == "(":
            tokens.append(_Token("LPAREN", ch))
            idx += 1
            continue
        if ch == ")":
            tokens.append(_Token("RPAREN", ch))
            idx += 1
            continue
        if ch == "-":
            raise LinearInequalityParseError("neg")
        if ch == "/":
            raise LinearInequalityParseError("div")
        if ch == "λ":
            raise LinearInequalityParseError("lambda")
        if ch.isdigit():
            end = idx + 1
            while end < len(text) and text[end].isdigit():
                end += 1
            tokens.append(_Token("NUM", text[idx:end]))
            idx = end
            continue
        if ch.isalpha() or ch == "_":
            end = idx + 1
            while end < len(text) and (text[end].isalnum() or text[end] in {"_", "'"}):
                end += 1
            ident = text[idx:end]
            code = _FORBIDDEN_IDENT_CODES.get(ident)
            if code is not None:
                raise LinearInequalityParseError(code)
            tokens.append(_Token("IDENT", ident))
            idx = end
            continue
        raise LinearInequalityParseError(f"unexpected_char:{ch}")
    tokens.append(_Token("EOF", ""))
    return tokens


def _zero_affine(arity: int) -> _AffineExpr:
    return _AffineExpr(coeffs=tuple(0 for _ in range(arity)), const=0, literal=None)


def _const_affine(arity: int, value: int, *, literal: int | None) -> _AffineExpr:
    return _AffineExpr(coeffs=tuple(0 for _ in range(arity)), const=value, literal=literal)


def _var_affine(arity: int, idx: int) -> _AffineExpr:
    coeffs = [0] * arity
    coeffs[idx] = 1
    return _AffineExpr(coeffs=tuple(coeffs), const=0, literal=None)


def _add_affine(lhs: _AffineExpr, rhs: _AffineExpr) -> _AffineExpr:
    return _AffineExpr(
        coeffs=tuple(a + b for a, b in zip(lhs.coeffs, rhs.coeffs, strict=True)),
        const=lhs.const + rhs.const,
        literal=None,
    )


def _scale_affine(scale: int, expr: _AffineExpr) -> _AffineExpr:
    return _AffineExpr(
        coeffs=tuple(scale * coeff for coeff in expr.coeffs),
        const=scale * expr.const,
        literal=None,
    )


class _Parser:
    def __init__(self, tokens: list[_Token], binder_index: dict[str, int]) -> None:
        self.tokens = tokens
        self.binder_index = binder_index
        self.pos = 0
        self.arity = len(binder_index)

    def _peek(self) -> _Token:
        return self.tokens[self.pos]

    def _advance(self) -> _Token:
        token = self.tokens[self.pos]
        self.pos += 1
        return token

    def _expect(self, kind: str) -> _Token:
        token = self._peek()
        if token.kind != kind:
            raise LinearInequalityParseError(f"unexpected_token:{token.value or token.kind}")
        return self._advance()

    def parse(self) -> tuple[str, _AffineExpr]:
        lhs = self._parse_sum()
        rel_token = self._peek()
        if rel_token.kind not in {"LT", "LE"}:
            raise LinearInequalityParseError("expected_relation")
        relation = "<" if rel_token.kind == "LT" else "<="
        self._advance()
        rhs = self._parse_sum()
        if self._peek().kind != "EOF":
            raise LinearInequalityParseError(f"trailing_tokens:{self._peek().value}")
        coeffs = tuple(a - b for a, b in zip(lhs.coeffs, rhs.coeffs, strict=True))
        const = lhs.const - rhs.const
        return relation, _AffineExpr(coeffs=coeffs, const=const, literal=None)

    def _parse_sum(self) -> _AffineExpr:
        expr = self._parse_product()
        while self._peek().kind == "PLUS":
            self._advance()
            expr = _add_affine(expr, self._parse_product())
        return expr

    def _parse_product(self) -> _AffineExpr:
        expr = self._parse_atom()
        while self._peek().kind == "STAR":
            self._advance()
            rhs = self._parse_atom()
            if expr.literal is not None:
                expr = _scale_affine(expr.literal, rhs)
            elif rhs.literal is not None:
                expr = _scale_affine(rhs.literal, expr)
            else:
                raise LinearInequalityParseError("nonlinear_mul")
        return expr

    def _parse_atom(self) -> _AffineExpr:
        token = self._peek()
        if token.kind == "NUM":
            self._advance()
            value = int(token.value)
            return _const_affine(self.arity, value, literal=value)
        if token.kind == "IDENT":
            self._advance()
            idx = self.binder_index.get(token.value)
            if idx is None:
                raise LinearInequalityParseError(f"unknown_variable:{token.value}")
            return _var_affine(self.arity, idx)
        if token.kind == "LPAREN":
            self._advance()
            inner = self._parse_sum()
            if self._peek().kind != "RPAREN":
                raise LinearInequalityParseError("unclosed_paren")
            self._advance()
            return inner
        if token.kind == "RPAREN":
            raise LinearInequalityParseError("unexpected_token:)")
        if token.kind == "EOF":
            raise LinearInequalityParseError("unexpected_eof")
        raise LinearInequalityParseError(f"unexpected_token:{token.value or token.kind}")


def parse_linear_inequality(expr: str) -> LinearInequalitySpec:
    binders, body = _extract_binders(expr)
    binder_index = {name: idx for idx, (name, _) in enumerate(binders)}
    tokens = _tokenize(body)
    relation, affine = _Parser(tokens, binder_index).parse()
    return LinearInequalitySpec(
        binders=tuple(binders),
        relation=relation,
        coeffs=affine.coeffs,
        const=affine.const,
    )


def render_linear_inequality(spec: LinearInequalitySpec) -> str:
    lhs_terms: list[str] = []
    rhs_terms: list[str] = []
    for (name, _), coeff in zip(spec.binders, spec.coeffs, strict=True):
        if coeff > 0:
            lhs_terms.append(name if coeff == 1 else f"{coeff} * {name}")
        elif coeff < 0:
            mag = -coeff
            rhs_terms.append(name if mag == 1 else f"{mag} * {name}")
    if spec.const > 0:
        lhs_terms.append(str(spec.const))
    elif spec.const < 0:
        rhs_terms.append(str(-spec.const))
    lhs = " + ".join(lhs_terms) if lhs_terms else "0"
    rhs = " + ".join(rhs_terms) if rhs_terms else "0"
    prefix = " ".join(f"∀ {name} : {ty}," for name, ty in spec.binders)
    body = f"{lhs} {spec.relation} {rhs}"
    return f"{prefix} {body}".strip() if prefix else body
