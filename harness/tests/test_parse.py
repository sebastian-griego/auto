from autoform_eval.parse import parse_candidate, strip_comments


def test_parse_candidate_strips_nested_lean_block_comments():
    raw = """```lean
/- outer comment
  /- nested comment with theorem bogus : False -/
  still comment
-/
forall n : Nat, n = n
```"""

    parsed = parse_candidate(raw)

    assert parsed.accepted
    assert parsed.candidate == "forall n : Nat, n = n"


def test_parse_candidate_rejects_unterminated_block_comment():
    parsed = parse_candidate("/- comment starts\nforall n : Nat, n = n")

    assert not parsed.accepted
    assert parsed.reason == "unterminated_block_comment"


def test_strip_comments_treats_comments_as_whitespace():
    assert strip_comments("foo/- comment -/bar -- tail\nbaz").split() == ["foo", "bar", "baz"]
