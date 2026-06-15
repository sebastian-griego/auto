from autoform_eval.artifact_names import artifact_component, artifact_stem


def test_artifact_component_preserves_safe_values():
    assert artifact_component("unit_001") == "unit_001"
    assert artifact_component("gpt-4.1-mini") == "gpt-4.1-mini"


def test_artifact_component_normalizes_unsafe_values_with_hash_suffix():
    normalized = artifact_component("../bad model:name")

    assert normalized.startswith("bad_model_name-")
    assert "/" not in normalized
    assert "\\" not in normalized
    assert ":" not in normalized
    assert normalized != artifact_component("../bad model_name")


def test_artifact_stem_normalizes_each_component():
    stem = artifact_stem("../item", "openai/v1", "model:name", "k1")

    assert stem.count(".") == 3
    assert "/" not in stem
    assert "\\" not in stem
    assert ":" not in stem
