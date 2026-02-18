from __future__ import annotations

import os
from typing import Any


def _extract_gemini_text(response: Any) -> str | None:
    text = getattr(response, "text", None)
    if isinstance(text, str) and text.strip():
        return text

    candidates = getattr(response, "candidates", None) or []
    parts: list[str] = []
    for cand in candidates:
        content = getattr(cand, "content", None)
        cand_parts = getattr(content, "parts", None) or []
        for part in cand_parts:
            part_text = getattr(part, "text", None)
            if isinstance(part_text, str) and part_text.strip():
                parts.append(part_text)
    if not parts:
        return None
    return "\n".join(parts)


class GeminiAdapter:
    provider = "gemini"

    def generate(self, model: str, prompt: str, params: dict[str, Any] | None = None) -> str:
        params = params or {}
        api_key = os.getenv("GEMINI_API_KEY")
        if not api_key:
            raise RuntimeError("GEMINI_API_KEY is not set")

        try:
            from google import genai
        except ImportError as exc:
            raise RuntimeError("google-genai package is not installed") from exc

        client = genai.Client(api_key=api_key)
        base_config = {
            "temperature": float(params.get("temperature", 0.0)),
            "max_output_tokens": int(params.get("max_output_tokens", 512)),
        }
        config = {
            **base_config,
            # Keep response tokens available for final text instead of spending the whole budget on thoughts.
            "thinking_config": {"thinking_budget": int(params.get("thinking_budget", 128))},
        }
        response = client.models.generate_content(
            model=model,
            contents=prompt,
            config=config,
        )
        text = _extract_gemini_text(response)
        if not text:
            raise RuntimeError("Gemini response did not include text")
        return text
