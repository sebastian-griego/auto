from __future__ import annotations

import os
from typing import Any


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
        response = client.models.generate_content(
            model=model,
            contents=prompt,
            config={
                "temperature": float(params.get("temperature", 0.0)),
                "max_output_tokens": int(params.get("max_output_tokens", 512)),
            },
        )
        text = getattr(response, "text", None)
        if not text:
            raise RuntimeError("Gemini response did not include text")
        return text
