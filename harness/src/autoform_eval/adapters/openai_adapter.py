from __future__ import annotations

import os
from typing import Any


class OpenAIAdapter:
    provider = "openai"

    def generate(self, model: str, prompt: str, params: dict[str, Any] | None = None) -> str:
        params = params or {}
        api_key = os.getenv("OPENAI_API_KEY")
        if not api_key:
            raise RuntimeError("OPENAI_API_KEY is not set")

        try:
            from openai import OpenAI
        except ImportError as exc:
            raise RuntimeError("openai package is not installed") from exc

        client = OpenAI(api_key=api_key)
        response = client.responses.create(
            model=model,
            input=prompt,
            temperature=float(params.get("temperature", 0.0)),
            max_output_tokens=int(params.get("max_output_tokens", 512)),
        )
        text = getattr(response, "output_text", None)
        if not text:
            raise RuntimeError("OpenAI response did not include output_text")
        return text
