from __future__ import annotations

import json
import os
from urllib import error, request
from typing import Any


def _get_field(obj: Any, key: str) -> Any:
    if isinstance(obj, dict):
        return obj.get(key)
    return getattr(obj, key, None)


def _extract_response_text(response: Any) -> str | None:
    text = _get_field(response, "output_text")
    if isinstance(text, str) and text.strip():
        return text

    output = _get_field(response, "output")
    if not isinstance(output, list):
        return None

    parts: list[str] = []
    for item in output:
        content = _get_field(item, "content")
        if not isinstance(content, list):
            continue
        for piece in content:
            piece_text = _get_field(piece, "text")
            if isinstance(piece_text, str) and piece_text.strip():
                parts.append(piece_text)
    if not parts:
        return None
    return "\n".join(parts)


def _responses_api_fallback(api_key: str, payload: dict[str, Any]) -> dict[str, Any]:
    req = request.Request(
        "https://api.openai.com/v1/responses",
        data=json.dumps(payload).encode("utf-8"),
        headers={
            "Authorization": f"Bearer {api_key}",
            "Content-Type": "application/json",
        },
        method="POST",
    )
    try:
        with request.urlopen(req, timeout=120) as resp:
            return json.loads(resp.read().decode("utf-8"))
    except error.HTTPError as exc:
        body = exc.read().decode("utf-8", errors="replace")
        raise RuntimeError(f"OpenAI responses request failed ({exc.code}): {body[:300]}") from exc
    except error.URLError as exc:
        raise RuntimeError(f"OpenAI responses request failed: {exc}") from exc


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
        payload: dict[str, Any] = {
            "model": model,
            "input": prompt,
            "max_output_tokens": int(params.get("max_output_tokens", 512)),
        }
        if "temperature" in params and params.get("temperature") is not None:
            payload["temperature"] = float(params["temperature"])

        def _request(payload_in: dict[str, Any]) -> Any:
            if hasattr(client, "responses"):
                return client.responses.create(**payload_in)
            # Older 1.x SDK builds may not expose `client.responses`; fall back to direct REST.
            return _responses_api_fallback(api_key, payload_in)

        try:
            response = _request(payload)
        except Exception as exc:  # noqa: BLE001
            if "temperature" in payload and "unsupported parameter" in str(exc).lower() and "temperature" in str(exc).lower():
                payload_no_temp = dict(payload)
                payload_no_temp.pop("temperature", None)
                response = _request(payload_no_temp)
            else:
                raise

        text = _extract_response_text(response)
        if not text:
            raise RuntimeError("OpenAI response did not include output text")
        return text
