#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path


def format_jsonl(path: Path) -> int:
    rows = []
    for idx, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        text = line.strip()
        if not text:
            continue
        try:
            rows.append(json.loads(text))
        except json.JSONDecodeError as exc:
            raise ValueError(f"{path}:{idx}: invalid JSON: {exc}") from exc

    path.write_text(
        "\n".join(json.dumps(row, separators=(",", ":"), ensure_ascii=False) for row in rows) + "\n",
        encoding="utf-8",
    )
    return len(rows)


def main() -> int:
    parser = argparse.ArgumentParser(description="Canonicalize a JSONL file (one compact JSON object per line).")
    parser.add_argument("path", nargs="?", default="dataset/pilot.jsonl", help="Path to JSONL file")
    args = parser.parse_args()

    path = Path(args.path)
    if not path.exists():
        raise FileNotFoundError(f"missing file: {path}")

    count = format_jsonl(path)
    print(f"formatted {count} rows in {path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
