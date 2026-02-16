from __future__ import annotations

import argparse
import json
import os
import sys
import time
from pathlib import Path
from typing import Any

from .adapters import GeminiAdapter, OpenAIAdapter
from .cache import JsonCache, stable_hash
from .dataset import DatasetError, load_split
from .lean_runner import classify_failure, run_lean_file
from .parse import parse_candidate
from .render import render_test1, render_test2
from .report import compute_summary, write_report, write_summary
from .types import excerpt
from .validate import validate_split


def _repo_root() -> Path:
    return Path(__file__).resolve().parents[3]


def _default_dataset_dir() -> Path:
    return _repo_root() / "dataset"


def _default_lean_dir() -> Path:
    return _repo_root() / "lean"


def _default_results_root() -> Path:
    return _repo_root() / "results" / "runs"


def _default_cache_root() -> Path:
    return _repo_root() / "harness_cache"


def _mk_run_id() -> str:
    return time.strftime("%Y%m%d_%H%M%S", time.gmtime())


def _build_prompt(nl: str, context: str) -> str:
    rules = (
        "Return exactly one Lean term that elaborates to Prop. "
        "Do not return theorem/lemma/def/example/namespace/section/by/sorry."
    )
    parts = [rules, "", f"Natural language statement:\n{nl.strip()}"]
    ctx = context.strip()
    if ctx:
        parts.extend(["", f"Lean context:\n{ctx}"])
    return "\n".join(parts)


def _adapter_for(provider: str):
    provider = provider.lower().strip()
    if provider == "openai":
        return OpenAIAdapter()
    if provider == "gemini":
        return GeminiAdapter()
    raise ValueError(f"unsupported provider '{provider}'")


def _run_attempt(
    item,
    provider: str,
    model: str,
    params: dict[str, Any],
    k_index: int,
    lean_dir: Path,
    run_dir: Path,
    cache: JsonCache,
    timeout1_s: float,
    timeout2_s: float,
    hb1: int,
    hb2: int,
    mock: bool,
    save_prompt_text: bool,
) -> dict[str, Any]:
    prompt = _build_prompt(item.nl, item.context)
    prompt_hash = stable_hash(prompt)
    prompt_text = prompt if save_prompt_text else None

    cache_key_model = stable_hash(
        json.dumps(
            {
                "provider": provider,
                "model": model,
                "params": params,
                "prompt_hash": prompt_hash,
                "item_id": item.id,
                "schema_version": item.schema_version,
                "checker_version": item.checker_version,
                "k_index": k_index,
            },
            sort_keys=True,
        )
    )

    model_cache = cache.get("model", cache_key_model)
    if model_cache:
        candidate_raw = str(model_cache.get("candidate_raw", ""))
    else:
        if mock:
            candidate_raw = item.expected
        else:
            adapter = _adapter_for(provider)
            candidate_raw = adapter.generate(model=model, prompt=prompt, params=params)
        cache.set("model", cache_key_model, {"candidate_raw": candidate_raw})

    parse_res = parse_candidate(candidate_raw, forbidden_ok=set(item.forbidden_ok), strict_reject_assign=False)
    if not parse_res.accepted:
        return {
            "test1_pass": False,
            "test2_pass": False,
            "shape_pass": None,
            "bucket": "output_parse_reject",
            "test1_elapsed_ms": 0,
            "test2_elapsed_ms": 0,
            "stdout_excerpt": "",
            "stderr_excerpt": parse_res.reason or "output_parse_reject",
            "candidate_raw": candidate_raw,
            "candidate_hash": stable_hash(candidate_raw),
            "prompt_hash": prompt_hash,
            "prompt_text": prompt_text,
            "test1_rendered_path": "",
            "test2_rendered_path": "",
            "test1_stdout_log_path": "",
            "test1_stderr_log_path": "",
            "test2_stdout_log_path": "",
            "test2_stderr_log_path": "",
        }

    candidate = parse_res.candidate

    rendered_dir = run_dir / "rendered"
    logs_dir = run_dir / "logs"
    rendered_dir.mkdir(parents=True, exist_ok=True)
    logs_dir.mkdir(parents=True, exist_ok=True)

    t1_content = render_test1(lean_dir, item, candidate, hb1)
    t1_path = rendered_dir / f"{item.id}.{provider}.{model}.k{k_index}.test1.lean"
    t1_path.write_text(t1_content, encoding="utf-8")
    t1_rendered_rel = str(t1_path.relative_to(run_dir))

    lean_key1 = stable_hash(
        json.dumps(
            {
                "toolchain": (lean_dir / "lean-toolchain").read_text(encoding="utf-8").strip()
                if (lean_dir / "lean-toolchain").exists()
                else "",
                "rendered": t1_content,
                "hb": hb1,
                "timeout": timeout1_s,
            },
            sort_keys=True,
        )
    )
    lean_cache1 = cache.get("lean", lean_key1)
    if lean_cache1:
        t1_ok = bool(lean_cache1.get("ok"))
        t1_elapsed = int(lean_cache1.get("elapsed_ms", 0))
        t1_stdout = str(lean_cache1.get("stdout", ""))
        t1_stderr = str(lean_cache1.get("stderr", ""))
        t1_timeout = bool(lean_cache1.get("timed_out", False))
    else:
        t1_res = run_lean_file(lean_dir, t1_path, timeout1_s)
        t1_ok = t1_res.ok
        t1_elapsed = t1_res.elapsed_ms
        t1_stdout = t1_res.stdout
        t1_stderr = t1_res.stderr
        t1_timeout = t1_res.timed_out
        cache.set(
            "lean",
            lean_key1,
            {
                "ok": t1_ok,
                "timed_out": t1_timeout,
                "elapsed_ms": t1_elapsed,
                "stdout": t1_stdout,
                "stderr": t1_stderr,
            },
        )

    t1_stderr_path = logs_dir / f"{item.id}.{provider}.{model}.k{k_index}.test1.stderr.log"
    t1_stdout_path = logs_dir / f"{item.id}.{provider}.{model}.k{k_index}.test1.stdout.log"
    t1_stderr_path.write_text(t1_stderr, encoding="utf-8")
    t1_stdout_path.write_text(t1_stdout, encoding="utf-8")
    t1_stderr_rel = str(t1_stderr_path.relative_to(run_dir))
    t1_stdout_rel = str(t1_stdout_path.relative_to(run_dir))

    if not t1_ok:
        return {
            "test1_pass": False,
            "test2_pass": False,
            "shape_pass": None,
            "bucket": classify_failure(t1_stderr, t1_timeout, t1_stdout),
            "test1_elapsed_ms": t1_elapsed,
            "test2_elapsed_ms": 0,
            "stdout_excerpt": excerpt(t1_stdout),
            "stderr_excerpt": excerpt(t1_stderr),
            "candidate_raw": candidate_raw,
            "candidate_hash": stable_hash(candidate),
            "prompt_hash": prompt_hash,
            "prompt_text": prompt_text,
            "test1_rendered_path": t1_rendered_rel,
            "test2_rendered_path": "",
            "test1_stdout_log_path": t1_stdout_rel,
            "test1_stderr_log_path": t1_stderr_rel,
            "test2_stdout_log_path": "",
            "test2_stderr_log_path": "",
        }

    t2_content = render_test2(lean_dir, item, candidate, hb2)
    t2_path = rendered_dir / f"{item.id}.{provider}.{model}.k{k_index}.test2.lean"
    t2_path.write_text(t2_content, encoding="utf-8")
    t2_rendered_rel = str(t2_path.relative_to(run_dir))

    lean_key2 = stable_hash(
        json.dumps(
            {
                "toolchain": (lean_dir / "lean-toolchain").read_text(encoding="utf-8").strip()
                if (lean_dir / "lean-toolchain").exists()
                else "",
                "rendered": t2_content,
                "hb": hb2,
                "timeout": timeout2_s,
            },
            sort_keys=True,
        )
    )
    lean_cache2 = cache.get("lean", lean_key2)
    if lean_cache2:
        t2_ok = bool(lean_cache2.get("ok"))
        t2_elapsed = int(lean_cache2.get("elapsed_ms", 0))
        t2_stdout = str(lean_cache2.get("stdout", ""))
        t2_stderr = str(lean_cache2.get("stderr", ""))
        t2_timeout = bool(lean_cache2.get("timed_out", False))
    else:
        t2_res = run_lean_file(lean_dir, t2_path, timeout2_s)
        t2_ok = t2_res.ok
        t2_elapsed = t2_res.elapsed_ms
        t2_stdout = t2_res.stdout
        t2_stderr = t2_res.stderr
        t2_timeout = t2_res.timed_out
        cache.set(
            "lean",
            lean_key2,
            {
                "ok": t2_ok,
                "timed_out": t2_timeout,
                "elapsed_ms": t2_elapsed,
                "stdout": t2_stdout,
                "stderr": t2_stderr,
            },
        )

    t2_stderr_path = logs_dir / f"{item.id}.{provider}.{model}.k{k_index}.test2.stderr.log"
    t2_stdout_path = logs_dir / f"{item.id}.{provider}.{model}.k{k_index}.test2.stdout.log"
    t2_stderr_path.write_text(t2_stderr, encoding="utf-8")
    t2_stdout_path.write_text(t2_stdout, encoding="utf-8")
    t2_stderr_rel = str(t2_stderr_path.relative_to(run_dir))
    t2_stdout_rel = str(t2_stdout_path.relative_to(run_dir))

    bucket = "pass" if t2_ok else classify_failure(t2_stderr, t2_timeout, t2_stdout)
    t2_text = f"{t2_stderr}\n{t2_stdout}"
    return {
        "test1_pass": True,
        "test2_pass": bool(t2_ok),
        "shape_pass": None if t2_ok else (False if "[shape_fail]" in t2_text else None),
        "bucket": bucket,
        "test1_elapsed_ms": t1_elapsed,
        "test2_elapsed_ms": t2_elapsed,
        "stdout_excerpt": excerpt(t2_stdout),
        "stderr_excerpt": excerpt(t2_stderr),
        "candidate_raw": candidate_raw,
        "candidate_hash": stable_hash(candidate),
        "prompt_hash": prompt_hash,
        "prompt_text": prompt_text,
        "test1_rendered_path": t1_rendered_rel,
        "test2_rendered_path": t2_rendered_rel,
        "test1_stdout_log_path": t1_stdout_rel,
        "test1_stderr_log_path": t1_stderr_rel,
        "test2_stdout_log_path": t2_stdout_rel,
        "test2_stderr_log_path": t2_stderr_rel,
    }


def cmd_validate(args: argparse.Namespace) -> int:
    budget1_ms = args.budget1_ms if args.budget1_ms is not None else int(args.timeout1 * 1000)
    budget2_ms = args.budget2_ms if args.budget2_ms is not None else int(args.timeout2 * 1000)
    try:
        summary = validate_split(
            dataset_dir=Path(args.dataset_dir),
            split=args.split,
            lean_dir=Path(args.lean_dir),
            out_report=Path(args.out_report),
            rendered_dir=Path(args.rendered_dir),
            use_lean=not args.skip_lean,
            test1_heartbeats=args.test1_heartbeats,
            test2_heartbeats=args.test2_heartbeats,
            timeout1_s=args.timeout1,
            timeout2_s=args.timeout2,
            budget1_ms=budget1_ms,
            budget2_ms=budget2_ms,
            determinism_repeats=args.determinism_repeats,
            determinism_jitter_ms=args.determinism_jitter_ms,
        )
    except DatasetError as exc:
        print(f"dataset error: {exc}", file=sys.stderr)
        return 2

    print(json.dumps({"split": summary["split"], "total": summary["total"], "invalid": summary["invalid"]}, indent=2))
    return 0 if summary["invalid"] == 0 else 1


def cmd_run(args: argparse.Namespace) -> int:
    dataset_dir = Path(args.dataset_dir)
    lean_dir = Path(args.lean_dir)
    results_root = Path(args.results_root)
    cache_root = Path(args.cache_root)

    try:
        items = load_split(dataset_dir, args.split)
    except DatasetError as exc:
        print(f"dataset error: {exc}", file=sys.stderr)
        return 2

    run_id = args.run_id or _mk_run_id()
    run_dir = results_root / run_id
    run_dir.mkdir(parents=True, exist_ok=True)
    cache = JsonCache(cache_root)

    models: list[tuple[str, str]] = []
    for token in args.models.split(","):
        token = token.strip()
        if not token:
            continue
        if ":" not in token:
            print(f"invalid model token '{token}', expected provider:model", file=sys.stderr)
            return 2
        provider, model = token.split(":", 1)
        models.append((provider.strip(), model.strip()))

    records: list[dict[str, Any]] = []
    toolchain = (lean_dir / "lean-toolchain").read_text(encoding="utf-8").strip() if (lean_dir / "lean-toolchain").exists() else ""

    for item in items:
        for provider, model in models:
            for k_index in range(1, args.k + 1):
                try:
                    attempt = _run_attempt(
                        item=item,
                        provider=provider,
                        model=model,
                        params={"temperature": args.temperature, "max_output_tokens": args.max_output_tokens},
                        k_index=k_index,
                        lean_dir=lean_dir,
                        run_dir=run_dir,
                        cache=cache,
                        timeout1_s=args.timeout1,
                        timeout2_s=args.timeout2,
                        hb1=args.test1_heartbeats,
                        hb2=args.test2_heartbeats,
                        mock=args.mock,
                        save_prompt_text=args.save_prompt_text,
                    )
                except Exception as exc:  # noqa: BLE001
                    attempt = {
                        "test1_pass": False,
                        "test2_pass": False,
                        "shape_pass": None,
                        "bucket": "elab_fail",
                        "test1_elapsed_ms": 0,
                        "test2_elapsed_ms": 0,
                        "stdout_excerpt": "",
                        "stderr_excerpt": f"runner_exception:{exc}",
                        "candidate_raw": "",
                        "candidate_hash": "",
                        "prompt_hash": "",
                        "prompt_text": None,
                        "test1_rendered_path": "",
                        "test2_rendered_path": "",
                        "test1_stdout_log_path": "",
                        "test1_stderr_log_path": "",
                        "test2_stdout_log_path": "",
                        "test2_stderr_log_path": "",
                    }

                record = {
                    "run_id": run_id,
                    "item_id": item.id,
                    "split": item.split,
                    "family": item.family,
                    "tier": item.tier,
                    "tags": item.tags,
                    "provider": provider,
                    "model": model,
                    "attempt_index": k_index,
                    "params": {"temperature": args.temperature, "max_output_tokens": args.max_output_tokens},
                    "prompt_hash": attempt["prompt_hash"],
                    "candidate_raw": attempt["candidate_raw"],
                    "candidate_hash": attempt["candidate_hash"],
                    "lean_toolchain": toolchain,
                    "mathlib_rev": args.mathlib_rev,
                    "test1_heartbeats": args.test1_heartbeats,
                    "test2_heartbeats": args.test2_heartbeats,
                    "test1_pass": attempt["test1_pass"],
                    "test2_pass": attempt["test2_pass"],
                    "shape_pass": attempt["shape_pass"],
                    "bucket": attempt["bucket"],
                    "test1_elapsed_ms": attempt["test1_elapsed_ms"],
                    "test2_elapsed_ms": attempt["test2_elapsed_ms"],
                    "stderr_excerpt": attempt["stderr_excerpt"],
                    "stdout_excerpt": attempt["stdout_excerpt"],
                    "test1_rendered_path": attempt["test1_rendered_path"],
                    "test2_rendered_path": attempt["test2_rendered_path"],
                    "test1_stdout_log_path": attempt["test1_stdout_log_path"],
                    "test1_stderr_log_path": attempt["test1_stderr_log_path"],
                    "test2_stdout_log_path": attempt["test2_stdout_log_path"],
                    "test2_stderr_log_path": attempt["test2_stderr_log_path"],
                }
                if attempt["prompt_text"] is not None:
                    record["prompt_text"] = attempt["prompt_text"]
                records.append(record)

    results_path = run_dir / "results.jsonl"
    with results_path.open("w", encoding="utf-8") as f:
        for row in records:
            f.write(json.dumps(row, sort_keys=True) + "\n")

    summary = compute_summary(records)
    write_summary(run_dir / "summary.json", summary)
    write_report(run_dir / "report.md", records, summary)

    print(json.dumps({"run_id": run_id, "records": len(records), "path": str(run_dir)}, indent=2))
    return 0


def cmd_report(args: argparse.Namespace) -> int:
    run_dir = Path(args.run_dir)
    results_path = run_dir / "results.jsonl"
    if not results_path.exists():
        print(f"missing {results_path}", file=sys.stderr)
        return 2

    records: list[dict[str, Any]] = []
    with results_path.open("r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            records.append(json.loads(line))

    summary = compute_summary(records)
    write_summary(run_dir / "summary.json", summary)
    write_report(run_dir / "report.md", records, summary)
    print(json.dumps({"run_dir": str(run_dir), "records": len(records)}, indent=2))
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(prog="autoform-eval")
    sub = parser.add_subparsers(dest="cmd", required=True)

    validate = sub.add_parser("validate")
    validate.add_argument("--split", default="pilot")
    validate.add_argument("--dataset-dir", default=str(_default_dataset_dir()))
    validate.add_argument("--lean-dir", default=str(_default_lean_dir()))
    validate.add_argument("--out-report", default=str(_default_dataset_dir() / "validation_report.json"))
    validate.add_argument("--rendered-dir", default=str(_default_results_root() / "validate_rendered"))
    validate.add_argument("--skip-lean", action="store_true")
    validate.add_argument("--test1-heartbeats", type=int, default=40000)
    validate.add_argument("--test2-heartbeats", type=int, default=200000)
    validate.add_argument("--timeout1", type=float, default=8.0)
    validate.add_argument("--timeout2", type=float, default=20.0)
    validate.add_argument("--budget1-ms", type=int, default=None)
    validate.add_argument("--budget2-ms", type=int, default=None)
    validate.add_argument("--determinism-repeats", type=int, default=1)
    validate.add_argument("--determinism-jitter-ms", type=int, default=None)
    validate.set_defaults(func=cmd_validate)

    run = sub.add_parser("run")
    run.add_argument("--split", default="pilot")
    run.add_argument("--models", default="openai:gpt-5")
    run.add_argument("--k", type=int, default=1)
    run.add_argument("--mock", action="store_true", help="Use expected proposition as model output")
    run.add_argument("--dataset-dir", default=str(_default_dataset_dir()))
    run.add_argument("--lean-dir", default=str(_default_lean_dir()))
    run.add_argument("--results-root", default=str(_default_results_root()))
    run.add_argument("--cache-root", default=str(_default_cache_root()))
    run.add_argument("--run-id", default="")
    run.add_argument("--mathlib-rev", default=os.getenv("MATHLIB_REV", "unknown"))
    run.add_argument("--temperature", type=float, default=0.0)
    run.add_argument("--max-output-tokens", type=int, default=512)
    run.add_argument("--save-prompt-text", action="store_true")
    run.add_argument("--test1-heartbeats", type=int, default=40000)
    run.add_argument("--test2-heartbeats", type=int, default=200000)
    run.add_argument("--timeout1", type=float, default=8.0)
    run.add_argument("--timeout2", type=float, default=20.0)
    run.set_defaults(func=cmd_run)

    report = sub.add_parser("report")
    report.add_argument("--run-dir", required=True)
    report.set_defaults(func=cmd_report)

    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
