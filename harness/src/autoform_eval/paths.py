from __future__ import annotations

from pathlib import Path


def repo_root() -> Path:
    return Path(__file__).resolve().parents[3]


def default_lean_dir() -> Path:
    return repo_root() / "lean"


def default_dataset_dir() -> Path:
    return repo_root() / "dataset"


def default_results_root() -> Path:
    return repo_root() / "results" / "runs"


def default_cache_root() -> Path:
    return repo_root() / "harness_cache"
