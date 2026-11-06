#!/usr/bin/env python3
"""Export built proof evidence without asserting roadmap progress."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess


def run(command: list[str], output: Path | None = None) -> None:
    result = subprocess.run(command, capture_output=True, text=True)
    combined = result.stdout + result.stderr
    if output is not None:
        output.write_text(combined, encoding="utf-8")
    print(combined, end="", flush=True)
    if result.returncode:
        raise SystemExit(result.returncode)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--article-id", required=True)
    parser.add_argument("--module", required=True)
    parser.add_argument("--declaration", action="append", required=True)
    parser.add_argument("--prepare-only", action="store_true")
    args = parser.parse_args()
    if not re.fullmatch(r"af_[0-9a-f]{24}", args.article_id):
        parser.error("article-id must be a durable Autoform article ID")
    lean_name = r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*"
    for value in [args.module, *args.declaration]:
        if not re.fullmatch(lean_name, value):
            parser.error("module and declaration must be qualified Lean names")

    root = Path.cwd().resolve()
    destination = root / ".lake" / "formalize-evidence"
    if destination.exists():
        parser.error("evidence destination already exists; preserve the previous run")
    artifacts = destination / "artifacts"
    artifacts.mkdir(parents=True)
    blueprint = destination / "blueprint"
    shutil.copytree(root / "blueprint", blueprint)

    matches: list[Path] = []
    for path in (blueprint / "roadmap").rglob("*.md"):
        text = path.read_text(encoding="utf-8")
        if not text.startswith("---\n"):
            continue
        end = text.find("\n---\n", 4)
        if end < 0:
            continue
        if f"article_id: {args.article_id}" in text[4:end].splitlines():
            matches.append(path)
    if len(matches) != 1:
        parser.error("article ID must identify exactly one roadmap article")
    article = matches[0]
    text = article.read_text(encoding="utf-8")
    end = text.find("\n---\n", 4)
    header = text[4:end].splitlines()
    mappings = [line for line in header if line.startswith("lean:")]
    expected_mapping = (
        f"lean: {args.declaration[0]}" if len(args.declaration) == 1
        else "lean: [" + ", ".join(args.declaration) + "]"
    )
    if mappings and mappings != [expected_mapping]:
        parser.error("the article already maps a different Lean declaration")
    added_mapping = not mappings
    if added_mapping:
        article.write_text(
            text[:end] + "\n" + expected_mapping + text[end:], encoding="utf-8"
        )

    source = root.joinpath(*args.module.split(".")).with_suffix(".lean")
    if not source.is_file() or source.is_symlink():
        parser.error("the selected module must have a regular project source file")
    manifest = {
        "schema": "hatcher-formalize-evidence/v1",
        "commit": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], text=True
        ).strip(),
        "autoform_ref": (root / ".github" / "autoform-ref").read_text().strip(),
        "article_id": args.article_id,
        "article_path": article.relative_to(blueprint).as_posix(),
        "module": args.module,
        "declaration": args.declaration[0],
        "declarations": args.declaration,
        "lean_source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "review_projection_added_target_mapping": added_mapping,
        "progress_assertions_changed": False,
        "github_run_id": os.environ.get("GITHUB_RUN_ID"),
    }
    (artifacts / "manifest.json").write_text(
        json.dumps(manifest, indent=2) + "\n", encoding="utf-8"
    )
    if args.prepare_only:
        print("Review projection prepared; no Lean command was run.")
        return

    probe = destination / "Checks.lean"
    probe.write_text(
        f"import {args.module}\n"
        "import Batteries.Tactic.Lint\n\n"
        + "".join(f"#print axioms {name}\n" for name in args.declaration)
        + f"#lint only unusedArguments in {args.module}\n",
        encoding="utf-8",
    )
    run(["lake", "env", "lean", str(probe)], artifacts / "axioms-and-lint.txt")
    autoform = [
        "uvx", "--from",
        "git+https://github.com/facebookresearch/autoform-bot.git@"
        + manifest["autoform_ref"],
        "autoform",
    ]
    run(autoform + ["check", str(blueprint), "--lean-root", str(root)],
        artifacts / "check.txt")
    run(autoform + [
        "skeleton", str(blueprint), "--lean-root", str(root),
        "--output", str(artifacts / "skeleton.json"),
        "--packets", str(artifacts / "packets"),
        "--passages", str(artifacts / "passages"),
    ], artifacts / "skeleton-log.txt")


if __name__ == "__main__":
    main()
