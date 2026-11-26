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


def annotated_articles(blueprint: Path) -> dict[str, tuple[Path, list[str]]]:
    """Each article's durable ID, with its page and its Lean names, as blueprint/links/ records them."""
    articles: dict[str, tuple[Path, list[str]]] = {}
    mathlib = blueprint / "links" / "mathlib"
    for path in sorted((blueprint / "links").rglob("*.jsonl")):
        for line in path.read_text(encoding="utf-8").splitlines():
            entry = json.loads(line) if line.strip() else {}
            identity = entry.get("id")
            if not isinstance(identity, str):
                continue
            pages = {Path(os.path.normpath(path.parent / subject["uri"])) for subject in entry.get("subject", [])}
            # The article's own annotation lists its Lean names in order; the Mathlib one, its Mathlib names.
            names = [] if path.is_relative_to(mathlib) else [
                item["location"]["declaration"] for item in entry.get("object", [])]
            page, known = articles.get(identity, (None, []))
            if len(pages) != 1 or (page is not None and {page} != pages):
                raise ValueError(f"article ID {identity} names more than one page")
            articles[identity] = (pages.pop(), known + names)
    return articles


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--article-id", required=True)
    parser.add_argument("--module", required=True)
    parser.add_argument("--declaration", action="append", required=True)
    parser.add_argument("--prepare-only", action="store_true")
    args = parser.parse_args()
    if not re.fullmatch(r"af_[0-9a-f]{24}", args.article_id):
        parser.error("article-id must be a durable Autoform article ID")
    # Lean declaration names can include Unicode letters such as ι and subscripts.
    # Keep each component an identifier so the generated probes cannot inject code.
    lean_name = r"(?:[^\W\d]|_)[\w]*(?:\.(?:[^\W\d]|_)[\w]*)*"
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
    autoform_ref = (root / ".github" / "autoform-ref").read_text().strip()
    autoform = [
        "uvx", "--from",
        "git+https://github.com/facebookresearch/autoform-bot.git@" + autoform_ref,
        "autoform",
    ]

    # Articles' facts, their IDs and Lean names among them, live in blueprint/links/; the projection's
    # mappings are written there with the pinned CLI, as an agent would record them.
    try:
        articles = annotated_articles(blueprint)
    except (KeyError, TypeError, ValueError) as error:
        parser.error(f"cannot read blueprint/links/: {error}")
    roadmap = blueprint / "roadmap"
    if args.article_id not in articles or not articles[args.article_id][0].is_relative_to(roadmap):
        parser.error("article ID must identify exactly one roadmap article")
    article, mapped = articles[args.article_id]
    if mapped and mapped != args.declaration:
        parser.error("the article already maps a different Lean declaration")
    added_mapping = not mapped
    if added_mapping:
        run(autoform + ["links", "set", str(blueprint), str(article), "lean=" + ", ".join(args.declaration)])

    source = root.joinpath(*args.module.split(".")).with_suffix(".lean")
    if not source.is_file() or source.is_symlink():
        parser.error("the selected module must have a regular project source file")
    manifest = {
        "schema": "hatcher-formalize-evidence/v1",
        "commit": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], text=True
        ).strip(),
        "autoform_ref": autoform_ref,
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
    additional_path = root / "scripts" / "formalize_additional_targets.json"
    additional = []
    if additional_path.exists():
        if not additional_path.is_file() or additional_path.is_symlink():
            parser.error("additional evidence selections must be a regular file")
        selections = json.loads(additional_path.read_text(encoding="utf-8"))
        if selections.get("schema") != "hatcher-additional-evidence/v1" or not isinstance(
                selections.get("articles"), list):
            parser.error("invalid additional evidence selection schema")
        seen = {args.article_id}
        for selected in selections["articles"]:
            article_id = selected.get("article_id")
            module = selected.get("module")
            declarations = selected.get("declarations")
            if (not isinstance(article_id, str) or not re.fullmatch(r"af_[0-9a-f]{24}", article_id)
                    or article_id in seen):
                parser.error("invalid or duplicate additional article ID")
            seen.add(article_id)
            if not isinstance(module, str) or not re.fullmatch(lean_name, module):
                parser.error("invalid additional module")
            if (not isinstance(declarations, list) or not declarations
                    or any(not isinstance(name, str) or not re.fullmatch(lean_name, name)
                           for name in declarations)
                    or len(set(declarations)) != len(declarations)):
                parser.error("invalid additional declarations")
            if article_id not in articles or not articles[article_id][0].is_relative_to(roadmap):
                parser.error("additional article ID must identify exactly one article")
            selected_article, old_mappings = articles[article_id]
            if old_mappings and old_mappings != declarations:
                parser.error("additional article already maps different declarations")
            if not old_mappings:
                run(autoform + ["links", "set", str(blueprint), str(selected_article),
                                "lean=" + ", ".join(declarations)])
            selected_source = root.joinpath(*module.split(".")).with_suffix(".lean")
            if not selected_source.is_file() or selected_source.is_symlink():
                parser.error("additional module must have a regular project source")
            additional.append({
                **manifest, "article_id": article_id,
                "article_path": selected_article.relative_to(blueprint).as_posix(),
                "module": module, "declaration": declarations[0], "declarations": declarations,
                "lean_source_sha256": hashlib.sha256(selected_source.read_bytes()).hexdigest(),
                "review_projection_added_target_mapping": not old_mappings,
            })
        (artifacts / "additional-manifest.json").write_text(
            json.dumps({"schema": "hatcher-additional-evidence/v1", "articles": additional}, indent=2)
            + "\n", encoding="utf-8")
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
    for selected in additional:
        selected_probe = destination / (selected["article_id"] + "Checks.lean")
        selected_probe.write_text(
            f"import {selected['module']}\nimport Batteries.Tactic.Lint\n\n"
            + "".join(f"#print axioms {name}\n" for name in selected["declarations"])
            + f"#lint only unusedArguments in {selected['module']}\n", encoding="utf-8")
        run(["lake", "env", "lean", str(selected_probe)],
            artifacts / (selected["article_id"] + "-axioms-and-lint.txt"))
    import_selections_path = root / "scripts" / "formalize_import_targets.json"
    if import_selections_path.exists():
        if not import_selections_path.is_file() or import_selections_path.is_symlink():
            parser.error("import evidence selections must be a regular file")
        import_selections = json.loads(import_selections_path.read_text(encoding="utf-8"))
        if (import_selections.get("schema") != "hatcher-import-evidence/v1"
                or not isinstance(import_selections.get("targets"), list)):
            parser.error("invalid import evidence selection schema")
        seen_imports = set()
        for selected in import_selections["targets"]:
            article_id = selected.get("article_id")
            module = selected.get("module")
            if (not isinstance(article_id, str) or not re.fullmatch(r"af_[0-9a-f]{24}", article_id)
                    or not isinstance(module, str) or not re.fullmatch(lean_name, module)
                    or article_id in seen_imports):
                parser.error("invalid or duplicate import evidence target")
            seen_imports.add(article_id)
            impact = subprocess.run(
                autoform + ["work", "import-impact", article_id, module, str(root),
                            "--lean-root", str(root), "--json"],
                capture_output=True, text=True)
            print(impact.stdout, end="", flush=True)
            print(impact.stderr, end="", flush=True)
            if impact.returncode:
                raise SystemExit(impact.returncode)
            json.loads(impact.stdout)
            (artifacts / (article_id + "-import-impact.json")).write_text(
                impact.stdout, encoding="utf-8")
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
