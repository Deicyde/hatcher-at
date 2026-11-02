"""Validate source provenance retained from the legacy Autoform workspace."""

import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate source-index key: {key}")
        result[key] = value
    return result


def read_file(root: Path, relative: str, prefix: str) -> bytes:
    path = PurePosixPath(relative)
    if path.is_absolute() or ".." in path.parts or path.parts[:1] != (prefix,):
        raise ValueError(f"invalid {prefix} path: {relative}")
    target = root.joinpath(*path.parts)
    if target.is_symlink() or not target.is_file():
        raise ValueError(f"missing or symbolic-link file: {relative}")
    if not target.resolve().is_relative_to(root.resolve()):
        raise ValueError(f"path escapes the blueprint: {relative}")
    return target.read_bytes()


def verify(blueprint: Path) -> tuple[int, int]:
    data = json.loads(read_file(blueprint, "sources/source-units.json", "sources"),
                      object_pairs_hook=unique_object)
    if data.get("schema") != "hatcher-source-units/v1":
        raise ValueError("unsupported source-unit index schema")
    artifact = read_file(blueprint, data["artifact"], "sources")
    if hashlib.sha256(artifact).hexdigest() != data["artifact_sha256"]:
        raise ValueError("source ledger SHA-256 does not match its index")
    lines = artifact.splitlines(keepends=True)
    units = {}
    for unit in data["units"]:
        identity = unit["unit"]
        if identity in units:
            raise ValueError(f"duplicate source unit: {identity}")
        start, stop = unit["start_line"], unit["end_line"]
        if not isinstance(start, int) or not isinstance(stop, int) or not 1 <= start <= stop <= len(lines):
            raise ValueError(f"invalid source span: {identity}")
        if hashlib.sha256(b"".join(lines[start - 1:stop])).hexdigest() != unit["unit_sha256"]:
            raise ValueError(f"source-unit SHA-256 does not match its ledger span: {identity}")
        units[identity] = unit
    if not units or not data["articles"]:
        raise ValueError("source-unit index has no source accounting")
    for identity, article in data["articles"].items():
        if re.fullmatch(r"af_[0-9a-f]{24}", identity) is None:
            raise ValueError(f"invalid article identity: {identity}")
        text = read_file(blueprint, article["path"], "roadmap").decode("utf-8")
        if not text.startswith("---\n"):
            raise ValueError(f"article has no frontmatter: {article['path']}")
        frontmatter = text.split("\n---\n", 1)[0]
        if re.search(r"(?m)^article_id: " + re.escape(identity) + r"$", frontmatter) is None:
            raise ValueError(f"source-unit mapping names the wrong article: {article['path']}")
        membership = article["source_units"]
        if not membership or any(unit not in units for unit in membership):
            raise ValueError(f"article names an unknown or empty source-unit set: {identity}")
    return len(units), len(data["articles"])


if __name__ == "__main__":
    try:
        count, articles = verify(Path(sys.argv[1]) if len(sys.argv) == 2 else Path("blueprint"))
    except (KeyError, OSError, UnicodeError, ValueError) as error:
        sys.exit(f"source-unit provenance failed: {error}")
    print(f"Source-unit provenance verified: {count} units, {articles} article mappings")
