"""Repair the pinned renderer's Book ordering without editing its output files."""

from collections import defaultdict
from pathlib import PurePosixPath
import re

from mkdocs.plugins import event_priority


_ENTRY = re.compile(r" +\- (?P<label>\[.+\]\((?P<path>[^()\n]+)\))")


def normalize_summary(content: str) -> str:
    """Group generated links by their nearest listed directory ancestor.

    The renderer follows every prose link, so a landing-page shortcut can put
    a deep chapter before its parents. Absolute-depth indentation then produces
    invalid Markdown. Keep every original label and target, preserve encounter
    order among siblings, and emit a proper depth-first list. This is only a
    publication projection: the vault remains the sole navigation source.
    """
    lines = content.splitlines()
    if "- Book" not in lines:
        return content
    start = lines.index("- Book") + 1
    end = next((i for i in range(start, len(lines)) if lines[i].startswith("- ")),
               len(lines))
    entries = {}
    for line in lines[start:end]:
        if not line.strip():
            continue
        match = _ENTRY.fullmatch(line)
        if match is None:
            raise ValueError(f"Unexpected generated Book navigation entry: {line!r}")
        target = match["path"]
        path = PurePosixPath(target)
        if path.is_absolute() or ".." in path.parts or target in entries:
            raise ValueError(f"Invalid or duplicate generated navigation target: {target!r}")
        entries[target] = match["label"]

    children = defaultdict(list)
    for target in entries:
        path = PurePosixPath(target)
        ancestors = path.parent.parents if path.name == "README.md" else (path.parent, *path.parent.parents)
        parent = next((str(directory / "README.md") for directory in ancestors
                       if str(directory / "README.md") in entries), None)
        children[parent].append(target)

    ordered = []

    def emit(parent, depth):
        for target in children[parent]:
            ordered.append("    " * depth + "- " + entries[target])
            emit(target, depth + 1)

    emit(None, 1)
    if len(ordered) != len(entries):
        raise ValueError("Generated Book navigation contains an ancestry cycle")
    return "\n".join([*lines[:start], *ordered, *lines[end:]]) + "\n"


@event_priority(100)  # Before literate-nav's on_files handler (priority -100).
def on_files(files, *, config):
    summary = files.get_file_from_path("SUMMARY.md")
    if summary is not None:
        summary.content_string = normalize_summary(summary.content_string)
    return files
