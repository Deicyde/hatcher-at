"""Regression tests for landing-page shortcuts in generated book navigation."""

from collections import Counter
import unittest

from scripts.blueprint_nav import normalize_summary, on_files
from mkdocs.structure.files import File, Files
from mkdocs_literate_nav.plugin import resolve_directories_in_nav


class BlueprintNavigationTests(unittest.TestCase):
    summary = (
        "- [Home](README.md)\n- Book\n"
        "                - [Degree](roadmap/homology/computations/degree/README.md)\n"
        "                    - [Shared](roadmap/homology/computations/degree/shared/README.md)\n"
        "    - [Roadmap](roadmap/README.md)\n"
        "        - [Fundamental group](roadmap/fundamental-group/README.md)\n"
        "        - [Homology](roadmap/homology/README.md)\n"
        "            - [Computations](roadmap/homology/computations/README.md)\n"
        "    - [Coverage](coverage/README.md)\n"
        "- Graph\n    - [DAG](dependencies.md)\n"
    )

    def test_shortcut_is_grouped_beneath_real_ancestors(self):
        self.assertEqual(normalize_summary(self.summary), (
            "- [Home](README.md)\n- Book\n"
            "    - [Roadmap](roadmap/README.md)\n"
            "        - [Fundamental group](roadmap/fundamental-group/README.md)\n"
            "        - [Homology](roadmap/homology/README.md)\n"
            "            - [Computations](roadmap/homology/computations/README.md)\n"
            "                - [Degree](roadmap/homology/computations/degree/README.md)\n"
            "                    - [Shared](roadmap/homology/computations/degree/shared/README.md)\n"
            "    - [Coverage](coverage/README.md)\n"
            "- Graph\n    - [DAG](dependencies.md)\n"
        ))

    def test_preserves_all_labels_and_targets_exactly_once(self):
        self.assertEqual(Counter(line.strip() for line in self.summary.splitlines()),
                         Counter(line.strip() for line in normalize_summary(self.summary).splitlines()))

    def test_idempotent(self):
        result = normalize_summary(self.summary)
        self.assertEqual(normalize_summary(result), result)

    def test_missing_ancestors_do_not_create_indent_gaps(self):
        self.assertEqual(normalize_summary(
            "- Book\n                - [Deep](roadmap/a/b/README.md)\n- Graph\n"
        ), "- Book\n    - [Deep](roadmap/a/b/README.md)\n- Graph\n")

    def test_malformed_or_duplicate_entries_are_rejected(self):
        for entry in ("    - unexpected", "    - [Bad](../README.md)",
                      "    - [One](a.md)\n    - [Two](a.md)"):
            with self.subTest(entry=entry), self.assertRaises(ValueError):
                normalize_summary("- Book\n" + entry + "\n")

    def test_pinned_literate_nav_parser_accepts_repaired_summary(self):
        summary = File("SUMMARY.md", ".", ".", False)
        summary.content_string = normalize_summary(self.summary)
        nav = resolve_directories_in_nav(None, Files([summary]), "SUMMARY.md",
                                         implicit_index=False)
        self.assertEqual(list(nav[1]), ["Book"])
        self.assertEqual(nav[1]["Book"][0]["Roadmap"][0], "roadmap/README.md")

    def test_hook_changes_only_in_memory_summary(self):
        summary = File("SUMMARY.md", ".", ".", False)
        summary.content_string = self.summary
        chapter = File("roadmap/README.md", ".", ".", False)
        chapter.content_string = "# Unchanged mathematics\n"
        files = Files([summary, chapter])
        self.assertIs(on_files(files, config=None), files)
        self.assertEqual(summary.content_string, normalize_summary(self.summary))
        self.assertEqual(chapter.content_string, "# Unchanged mathematics\n")


if __name__ == "__main__":
    unittest.main()
