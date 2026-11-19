---
kind: graph
autoform_generated: true
---

# Dependency summary

The roadmap has 395 articles: 350 formalization targets and 45 others (the roadmap's own article, chapters and sections, and articles that declare nothing). It has 6 chapters, with 3 dependencies between chapters. A chapter depends on another when one of its articles rests on one of the other's; "proof only" marks a dependency only a proof needs.

The Chapters table's Items column also counts 8 articles marked not ready with no declaration yet, so deferred work holds its chapter open; the status table, like `autoform check`, leaves such articles out.

| Status | Count | Meaning |
| --- | ---: | --- |
| in mathlib | 18 | Restates an existing Mathlib declaration. |
| fully proved | 307 | Proved, and every prerequisite is fully proved too. |
| ready to state | 6 | Everything its statement uses is in Lean, so the statement can be written in Lean. |
| planned | 19 | Described in the blueprint only. |

## Chapters

| Chapter | Items | Status | Ready | Depends on | Used by |
| --- | ---: | --- | ---: | --- | --- |
| [Appendix](roadmap/appendix/README.md) | 5 | 5 fully proved | 0 | none | Homology (proof only), The fundamental group (proof only) |
| [Cohomology](roadmap/cohomology/README.md) | 3 | 3 not ready | 0 | none | none |
| [The fundamental group](roadmap/fundamental-group/README.md) | 118 | 8 in mathlib · 110 fully proved | 0 | Appendix (proof only) | Homology |
| [Homology](roadmap/homology/README.md) | 228 | 10 in mathlib · 192 fully proved · 6 ready to state · 1 not ready · 19 planned | 6 | Appendix (proof only), The fundamental group | none |
| [Homotopy theory](roadmap/homotopy-theory/README.md) | 3 | 3 not ready | 0 | none | none |
| [Top level](roadmap/README.md) | 1 | 1 not ready | 0 | none | none |

The Items column totals 358; this page lists items only when there are at most 120, so it lists none, and the explorer shows every one.

## Explorer

The published site draws the whole graph as an interactive explorer, on its home page and under Graph. To open it locally, render the site, build it, and serve it, where `<AUTOFORM_PLUGIN_ROOT>` is the Autoform plugin's root:

```bash
uv run --project "<AUTOFORM_PLUGIN_ROOT>" autoform render blueprint \
  --output site-src --lean-root .
uv run --with mkdocs --with mkdocs-material --with mkdocs-literate-nav \
  --with pymdown-extensions mkdocs build --strict
uv run --project "<AUTOFORM_PLUGIN_ROOT>" autoform dashboard . --site-dir site
```
