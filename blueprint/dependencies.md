---
kind: graph
autoform_generated: true
---

# Dependency summary

358 articles in 6 chapters, with 3 dependencies between chapters. A chapter depends on another when one of its articles rests on one of the other's; "proof only" marks a dependency only a proof needs.

| Status | Count | Meaning |
| --- | ---: | --- |
| in mathlib | 18 | Upstreamed into Mathlib. |
| fully proved | 300 | Proved, and every prerequisite is fully proved too. |
| ready to state | 11 | Everything its statement uses is in Lean, so the statement can be written in Lean. |
| not ready | 8 | Needs more blueprint work before it can be attempted. |
| planned | 21 | Described in the blueprint only. |

## Chapters

| Chapter | Items | Status | Ready | Depends on | Used by |
| --- | ---: | --- | ---: | --- | --- |
| [Appendix](roadmap/appendix/README.md) | 5 | 5 fully proved | 0 | none | Homology (proof only), The fundamental group (proof only) |
| [Cohomology](roadmap/cohomology/README.md) | 3 | 3 not ready | 0 | none | none |
| [The fundamental group](roadmap/fundamental-group/README.md) | 118 | 8 in mathlib · 110 fully proved | 0 | Appendix (proof only) | Homology |
| [Homology](roadmap/homology/README.md) | 228 | 10 in mathlib · 185 fully proved · 11 ready to state · 1 not ready · 21 planned | 11 | Appendix (proof only), The fundamental group | none |
| [Homotopy theory](roadmap/homotopy-theory/README.md) | 3 | 3 not ready | 0 | none | none |
| [Top level](roadmap/README.md) | 1 | 1 not ready | 0 | none | none |

The roadmap has more articles than the 120 this page lists; the explorer shows every one.

## Explorer

The published site draws the whole graph as an interactive explorer, on its home page and under Graph. To open it locally, render the site, build it, and serve it, where `<AUTOFORM_PLUGIN_ROOT>` is the Autoform plugin's root:

```bash
uv run --project "<AUTOFORM_PLUGIN_ROOT>" autoform render blueprint \
  --output site-src --lean-root .
uv run --with mkdocs --with mkdocs-material --with mkdocs-literate-nav \
  --with pymdown-extensions mkdocs build --strict
uv run --project "<AUTOFORM_PLUGIN_ROOT>" autoform dashboard . --site-dir site
```
