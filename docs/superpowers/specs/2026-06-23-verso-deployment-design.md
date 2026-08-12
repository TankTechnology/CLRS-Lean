# CLRS-Lean Verso Deployment Design

Date: 2026-06-23
Status: Approved
Reference: https://github.com/teorth/analysis

## Goals

Migrate the CLRS-Lean website from hand-written static HTML to the Verso literate programming engine,
delivering a book-like reading experience on par with `teorth/analysis`.

## Architecture

```
.lean source files (with /-! literate comments)
  → lakefile.lean (enables doc.verso, depends on the verso package)
    → literate.toml (module ordering, chapter titles)
      → lake build (compiles Lean)
        → lake build :literateHtml (Verso generates HTML)
          → _site/ (complete site)
            → GitHub Actions → GitHub Pages
```

## File structure

```
CLRSLean/
├── CLAUDE.md                  ← Agent authoring guide
├── CLRSLean.lean              ← top-level entry + Verso landing page
├── CLRSLean/
│   ├── Chapter_02/
│   │   └── Section_02_1_Insertion_Sort.lean
│   ├── Chapter_16/
│   │   └── Section_16_3_Huffman_Codes.lean
│   └── Chapter_23/
│       ├── Section_23_1_Growing_Minimum_Spanning_Trees.lean
│       └── Section_23_2_Kruskal_And_Prim.lean
├── lakefile.lean              ← changed from .toml to .lean DSL
├── literate.toml              ← Verso configuration
├── lean-toolchain             ← unchanged (v4.29.1)
├── docs/proof-map.md          ← manually maintained status ledger
└── .github/workflows/
    ├── lean_action_ci.yml     ← CI unchanged
    └── pages.yml              ← adds literate build step
```

## lakefile.lean

```lean
import Lake
open Lake DSL

package «clrs-lean» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`doc.verso, true⟩
  ]
  moreLeanArgs := #[
    "-Dwarn.sorry=false"
  ]

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"

require verso from git
  "https://github.com/leanprover/verso" @ "main"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.1"

@[default_target]
lean_lib «CLRSLean» where
```

## literate.toml

```toml
landing_page = "CLRSLean"

[order_children]
"CLRSLean" = [
  "CLRSLean.Chapter_02.Section_02_1_Insertion_Sort",
  "CLRSLean.Chapter_16.Section_16_3_Huffman_Codes",
  "CLRSLean.Chapter_23.Section_23_1_Growing_Minimum_Spanning_Trees",
  "CLRSLean.Chapter_23.Section_23_2_Kruskal_And_Prim",
]

[modules."CLRSLean.Chapter_02.Section_02_1_Insertion_Sort"]
title = "2.1. Insertion Sort"

[modules."CLRSLean.Chapter_16.Section_16_3_Huffman_Codes"]
title = "16.3. Huffman Codes"

[modules."CLRSLean.Chapter_23.Section_23_1_Growing_Minimum_Spanning_Trees"]
title = "23.1. Growing a Minimum Spanning Tree"

[modules."CLRSLean.Chapter_23.Section_23_2_Kruskal_And_Prim"]
title = "23.2. Kruskal and Prim"
```

## .lean file rewriting guidelines

See `CLAUDE.md`. Core requirements:

1. Every file must have a `/-! ... -/` module doc block at the top (page title + introduction + main results)
2. Every definition/theorem must be preceded by a `/-- ... -/` doc comment
3. Use `namespace CLRS` consistently
4. Unfinished proofs use a `sorry` explained in a comment

## CI/CD

### pages.yml (update)

Two jobs: `build` (builds the site) → `deploy` (deploys to Pages)

build steps: checkout → lean-action → lake build → doc-gen4 → lake build :literateHtml → collect into _site/ → upload artifact

deploy: deploy-pages, only on the main branch

### lean_action_ci.yml (unchanged)

Standard lean-action CI, only verifies compilation.

## Implementation steps

1. Replace lakefile.toml with lakefile.lean
2. Create literate.toml
3. Rewrite CLRSLean.lean (landing page)
4. Add a /-! module doc block to each .lean file
5. Update pages.yml
6. Verify locally that lake build passes
7. Verify locally that lake build :literateHtml generates correctly
8. Push, and observe CI + Pages deployment
