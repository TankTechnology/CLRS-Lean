# Chapter 34 Reader Structure Design

## Problem

The fourth-edition Chapter 34 reader page is structurally different from its
neighbors. `CLRSLean.FourthEdition.Chapter_34` imports only the legacy aggregate
`CLRSLean.Chapter_34`, so Verso has no fourth-edition section modules to place
under Chapter 34 in the primary sidebar. The page compensates with two very
long prose sections, which makes the guide difficult to scan and hides the
textbook's five-section organization.

## Approaches considered

1. **Fourth-edition section adapters (selected).** Add five small reader-facing
   modules under `CLRSLean/FourthEdition/Chapter_34/`. Each imports the existing
   proved section aggregate and explains its public theorem surface. Register
   those modules as children of the fourth-edition chapter.
2. **CSS-only collapsing.** Visually shorten the existing page with disclosure
   widgets. This would not fix the missing sidebar hierarchy or provide stable
   section URLs.
3. **Link directly to legacy section pages.** This would be cheaper, but it
   would move readers out of the canonical fourth-edition namespace and make
   Chapter 34 remain inconsistent with Chapters 33 and 35.

## Selected structure

The primary reader tree becomes:

```text
Chapter 34. NP-Completeness
├── 34.1. Polynomial Time
├── 34.2. Polynomial-Time Verification
├── 34.3. NP-Completeness and Reducibility
├── 34.4. NP-Completeness Proofs
└── 34.5. NP-Complete Problems
```

The adapters do not duplicate proofs. They import the existing section
aggregates, provide concise textbook-oriented summaries, list the main public
results, and link to the compatibility implementation pages when readers need
the deeper module tree.

The Chapter 34 landing page imports the five adapters and becomes a compact
chapter map. It contains:

- a short orientation paragraph;
- one link and one-sentence summary for each textbook section;
- the main reduction chain and Cook--Levin endpoint;
- a concise, scope-qualified completion statement.

## Navigation and presentation

`literate.toml` owns the hierarchy and titles. The section adapters are direct
children of `CLRSLean.FourthEdition.Chapter_34`, which lets the existing reader
sidebar renderer treat Chapter 34 exactly like Chapters 33 and 35. No
Chapter-34-only CSS or JavaScript is introduced.

Desktop acceptance criteria:

- Chapter 34 has an expandable sidebar node with five visible section links.
- The landing page opens with a chapter map instead of multi-screen status
  prose.
- The on-page table of contents contains the chapter map, main theorem chain,
  and coverage boundary.

Mobile acceptance criteria:

- The page has no horizontal overflow.
- The five section links remain readable in the content flow.
- Opening the sidebar exposes the same five section links.

## Verification

Tests enforce the five imported adapters, their order, configured titles, and
reader-facing links. Focused Lean builds compile the chapter guide and all five
adapters. A generated-site browser check compares Chapter 34 with Chapters 33
and 35, validates sidebar children and section links, and checks desktop and
390-pixel mobile layouts for overflow and console errors.

## Scope

This change reorganizes the reader surface only. Existing theorem statements,
proof implementations, compatibility URLs, proof-status counts, and public
completion claims remain unchanged.
