# Inline Chapter Reader Design

## Problem

Fourth-edition chapter pages currently act as migration guides. Their direct
section modules are available only through links, so readers must navigate to a
new page for every section. The generated sidebar also ships every disclosure
open and closes most of them after `DOMContentLoaded`, producing a visible
first-paint layout shift. Its fallback `scrollIntoView` can also move the main
document while trying to reveal the current sidebar row.

## Reader behavior

Each fourth-edition chapter page will retain its short chapter guide and then
render the complete contents of every direct section in configured order. The
same section pages and URLs remain available for deep links, search results,
and focused reading. On the combined chapter page, links to direct sections
become same-page anchors.

Only direct fourth-edition section children are embedded. Supporting modules
below a section remain separate implementation pages, which keeps chapter page
sizes bounded and preserves the existing navigation policy.

## Build implementation

Site preparation will optimize all generated pages first, then assemble each
chapter from the direct children listed in `literate.toml`. It will extract the
child `code-content` section, wrap it in a stable chapter-local anchor, and
append it to the chapter's content wrapper. The transformation is deterministic
and idempotent, and fails when an expected page or structural element is
missing.

Every ID inside embedded content is prefixed with its section anchor, and local
fragment links are rewritten to the prefixed target. This prevents identical
headings or declaration IDs in different sections from competing for the same
chapter-local anchor. Same-page links include the chapter route before the
fragment because Verso's relative `<base>` otherwise resolves a bare fragment
against the site root.

The largest projected combined chapter page is below 5 MiB in the current
build, well below the existing 25 MiB raw-page limit.

## First-paint stability

Generated navigation disclosures will be closed in static HTML, matching the
default script state. A small head bootstrap will hide the navigation tree
before first paint while saved disclosure state is applied, and the existing
state script will reveal it synchronously at the end of initialization. The
main content keeps its reserved layout width throughout. Initial sidebar
positioning adjusts only the sidebar scroll container and never calls
`scrollIntoView` on the current row.

## Verification

Unit tests will cover ordered section embedding, same-page links, preserved
standalone section pages, idempotence, static disclosure state, and the
first-paint bootstrap. Browser tests will compare pre- and post-load URLs,
measure layout shifts, and verify direct chapter content on desktop and mobile.
