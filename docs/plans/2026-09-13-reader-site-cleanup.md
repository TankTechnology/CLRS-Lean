# Reader site cleanup

## Accepted direction

Keep the existing static Verso book and fourth-edition routes. The reader sees
all 35 chapter names, canonical section names, a chapter contents list, the
section bodies, and then detailed scope and implementation notes. No JavaScript
is required to reveal content or establish the navigation layout.

## Repairs

1. Use configured chapter children as the sidebar allowlist, including on old
   compatibility URLs. Preserve internal proof URLs and discoverability.
2. Generate the active chapter's open state in HTML; remove delayed navigation
   hiding and disclosure restoration. Keep browser-native links and disclosures.
3. Compose chapter introductions, same-page contents, correctly nested section
   headings, section bodies and scope notes in reading order. Rebuild the page
   table of contents from those sections.
4. Separate shared reader interactions from HTML optimization. Correct mobile
   spacing, focus treatment, dark surfaces and long-content anchor behavior.
5. Verify every chapter and canonical section against rendered HTML, check
   same-page targets and links, and exercise real browser reading/search/menu
   flows with JavaScript enabled and disabled. Run the same checks in Pages.

## Validation and release

Use the existing built Lean/Verso artifacts because these changes affect site
assembly, not theorem definitions. Reassemble the entire site, run repository
and rendering checks, and inspect desktop/mobile screenshots. Commit in English
as TankTechnology, merge to main, and dispatch Pages. Distinguish dispatch from
successful deployment and public verification in the handoff.
