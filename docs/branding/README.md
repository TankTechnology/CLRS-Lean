# CLRS-Lean visual identity

The September 14, 2026 project artwork is an open book unfolding into algorithm
trees, sorting bars, graphs and a proof tree. The accompanying square icon uses
an ivory book and a gold binary tree on an ink-blue background. These are project
illustrations, not formal proof diagrams or coverage claims.

## Sources and published assets

- `clrs-lean-project.png`: original approved cover, 1536 × 1024.
- `clrs-lean-project-prompt.txt`: cover prompt and generation method.
- `clrs-lean-icon-source.png`: companion icon generated with the built-in image
  generator, using the approved cover as a reference.
- `clrs-lean-icon-prompt.txt`: exact companion icon prompt and reference.
- `../literate/assets/clrs-lean-cover.webp`: web cover, also used by the README.
- `../literate/assets/clrs-lean-social.jpg`: uncropped 1200 × 800 share image.
- `../literate/assets/clrs-lean-icon.png`: 192 × 192 navigation and browser icon.
- `../literate/assets/apple-touch-icon.png`: 180 × 180 touch icon.
- `../literate/assets/favicon.ico`: 16, 32 and 48 pixel browser icons.

Use the complete cover at its original aspect ratio. Use the square icon for
small identity placements. Keep image text out of crops. The original SVG art
and September 13 social card remain available as historical release assets.

## Exporting

The artwork is generated; ImageMagick only resizes and encodes the web files.
From the repository root:

```sh
convert docs/branding/clrs-lean-project.png -quality 86 docs/literate/assets/clrs-lean-cover.webp
convert docs/branding/clrs-lean-project.png -resize 1200x800 -quality 88 docs/literate/assets/clrs-lean-social.jpg
convert docs/branding/clrs-lean-icon-source.png -resize 192x192 docs/literate/assets/clrs-lean-icon.png
convert docs/branding/clrs-lean-icon-source.png -resize 180x180 docs/literate/assets/apple-touch-icon.png
convert docs/branding/clrs-lean-icon-source.png -define icon:auto-resize=48,32,16 docs/literate/assets/favicon.ico
```

`scripts/prepare_literate_site.py` copies these assets and installs the cover,
icon links and social metadata on the generated website. See
[site architecture](../site-architecture.md) for preview and publication.
