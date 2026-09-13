#!/usr/bin/env python3
"""Capture book release stills and a short, unedited reading walkthrough.

Serve the assembled site before running. Requires Playwright, Chromium and ffmpeg.
"""
import argparse
from pathlib import Path
import subprocess
import tempfile

from playwright.sync_api import sync_playwright

ROOT = Path(__file__).resolve().parents[1]


def capture(base: str, output: Path, browser_path: str | None) -> None:
    base = base.rstrip('/') + '/'
    output.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='clrs-book-video-') as tmp, sync_playwright() as pw:
        options = {'headless': True}
        if browser_path:
            options['executable_path'] = browser_path
        browser = pw.chromium.launch(**options)
        card = browser.new_page(viewport={'width': 1200, 'height': 630})
        card.goto((ROOT / 'docs/releases/assets/share-card.html').as_uri(), wait_until='networkidle')
        card.screenshot(path=str(ROOT / 'docs/literate/assets/book-social.png'))
        card.close()
        context = browser.new_context(viewport={'width': 1680, 'height': 1000},
                                      record_video_dir=tmp, record_video_size={'width': 1680, 'height': 1000})
        page = context.new_page()
        page.goto(base, wait_until='networkidle')
        page.screenshot(path=str(output / 'book-cover-desktop.png'))
        page.wait_for_timeout(2200)
        page.get_by_role('link', name='Open the book').click()
        page.wait_for_load_state('networkidle')
        page.screenshot(path=str(output / 'book-contents.png'))
        page.wait_for_timeout(1800)
        page.goto(base + 'CLRSLean/FourthEdition/Chapter_02/', wait_until='networkidle')
        page.wait_for_timeout(1800)
        theorem = page.locator('[id$="___insertionSort_sorted"]').first
        theorem.scroll_into_view_if_needed()
        page.screenshot(path=str(output / 'book-proof.png'))
        page.wait_for_timeout(3000)
        page.goto(base + 'CLRSLean/FourthEdition/Chapter_33/', wait_until='networkidle')
        page.screenshot(path=str(output / 'book-chapter-33.png'))
        page.wait_for_timeout(2200)
        page.goto(base + 'CLRSLean/FourthEdition/Chapter_35/', wait_until='networkidle')
        page.locator('.clrs-book-colophon').scroll_into_view_if_needed()
        page.wait_for_function('document.querySelector(".clrs-book-colophon img").naturalWidth > 0')
        page.screenshot(path=str(output / 'book-closing.png'))
        page.wait_for_timeout(2500)
        video = page.video
        context.close()
        assert video is not None
        video.save_as(str(Path(tmp) / 'walkthrough.webm'))

        mobile = browser.new_page(viewport={'width': 390, 'height': 844})
        mobile.goto(base, wait_until='networkidle')
        assert mobile.evaluate('document.documentElement.scrollWidth <= innerWidth + 1')
        mobile.screenshot(path=str(output / 'book-cover-mobile.png'))
        mobile.emulate_media(color_scheme='dark')
        mobile.screenshot(path=str(output / 'book-cover-dark.png'))
        browser.close()
        subprocess.run(['ffmpeg', '-y', '-loglevel', 'error', '-i', str(Path(tmp) / 'walkthrough.webm'),
                        '-c:v', 'libx264', '-crf', '25', '-pix_fmt', 'yuv420p', '-movflags', '+faststart',
                        str(output / 'book-walkthrough.mp4')], check=True)
    print(f'Release stills and walkthrough saved to {output}')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base-url', required=True)
    parser.add_argument('--output', type=Path, default=ROOT / 'docs/releases/assets')
    parser.add_argument('--browser')
    args = parser.parse_args()
    capture(args.base_url, args.output, args.browser)
