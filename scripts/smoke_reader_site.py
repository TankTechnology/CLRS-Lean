#!/usr/bin/env python3
"""Exercise the book in Chromium against a local preview or public base URL.

Requires Playwright and Chromium. Set --browser to use a system installation.
"""
import argparse
from pathlib import Path
from playwright.sync_api import sync_playwright


def run(base: str, browser_path: str | None, screenshots: Path) -> None:
    base = base.rstrip('/') + '/'
    screenshots.mkdir(parents=True, exist_ok=True)
    with sync_playwright() as pw:
        options = {'headless': True}
        if browser_path:
            options['executable_path'] = browser_path
        browser = pw.chromium.launch(**options)
        context = browser.new_context(viewport={'width': 1440, 'height': 1000})
        errors = []
        context.on('page', lambda page: page.on('pageerror', lambda error: errors.append(str(error))))
        page = context.new_page()
        page.goto(base, wait_until='networkidle')
        assert 'CLRS-Lean' in page.title()
        assert not page.evaluate('performance.getEntriesByType("resource").some(r => /searchIndex\.js$/.test(r.name))')
        for n in range(1, 36):
            link = page.locator(f'.module-tree a[title="CLRSLean.FourthEdition.Chapter_{n:02d}"]')
            assert link.count() == 1 and link.is_visible(), n
        page.screenshot(path=str(screenshots / 'home-desktop.png'))
        for n in (3, 26, 33):
            url = base + f'CLRSLean/FourthEdition/Chapter_{n:02d}/'
            response = page.goto(url, wait_until='domcontentloaded')
            assert response.status == 200
            initial_headings = page.locator('main h1, main h2').all_text_contents()
            initial_open = page.locator('.module-tree details[open] > summary').all_text_contents()
            page.wait_for_load_state('networkidle')
            assert page.url == url
            assert initial_headings == page.locator('main h1, main h2').all_text_contents()
            assert initial_open == page.locator('.module-tree details[open] > summary').all_text_contents()
            assert page.locator('main h1').count() == 1
            page.screenshot(path=str(screenshots / f'chapter-{n}-top.png'))
            contents = page.locator('.clrs-chapter-contents a')
            assert contents.count() >= 3
            contents.nth(1).click()
            assert '#clrs-inline-' in page.url
            target = page.url.split('#', 1)[1]
            assert page.locator(f'[id="{target}"]').is_visible()
            assert page.evaluate('id => { const e = document.getElementById(id); const r = e.getBoundingClientRect(); return r.top >= -5 && r.top < innerHeight; }', target)
            page.screenshot(path=str(screenshots / f'chapter-{n}-section.png'))
        # Use the real search component and select a result with the keyboard.
        search = page.get_by_role('searchbox', name='Search', exact=True)
        results = page.get_by_role('listbox', name='Results')
        search.fill('variance decomposition')
        results.locator('.full-text').first.wait_for(state='visible', timeout=30000)
        assert page.evaluate('Boolean(window.searchIndex)')
        search.fill('pMergeSort_correct')
        results.locator('[role="option"]').first.wait_for(state='visible', timeout=30000)
        assert 'pMergeSort' in results.inner_text()
        search.press('ArrowDown')
        search.press('Enter')
        page.wait_for_load_state('networkidle')
        assert 'ParallelMergeSort' in page.url, page.url
        # Chapter link/anchor navigation on a touch-sized screen, plus dark mode.
        mobile = context.new_page()
        mobile.set_viewport_size({'width': 390, 'height': 844})
        url = base + 'CLRSLean/FourthEdition/Chapter_26/'
        mobile.goto(url, wait_until='networkidle')
        assert mobile.evaluate('document.documentElement.scrollWidth <= innerWidth + 1')
        mobile.locator('.hamburger').click()
        assert mobile.locator('.menu-toggle').is_checked()
        mobile.keyboard.press('Escape')
        assert not mobile.locator('.menu-toggle').is_checked()
        mobile.locator('.clrs-chapter-contents a').nth(2).click()
        assert '#clrs-inline-' in mobile.url
        mobile.screenshot(path=str(screenshots / 'chapter-26-mobile.png'))
        mobile.emulate_media(color_scheme='dark')
        mobile.evaluate('() => new Promise(resolve => requestAnimationFrame(() => requestAnimationFrame(resolve)))')
        mobile.screenshot(path=str(screenshots / 'chapter-26-dark.png'))
        # No script may be required to show chapters, section bodies or contents.
        offline = browser.new_context(java_script_enabled=False, viewport={'width': 390, 'height': 844})
        nojs = offline.new_page()
        nojs.goto(base + 'CLRSLean/FourthEdition/', wait_until='load')
        assert nojs.locator('main a[href*="/Chapter_"]').count() >= 35
        nojs.goto(url, wait_until='load')
        assert nojs.locator('.clrs-chapter-contents a').count() == 3
        assert nojs.locator('.clrs-inline-section').count() == 3
        nojs.locator('.hamburger').click()
        assert nojs.locator('.module-tree a[title="CLRSLean.FourthEdition.Chapter_35"]').is_visible()
        assert not errors, errors
        browser.close()
    print('Browser smoke OK: chapter index, stable layout, anchors, search, mobile menu, dark mode, no-JS reading')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base-url', required=True)
    parser.add_argument('--browser')
    parser.add_argument('--screenshots', type=Path, default=Path('/tmp/clrs-reader-smoke'))
    args = parser.parse_args()
    run(args.base_url, args.browser, args.screenshots)
