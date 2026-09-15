#!/usr/bin/env python3
"""Visit every book chapter and section at desktop and mobile widths."""
import argparse
import asyncio
import json
from pathlib import Path
import sys

from playwright.async_api import async_playwright

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from scripts.literate_navigation import canonical_sections


async def run(base, executable, output):
    base = base.rstrip('/') + '/'
    modules = [f'CLRSLean.FourthEdition.Chapter_{n:02}' for n in range(1, 36)] + sorted(canonical_sections())
    output.mkdir(parents=True, exist_ok=True)
    records, failures = [], []
    async with async_playwright() as pw:
        browser = await pw.chromium.launch(headless=True, **({'executable_path': executable} if executable else {}))
        context = await browser.new_context(java_script_enabled=False)
        semaphore = asyncio.Semaphore(2)

        async def visit(module):
            async with semaphore:
                page = await context.new_page()
                row = {'module': module}
                try:
                    response = await page.goto(base + module.replace('.', '/') + '/', wait_until='load', timeout=60000)
                    assert response.status == 200, f'HTTP {response.status}'
                    assert await page.locator('main h1').count() == 1, 'expected one visible main heading'
                    if '.Section_' in module:
                        assert await page.locator('main .code-box span.const[id]').count(), 'no declarations'
                    for width in (1440, 390):
                        await page.set_viewport_size({'width': width, 'height': 1000 if width == 1440 else 844})
                        assert await page.locator('main h1').is_visible(), f'{width}: heading hidden'
                        assert await page.evaluate('document.documentElement.scrollWidth <= innerWidth + 1'), f'{width}: horizontal page overflow'
                        if '.Section_' in module:
                            first = page.locator('main .code-box span.const[id]').first
                            await first.scroll_into_view_if_needed()
                            assert await first.is_visible(), f'{width}: code hidden'
                    if '.Section_' not in module:
                        await page.evaluate('scrollTo(0, 0)')
                        await page.screenshot(path=str(output / (module.split('.')[-1] + '-mobile.png')))
                    row['status'] = 'passed'
                except Exception as exc:
                    row['status'], row['error'] = 'failed', str(exc)
                    failures.append(row)
                finally:
                    await page.close()
                    records.append(row)
                    print(f'{len(records)}/{len(modules)} {module}: {row["status"]}', flush=True)
        await asyncio.gather(*(visit(module) for module in modules))
        await browser.close()
    report = {'pages': len(modules), 'viewports': [1440, 390], 'javascript': False,
              'results': sorted(records, key=lambda row: row['module'])}
    (output / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'Whole-book browser check: {len(modules)} pages, {len(failures)} failures')
    return bool(failures)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base-url', required=True)
    parser.add_argument('--browser')
    parser.add_argument('--screenshots', type=Path, default=Path('/tmp/clrs-whole-book-browser'))
    args = parser.parse_args()
    sys.exit(asyncio.run(run(args.base_url, args.browser, args.screenshots)))
