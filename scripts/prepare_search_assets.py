"""Adapt the pinned Verso search component for pasted input and lazy indexing."""
from pathlib import Path


def prepare_search_assets(site: Path) -> None:
    path = site / '-verso-search/search-box.js'
    if not path.is_file():
        return
    text = path.read_text()
    if '// CLRS input handling' in text:
        return
    needle = 'this.comboboxNode.addEventListener("keyup", this.onComboboxKeyUp.bind(this));'
    if text.count(needle) != 1:
        raise ValueError('Verso search input hook changed; review the pinned search adapter')
    if text.count('const searchIndex =') != 1 or text.count('const docContents =') != 1:
        raise ValueError('Verso search index binding changed; review the pinned search adapter')
    text = text.replace('const searchIndex =', 'let searchIndex =', 1)
    text = text.replace('const docContents =', 'let docContents =', 1)
    replacement = needle + '''
        // CLRS input handling: paste, touch keyboards and lazy full-text readiness.
        this.comboboxNode.addEventListener("input", this.onComboboxKeyUp.bind(this));
        this.comboboxNode.addEventListener("clrs-search-ready", () => {
            searchIndex = /** @type {any} */ (window).searchIndex;
            docContents = /** @type {any} */ (window).docContents;
            this.filter = null;
            this.onComboboxKeyUp(new KeyboardEvent("keyup"));
        });'''
    path.write_text(text.replace(needle, replacement))
